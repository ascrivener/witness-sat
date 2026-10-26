#!/usr/bin/env bash
# witness-sat's bounties, start to finish:
#
#   WITNESS_DIR=path/to/witness scripts/demo.sh            # in witness-sim
#   WITNESS_DIR=path/to/witness POLKAJAM_DIR=path/to/polkajam-v0.1.29 scripts/demo.sh --testnet
#
# WITNESS_DIR is a checkout of witness (at the commit Cargo.toml pins), for the service, its CLI,
# witness-sim and its submit scripts. --testnet starts a local PolkaJam testnet (v0.1.29), unless
# JAM_RPC names a running one, and runs every op on it.
#
# Four bounties, each by the maker, carol:
#
#   0  Ramsey, R(5,5) > 42: a graph on 42 vertices with no K5 and no independent 5-set
#      (ramsey-check, params `42 5 5`). Exoo found the first in 1989; alice reveals one of
#      McKay and Radziszowski's. mallory's copy has one edge flipped, and is refused.
#   1  Ramsey, R(5,5) > 43: the same for 43 vertices. Open: claiming it would prove R(5,5) ≥ 44.
#   2  SAT: a satisfying assignment of a random 3-SAT formula (the bounty's blob, sat-check), which
#      bob found.
#   3  UNSAT: a refutation of UNSAT_CNF (default: 7 pigeons in 6 holes). Its LRAT proof (UNSAT_LRAT)
#      is cut into chunks (sat-report plan), and the bounty cites the formula's anchor
#      attestation, so its reveals may trust attested clauses. It binds claims (--bind-claim):
#      a reveal's witness names the attestation it adds. dave computes his chunks' attestation
#      ids from his plan, commits to the last one's, then attests the chunks (witness's
#      attest-batches.py), and reveals trusting the attested empty clause. mallory, who
#      committed early to a witness of her own, can't claim it with dave's attestation.
#
# Every bounty's claim window passes and the hunters are paid; bounty 1 stays open.
set -euo pipefail
: "${WITNESS_DIR:?set WITNESS_DIR to a witness checkout}"
WITNESS_DIR=$(cd "$WITNESS_DIR" && pwd)
TESTNET=
case "${1:-}" in
	--testnet) TESTNET=1 ;;
	"") ;;
	*) echo "usage: $0 [--testnet]" >&2; exit 2 ;;
esac
cd "$(dirname "$0")/.."
ROOT=$(pwd)
# PolkaVM's recompiler makes its sandbox with userfaultfd: without it, every check is BadCheckBlob.
if [ "$(cat /proc/sys/vm/unprivileged_userfaultfd 2>/dev/null || echo 1)" = 0 ]; then
	echo 'vm.unprivileged_userfaultfd is 0: run `sysctl -w vm.unprivileged_userfaultfd=1` first' >&2
	exit 1
fi

W=$WITNESS_DIR/target/release/witness
SIM=$WITNESS_DIR/target/release/witness-sim
SERVICE=$WITNESS_DIR/out/witness-service.jam
SR=$ROOT/target/release/sat-report
TMP=$(mktemp -d)
X=$TMP/extrinsics
OP=$TMP/op
RAMSEY=$ROOT/out/ramsey-check.jam
SAT=$ROOT/out/sat-check.jam
UNSAT_CNF=${UNSAT_CNF:-$ROOT/tools/sat-report/testdata/php6.cnf}
UNSAT_LRAT=${UNSAT_LRAT:-$ROOT/tools/sat-report/testdata/php6.lrat}
# The estimated check gas a chunk may use: small, so the pigeonhole proof makes a few chunks.
CHUNK_GAS=${CHUNK_GAS:-10000000}
# Check gas: what a Ramsey or SAT check needs with room to spare, and refine's whole budget for
# a chunk (the testnet's dev chain has 10⁹; see witness-lean for the full spec's).
GAS=100000000
CHUNK_CHECK_GAS=${CHUNK_CHECK_GAS:-$([ -n "$TESTNET" ] && echo 900000000 || echo 5000000000)}

step() { printf '\n== %s\n' "$*"; }
fail() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }

# The chain, witness-sim or a testnet, gives `slot`, `submit SERVICE PAYLOAD [EXTRINSIC...]`,
# `raw_storage SERVICE KEY`, and POLL, the seconds between looks at it.
if [ -n "$TESTNET" ]; then
	JAMT=${POLKAJAM_DIR:+$POLKAJAM_DIR/}jamt
	POLL=2
	CHAIN=()
	slot() { "$JAMT" inspect slot; }
	submit() { python3 "$WITNESS_DIR/scripts/jam-submit.py" "$@"; }
	# jamt cuts values over 1 KiB short.
	raw_storage() { python3 "$WITNESS_DIR/scripts/jam-storage.py" "$1" "$2" 2>/dev/null || true; }
else
	export WITNESS_SIM_DIR=$TMP/sim
	POLL=0
	CHAIN=(--sim "$SIM")
	# witness-sim passes a slot with every item and every `inspect slot`.
	slot() { "$SIM" inspect slot; }
	submit() { "$SIM" item "$@"; }
	raw_storage() { "$SIM" inspect storage --raw "$1" "$2" 2>/dev/null || true; }
fi
wait_slot() { while [ "$(slot)" -lt "$1" ]; do sleep $POLL; done; }
# Submit PAYLOAD with the extrinsics the CLI last wrote, if any; one item per slot (a testnet
# silently drops some packages submitted together in one slot).
item() {
	[ -n "$1" ] || fail "no payload"
	printf '%s' "$1" >"$OP"
	submit "$SVC" "@$OP" $(ls "$X"/* 2>/dev/null) >/dev/null
	rm -rf "$X"
	wait_slot $(( $(slot) + 1 ))
}

storage() {
	local v; v=$(raw_storage "$SVC" "$($W key "$@")")
	case $v in 0x*) echo "$v" ;; *) echo "" ;; esac
}
bounty() { local v; v=$(storage --bounty "$1"); [ -n "$v" ] && $W decode --bounty "$v" || echo none; }
balance() { local v; v=$(storage --balance "$1" --asset test); [ -n "$v" ] && $W decode --balance "$v" || echo 0; }
account() { local v; v=$(storage --account "$1"); [ -n "$v" ] && $W decode --account "$v" || echo none; }
# Wait until COMMAND prints something matching PATTERN.
expect() { # DESCRIPTION PATTERN COMMAND...
	local what=$1 pattern=$2; shift 2
	local out=
	for _ in $(seq 1 60); do
		out=$("$@")
		if grep -qE "$pattern" <<<"$out"; then echo "ok: $what"; return; fi
		sleep $POLL
	done
	fail "$what: wanted /$pattern/, got: $out"
}
# Something that must not happen: give it time to (wrongly) happen, then check.
expect_still() { sleep $((POLL * 9)); expect "$@"; }
# Why witness-sim refused the last op (a testnet doesn't say).
why() { if [ -z "$TESTNET" ]; then grep -E 'Rejected|not applied' "$WITNESS_SIM_DIR/log" | tail -1 | sed -E 's/.*INFO witness +/   witness-sim: /' || true; fi; }

# Account nonces, so the script can send each account's signed ops in turn.
declare -A NONCE=()
# Set N to WHO's next nonce, and count it as used (in this shell: not in a $(...) subshell).
take() { N=${NONCE[$1]:-0}; NONCE[$1]=$((N + 1)); }

step "building"
(cd "$WITNESS_DIR" && cargo build -q --release -p witness-cli -p witness-sim &&
	cargo jam-build --out-dir out -p witness-service >/dev/null)
cargo build -q --release -p sat-report
cargo jam-build --out-dir out -p sat-check -p ramsey-check >/dev/null
echo "checks: ramsey-check $(wc -c <"$RAMSEY") bytes, sat-check $(wc -c <"$SAT") bytes"

step "preparing the witnesses"
"$SR" ramsey ramsey/testdata/r55_42.g6 0 "$TMP/r55.graph" >/dev/null
# mallory's copy: edge (0, 2) flipped, which makes a K5 or an independent 5-set. (Flipping
# (0, 1) wouldn't: it's one of 6 edges whose flip gives another (5,5,42)-graph.)
python3 -c "import sys; b = bytearray(open(sys.argv[1], 'rb').read()); b[0] ^= 2; open(sys.argv[2], 'wb').write(b)" \
	"$TMP/r55.graph" "$TMP/r55-flipped.graph"
"$SR" planted 400 1700 7 "$TMP/planted.cnf" "$TMP/planted.assignment"
"$SR" formula "$TMP/planted.cnf" "$TMP/planted.formula"
U=$TMP/unsat
"$SR" plan "$UNSAT_CNF" "$UNSAT_LRAT" "$U" --gas "$CHUNK_GAS"
UNSAT_PARAMS=$(cat "$U/params")

if [ -n "$TESTNET" ] && [ -z "${JAM_RPC:-}" ]; then
	step "starting a testnet (log: $TMP/testnet.log)"
	"${POLKAJAM_DIR:+$POLKAJAM_DIR/}polkajam-testnet" >"$TMP/testnet.log" 2>&1 &
	TESTNET_PID=$!
	trap 'pkill -P $TESTNET_PID 2>/dev/null; kill $TESTNET_PID 2>/dev/null || true' EXIT
	for _ in $(seq 1 60); do "$JAMT" list >/dev/null 2>&1 && break; sleep 2; done
fi

step "deploying witness"
if [ -n "$TESTNET" ]; then
	before=$("$JAMT" list | wc -l)
	# witness_types::DEPOSIT_GAS: what witness needs to credit a deposit.
	"$JAMT" create-service "$SERVICE" 10000000000 --min-memo-gas 300000 >/dev/null
	for _ in $(seq 1 40); do [ "$("$JAMT" list | wc -l)" -gt "$before" ] && break; sleep $POLL; done
	SVC=$((16#$("$JAMT" list | tail -1 | cut -f1)))
	# Packages anchored before the service existed can't see its code.
	for _ in $(seq 1 40); do "$JAMT" inspect final service "$SVC" >/dev/null 2>&1 && break; sleep $POLL; done
else
	"$SIM" create-service "$SERVICE" 10000000000 --min-memo-gas 300000 >/dev/null
	SVC=$((16#$("$SIM" list | tail -1 | cut -f1)))
fi
echo "service $SVC"
# On a testnet the first package can be anchored before guarantors see the new code (refine:
# BadCode), so send the configuration until it's there.
config() { local v; v=$(storage --config); [ -n "$v" ] && $W decode --config "$v" || echo none; }
for _ in 1 2 3 4 5; do
	item "$($W propose --service "$SVC" --nonce 0 --fee-asset test --commit-deposit 10 --attest-deposit 10)"
	for _ in 1 2 3 4 5 6; do [ "$(config)" != none ] && break 2; sleep $POLL; done
	echo "   the configuration didn't land; sending it again"
done
expect "witness is configured" 'commit_deposit: 10' config
item "$($W mint --to carol --amount 100000)"
for who in alice bob dave mallory; do item "$($W mint --to $who --amount 100)"; done
expect "carol has 100000" '^100000$' balance carol
for who in alice bob dave mallory; do expect "$who has 100" '^100$' balance $who; done

EXPIRY=$(( $(slot) + 2000 ))
step "carol posts the Ramsey bounties: R(5,5) > 42 and R(5,5) > 43"
take carol
item "$($W create --service "$SVC" --maker carol --nonce $N --check "$RAMSEY" --params 0x2a0505 \
	--reward 1000 --check-gas $GAS --expiry $EXPIRY)"
take carol
item "$($W create --service "$SVC" --maker carol --nonce $N --check "$RAMSEY" --params 0x2b0505 \
	--reward 50000 --check-gas $GAS --expiry $EXPIRY)"
expect "bounty 0 (R(5,5) > 42) open" 'status: Open' bounty 0
expect "bounty 1 (R(5,5) > 43) open" 'status: Open' bounty 1

step "carol posts the SAT bounty: an assignment of a 400-variable formula, its blob"
take carol
item "$($W create --service "$SVC" --maker carol --nonce $N --check "$SAT" --params 0x00 \
	--blobs "$TMP/planted.formula" --reward 2000 --check-gas $GAS --expiry $EXPIRY)"
expect "bounty 2 open" 'status: Open' bounty 2

step "carol attests the formula's anchor, and posts the UNSAT bounty citing it"
# The anchor proves one clause is in the formula: anyone can attest it before any proof exists.
take carol
item "$($W attest --service "$SVC" --attester carol --nonce $N --check "$SAT" --params "$UNSAT_PARAMS" \
	--subjects "$U/$(cat "$U/batch-0.subjects")" --witness-file "$U/batch-0.witness" --check-gas $GAS \
	--claim-out "$U/batch-0.claim" --extrinsics "$X")"
expect "the anchor is attested" '^0x' storage --attestation "$U/batch-0.claim"
take carol
item "$($W create --service "$SVC" --maker carol --nonce $N --check "$SAT" --params "$UNSAT_PARAMS" \
	--blobs "$U/batch-0.claim:0" --reward 5000 --check-gas $CHUNK_CHECK_GAS --expiry $EXPIRY --bind-claim)"
expect "bounty 3 open" 'status: Open' bounty 3
expect "carol escrowed the rewards" "^$((100000 - 1000 - 50000 - 2000 - 5000 - 10))\$" balance carol

step "hunters commit"
commit() { # HUNTER BOUNTY SALT WITNESS-ARGS...
	local who=$1 b=$2 salt=$3; shift 3
	take "$who"
	item "$($W commit --service "$SVC" --bounty "$b" --hunter "$who" --nonce $N --salt "$salt" "$@" 2>/dev/null)"
}
commit alice 0 0x0a --witness-file "$TMP/r55.graph"
commit mallory 0 0x0e --witness-file "$TMP/r55-flipped.graph"
commit bob 2 0x0b --witness-file "$TMP/planted.assignment"
# mallory commits to bounty 3 before anyone has proven anything, hoping to reveal trusting
# whoever's empty clause gets attested.
commit mallory 3 0x0e --witness-str mallory
# dave's attestations' ids follow from his plan, so he computes them before attesting any (`witness
# attest` only builds the op), and commits to the id of the one holding the empty clause. An
# attested chunk is public, and nobody could know that id before committing.
(cd "$U" && for b in $(seq 1 $(($(ls | grep -c '\.witness$') - 1))); do
	trust=$(cat "batch-$b.trust")
	$W attest --service "$SVC" --attester dave --nonce 0 --check "$SAT" --params "$UNSAT_PARAMS" \
		--subjects "$(cat "batch-$b.subjects")" ${trust:+--trust "$trust"} --witness-file "batch-$b.witness" \
		--check-gas "$CHUNK_CHECK_GAS" --claim-out "batch-$b.claim" --extrinsics "$TMP/dry" >/dev/null 2>&1
	rm -rf "$TMP/dry"
done)
EMPTY=$(cat "$U/empty")
DAVE_W=$($W claim-id --claim "$U/${EMPTY%:*}")
commit dave 3 0x0d --witness "$DAVE_W"
for who in alice bob dave; do expect "$who committed, deposit taken" '^90$' balance $who; done
expect "mallory committed twice" '^80$' balance mallory

step "dave attests his refutation: $(($(ls "$U" | grep -c '\.witness$') - 1)) chunks"
# attest-batches.py signs with the attesters' nonces from the chain; dave's next is 1.
cd "$U"
python3 "$WITNESS_DIR/scripts/attest-batches.py" "$U" --witness "$W" --service "$SVC" --check "$SAT" \
	--params "$UNSAT_PARAMS" --check-gas "$CHUNK_CHECK_GAS" --attesters dave "${CHAIN[@]}"
cd "$ROOT"
NONCE[dave]=$(account dave | sed -nE 's/.*nonce: ([0-9]+).*/\1/p')

step "hunters reveal"
wait_slot $(( $(slot) + 2 ))
reveal() { # BOUNTY CHECK PARAMS HUNTER SALT ARGS...
	local b=$1 check=$2 params=$3 who=$4 salt=$5; shift 5
	item "$($W reveal --bounty "$b" --check "$check" --params "$params" --check-gas "${REVEAL_GAS:-$GAS}" --hunter "$who" \
		--salt "$salt" "$@" --extrinsics "$X")"
}
reveal 0 "$RAMSEY" 0x2a0505 mallory 0x0e --witness-file "$TMP/r55-flipped.graph"
expect_still "mallory's graph, one edge off, is refused" 'status: Open' bounty 0
why
reveal 0 "$RAMSEY" 0x2a0505 alice 0x0a --witness-file "$TMP/r55.graph"
expect "alice's graph shows R(5,5) > 42" 'Revealing' bounty 0
reveal 2 "$SAT" 0x00 bob 0x0b --blobs "$TMP/planted.formula" --witness-file "$TMP/planted.assignment"
expect "bob's assignment satisfies the formula" 'Revealing' bounty 2
REVEAL_GAS=$CHUNK_CHECK_GAS reveal 3 "$SAT" "$UNSAT_PARAMS" dave 0x0d --blobs "$U/batch-0.claim:0" \
	--trust "$U/$EMPTY" --witness "$DAVE_W"
expect "dave's attested empty clause refutes the formula" 'Revealing' bounty 3
REVEAL_GAS=$CHUNK_CHECK_GAS reveal 3 "$SAT" "$UNSAT_PARAMS" mallory 0x0e --blobs "$U/batch-0.claim:0" \
	--trust "$U/$EMPTY" --witness-str mallory
# Refused in accumulate: had it counted, her commitment, the earlier, would win (see the payouts).
sleep $((POLL * 9))
why

step "waiting out the claim windows, then finalizing"
for b in 0 2 3; do
	wait_slot "$(bounty $b | sed -nE 's/.*window_end: ([0-9]+).*/\1/p')"
	item "$($W finalize --bounty $b)"
	expect "bounty $b claimed" 'Claimed' bounty $b
done
expect "alice is paid" "^$((100 + 1000))\$" balance alice
expect "bob is paid" "^$((100 + 2000))\$" balance bob
# Less an attest deposit for each chunk: attestations are kept for good, so it isn't refunded.
CHUNKS=$(($(ls "$U" | grep -c '\.witness$') - 1))
expect "dave is paid, less $CHUNKS attest deposits" "^$((100 + 5000 - 10 * CHUNKS))\$" balance dave
expect "mallory lost both commit deposits" '^80$' balance mallory
expect "bounty 1, R(5,5) > 43, is still open" 'status: Open' bounty 1

printf '\nthe witness-sat demo passed\n'
