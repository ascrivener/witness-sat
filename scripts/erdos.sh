#!/usr/bin/env bash
# An UNSAT bounty paid for a refutation attested in chunks: the Erdős discrepancy proof, or any
# CNF and LRAT proof.
#
#   WITNESS_DIR=path/to/witness scripts/erdos.sh IN.cnf PROOF WORK              # witness-sim
#   WITNESS_DIR=... POLKAJAM_DIR=path/to/polkajam-full-gas SLICE=10 \
#     scripts/erdos.sh --testnet IN.cnf PROOF WORK                              # a testnet
#
# PROOF is an LRAT file, or a directory `sat-report split` and `trim` made. WORK keeps the plan
# (WORK/plan, made with GAS_BUDGET, default sat-report's), the chain's state (witness-sim's in
# WORK/sim; a testnet's service id in WORK/service) and the stages' wall times (WORK/times), so
# a run stopped part way resumes: attest-batches.py picks up from what's attested.
#
# carol attests the formula's anchor and posts the bounty citing it; dave commits, attests the
# chunks (attest-batches.py, a round at a time, as many chunks a round as the DAG allows and a
# package fits), reveals trusting the attested empty clause, and is paid after the claim window.
# With SLICE=K he attests only the first K chunks, and the bounty stays open.
#
# --testnet starts a local PolkaJam testnet (v0.1.29) from POLKAJAM_DIR, unless JAM_RPC names a
# running one. Chunks need the full spec's refine gas: polkajam-full-gas wraps PolkaJam with it.
# A laptop testnet's validators share its cores, so plan chunks smaller there (GAS_BUDGET=10⁹)
# and let PACKAGE_GAS and SETTLE_SLOTS pace the rounds (attest-batches.py --package-gas,
# --settle); run nothing heavy alongside.
set -euo pipefail
: "${WITNESS_DIR:?set WITNESS_DIR to a witness checkout}"
WITNESS_DIR=$(cd "$WITNESS_DIR" && pwd)
TESTNET=
[ "${1:-}" = --testnet ] && { TESTNET=1; shift; }
CNF=$(realpath "${1:?usage: erdos.sh [--testnet] IN.cnf PROOF WORK}")
PROOF=$(realpath "${2:?}")
mkdir -p "${3:?}"
WORK=$(cd "$3" && pwd)
cd "$(dirname "$0")/.."
ROOT=$(pwd)

W=$WITNESS_DIR/target/release/witness
SIM=$WITNESS_DIR/target/release/witness-sim
SR=$ROOT/target/release/sat-report
SAT=$ROOT/out/sat-check.jam
U=$WORK/plan
X=$WORK/extrinsics
OP=$WORK/op
GAS=5000000000

step() { printf '\n== %s\n' "$*"; }
fail() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }
# Record how long the stage starting now takes.
STARTED=$(date +%s)
mark() { local now; now=$(date +%s); printf '%s\t%s s\n' "$1" $((now - STARTED)) | tee -a "$WORK/times"; STARTED=$now; }

# The chain, witness-sim or a testnet, gives `slot`, `submit SERVICE PAYLOAD [EXTRINSIC...]`,
# `raw_storage SERVICE KEY`, and POLL, the seconds between looks at it.
if [ -n "$TESTNET" ]; then
	JAMT=${POLKAJAM_DIR:+$POLKAJAM_DIR/}jamt
	POLL=2
	CHAIN=(${PACKAGE_GAS:+--package-gas "$PACKAGE_GAS"} ${SETTLE_SLOTS:+--settle "$SETTLE_SLOTS"})
	slot() { "$JAMT" inspect slot; }
	submit() { python3 "$WITNESS_DIR/scripts/jam-submit.py" "$@"; }
	# jamt cuts values over 1 KiB short.
	raw_storage() { python3 "$WITNESS_DIR/scripts/jam-storage.py" "$1" "$2" 2>/dev/null || true; }
else
	export WITNESS_SIM_DIR=$WORK/sim
	mkdir -p "$WITNESS_SIM_DIR"
	POLL=0
	CHAIN=(--sim "$SIM")
	# witness-sim passes a slot with every item and every `inspect slot`.
	slot() { "$SIM" inspect slot; }
	submit() { "$SIM" item "$@"; }
	raw_storage() { "$SIM" inspect storage --raw "$1" "$2" 2>/dev/null || true; }
fi
wait_slot() { while [ "$(slot)" -lt "$1" ]; do sleep $POLL; done; }
storage() {
	local v; v=$(raw_storage "$SVC" "$($W key "$@")")
	case $v in 0x*) echo "$v" ;; *) echo "" ;; esac
}
bounty() { local v; v=$(storage --bounty 0); [ -n "$v" ] && $W decode --bounty "$v" || echo none; }
balance() { local v; v=$(storage --balance "$1" --asset test); [ -n "$v" ] && $W decode --balance "$v" || echo 0; }
nonce() { local v; v=$(storage --account "$1"); [ -n "$v" ] && $W decode --account "$v" | sed -nE 's/.*nonce: ([0-9]+).*/\1/p' || echo 0; }
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
# Submit PAYLOAD with the extrinsics the CLI last wrote, if any, and wait a slot.
item() {
	[ -n "$1" ] || fail "no payload"
	printf '%s' "$1" >"$OP"
	submit "$SVC" "@$OP" $(ls "$X"/* 2>/dev/null) >/dev/null
	rm -rf "$X"
	wait_slot $(( $(slot) + 1 ))
}
# Submit WHO's signed op PAYLOAD (made with their nonce N) until it's applied, which bumps the
# nonce: a testnet sometimes drops a package, and a late copy is refused for its stale nonce.
signed() { # WHO N PAYLOAD
	local who=$1 n=$2
	[ -n "$3" ] || fail "no payload"
	local extrinsics=($(ls "$X"/* 2>/dev/null))
	printf '%s' "$3" >"$OP"
	for _ in 1 2 3; do
		submit "$SVC" "@$OP" "${extrinsics[@]}" >/dev/null
		for _ in $(seq 1 30); do
			[ "$(nonce "$who")" -gt "$n" ] && { rm -rf "$X"; return; }
			sleep $POLL
		done
		echo "   $who's op $n wasn't applied; sending it again"
	done
	fail "$who's op $n never applied"
}

step "building"
(cd "$WITNESS_DIR" && cargo build -q --release -p witness-cli -p witness-sim &&
	cargo jam-build --out-dir out -p witness-service >/dev/null)
cargo build -q --release -p sat-report
cargo jam-build --out-dir out -p sat-check >/dev/null 2>&1
mark build

if [ ! -s "$U/empty" ]; then
	step "planning"
	"$SR" plan "$CNF" "$PROOF" "$U" ${GAS_BUDGET:+--gas "$GAS_BUDGET"}
	mark plan
fi
PARAMS=$(cat "$U/params")
CHUNKS=$(($(ls "$U" | grep -c '\.witness$') - 1))
SLICE=${SLICE:-$CHUNKS}
[ "$SLICE" -le "$CHUNKS" ] || SLICE=$CHUNKS
# attest-batches.py attests the batches WORK numbers from 0: a slice is a directory of the first
# SLICE + 1 (the anchor and SLICE chunks), linked.
A=$U
if [ "$SLICE" -lt "$CHUNKS" ]; then
	A=$WORK/slice-$SLICE
	mkdir -p "$A"
	ln -sfn "$U/subjects" "$A/subjects"
	# Claims too, though they don't exist yet: attest-batches.py writes them through the links,
	# so they land with the plan, where a later, longer run finds them.
	for b in $(seq 0 "$SLICE"); do
		for kind in subjects trust witness gas claim; do ln -sf "$U/batch-$b.$kind" "$A/batch-$b.$kind"; done
	done
fi

if [ -n "$TESTNET" ] && [ -z "${JAM_RPC:-}" ] && [ ! -s "$WORK/service" ]; then
	step "starting a testnet (log: $WORK/testnet.log)"
	"${POLKAJAM_DIR:+$POLKAJAM_DIR/}polkajam-testnet" >"$WORK/testnet.log" 2>&1 &
	TESTNET_PID=$!
	trap 'pkill -P $TESTNET_PID 2>/dev/null; kill $TESTNET_PID 2>/dev/null || true' EXIT
	for _ in $(seq 1 60); do "$JAMT" list >/dev/null 2>&1 && break; sleep 2; done
fi

if [ ! -s "$WORK/service" ]; then
	step "deploying witness"
	if [ -n "$TESTNET" ]; then
		before=$("$JAMT" list | wc -l)
		# witness_types::DEPOSIT_GAS: what witness needs to credit a deposit.
		"$JAMT" create-service "$WITNESS_DIR/out/witness-service.jam" 10000000000 --min-memo-gas 300000 >/dev/null
		for _ in $(seq 1 40); do [ "$("$JAMT" list | wc -l)" -gt "$before" ] && break; sleep $POLL; done
		SVC=$((16#$("$JAMT" list | tail -1 | cut -f1)))
		# Packages anchored before the service existed can't see its code.
		for _ in $(seq 1 40); do "$JAMT" inspect final service "$SVC" >/dev/null 2>&1 && break; sleep $POLL; done
	else
		"$SIM" create-service "$WITNESS_DIR/out/witness-service.jam" 10000000000 --min-memo-gas 300000 >/dev/null
		SVC=$((16#$("$SIM" list | tail -1 | cut -f1)))
	fi
	# On a testnet the first package can be anchored before guarantors see the new code (refine:
	# BadCode), so send the configuration until it's there.
	config() { local v; v=$(storage --config); [ -n "$v" ] && $W decode --config "$v" || echo none; }
	for _ in 1 2 3 4 5; do
		item "$($W propose --service "$SVC" --nonce 0 --fee-asset test --commit-deposit 10 --attest-deposit 10)"
		for _ in 1 2 3 4 5 6; do [ "$(config)" != none ] && break 2; sleep $POLL; done
		echo "   the configuration didn't land; sending it again"
	done
	expect "witness is configured" 'commit_deposit: 10' config
	item "$($W mint --to carol --amount 1000000)"
	item "$($W mint --to dave --amount 1000000)"
	expect "carol has the test asset" '^1000000$' balance carol
	expect "dave has the test asset" '^1000000$' balance dave
	echo "$SVC" >"$WORK/service"
	mark "deploying witness"
fi
SVC=$(cat "$WORK/service")
echo "service $SVC"

if [ "$(bounty)" = none ]; then
	step "carol attests the formula's anchor, and posts the bounty citing it"
	if [ -z "$(storage --attestation "$U/batch-0.claim" 2>/dev/null)" ]; then
		n=$(nonce carol)
		signed carol "$n" "$($W attest --service "$SVC" --attester carol --nonce "$n" --check "$SAT" --params "$PARAMS" \
			--subjects "$U/$(cat "$U/batch-0.subjects")" --witness-file "$U/batch-0.witness" --check-gas 100000000 \
			--claim-out "$U/batch-0.claim" --extrinsics "$X")"
	fi
	expect "the anchor is attested" '^0x' storage --attestation "$U/batch-0.claim"
	n=$(nonce carol)
	signed carol "$n" "$($W create --service "$SVC" --maker carol --nonce "$n" --check "$SAT" --params "$PARAMS" \
		--blobs "$U/batch-0.claim:0" --reward 100000 --check-gas $GAS --expiry $(( $(slot) + 100000 )))"
	expect "the bounty is open" 'status: Open' bounty
	# dave commits before attesting a chunk: attested chunks are public.
	n=$(nonce dave)
	signed dave "$n" "$($W commit --service "$SVC" --bounty 0 --hunter dave --nonce "$n" --salt 0x0d --witness-str dave 2>/dev/null)"
	expect "dave committed" '^999990$' balance dave
	mark "anchor, bounty, commitment"
fi

step "dave attests $SLICE of the $CHUNKS chunks"
(cd "$A" && python3 "$WITNESS_DIR/scripts/attest-batches.py" "$A" --witness "$W" --service "$SVC" --check "$SAT" \
	--params "$PARAMS" --check-gas $GAS --attesters dave "${CHAIN[@]}")
mark "attesting $SLICE chunks"

if [ "$SLICE" -lt "$CHUNKS" ]; then
	expect "the bounty is still open: the empty clause isn't attested yet" 'status: Open' bounty
	printf '\n%s of %s chunks attested\n' "$SLICE" "$CHUNKS"
	exit 0
fi

step "dave reveals, trusting the attested empty clause"
if ! grep -q 'Revealing\|Claimed' <<<"$(bounty)"; then
	item "$($W reveal --bounty 0 --check "$SAT" --params "$PARAMS" --blobs "$U/batch-0.claim:0" --trust "$U/$(cat "$U/empty")" \
		--check-gas $GAS --hunter dave --salt 0x0d --witness-str dave --extrinsics "$X")"
fi
expect "the empty clause refutes the formula" 'Revealing|Claimed' bounty
if ! grep -q Claimed <<<"$(bounty)"; then
	wait_slot "$(bounty | sed -nE 's/.*window_end: ([0-9]+).*/\1/p')"
	item "$($W finalize --bounty 0)"
fi
expect "the bounty is claimed" 'Claimed' bounty
expect "dave is paid, less $CHUNKS attest deposits" "^$((1000000 + 100000 - 10 * CHUNKS))\$" balance dave
mark "reveal and payout"

if [ -z "$TESTNET" ]; then
	grep -h 'check used' "$WITNESS_SIM_DIR/log" | grep -oE 'check used [0-9]+' |
		awk '{s += $3; if ($3 > m) m = $3} END {printf "checks: %d, %.3e gas in all, %.3e at most\n", NR, s, m}'
fi
printf '\nthe UNSAT bounty is paid (%s chunks)\n' "$CHUNKS"
