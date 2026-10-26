#!/usr/bin/env bash
# An UNSAT bounty paid for a refutation attested in chunks, in witness-sim: the Erdős discrepancy
# proof, or any CNF and LRAT proof.
#
#   WITNESS_DIR=path/to/witness scripts/erdos-sim.sh IN.cnf PROOF WORK
#
# PROOF is an LRAT file, or a directory `sat-report split` and `trim` made. WORK keeps the plan
# (WORK/plan), witness-sim's chain (WORK/sim) and a log of the stages' wall times (WORK/times), so
# a run stopped part way resumes: attest-batches.py picks up from what's attested.
#
# carol attests the formula's anchor and posts the bounty citing it; dave commits, attests every
# chunk (attest-batches.py, a round at a time, as many chunks a round as the DAG allows and a
# package fits), reveals trusting the attested empty clause, and is paid after the claim window.
# Each chunk gets the full spec's 5×10⁹ refine gas.
set -euo pipefail
: "${WITNESS_DIR:?set WITNESS_DIR to a witness checkout}"
WITNESS_DIR=$(cd "$WITNESS_DIR" && pwd)
CNF=$(realpath "${1:?usage: erdos-sim.sh IN.cnf PROOF WORK}")
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
export WITNESS_SIM_DIR=$WORK/sim
mkdir -p "$WITNESS_SIM_DIR"

step() { printf '\n== %s\n' "$*"; }
fail() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }
# Record how long the stage starting now takes.
STARTED=$(date +%s)
mark() { local now; now=$(date +%s); printf '%s\t%s s\n' "$1" $((now - STARTED)) | tee -a "$WORK/times"; STARTED=$now; }
slot() { "$SIM" inspect slot; }
wait_slot() { while [ "$(slot)" -lt "$1" ]; do :; done; }
item() {
	[ -n "$1" ] || fail "no payload"
	printf '%s' "$1" >"$OP"
	"$SIM" item "$SVC" "@$OP" $(ls "$X"/* 2>/dev/null) >/dev/null
	rm -rf "$X"
}
storage() {
	local v; v=$("$SIM" inspect storage --raw "$SVC" "$($W key "$@")" 2>/dev/null || true)
	case $v in 0x*) echo "$v" ;; *) echo "" ;; esac
}
bounty() { local v; v=$(storage --bounty 0); [ -n "$v" ] && $W decode --bounty "$v" || echo none; }
balance() { local v; v=$(storage --balance "$1" --asset test); [ -n "$v" ] && $W decode --balance "$v" || echo 0; }
nonce() { local v; v=$(storage --account "$1"); [ -n "$v" ] && $W decode --account "$v" | sed -nE 's/.*nonce: ([0-9]+).*/\1/p' || echo 0; }
expect() { # DESCRIPTION PATTERN COMMAND...
	local what=$1 pattern=$2; shift 2
	local out; out=$("$@")
	grep -qE "$pattern" <<<"$out" && echo "ok: $what" || fail "$what: wanted /$pattern/, got: $out"
}

step "building"
(cd "$WITNESS_DIR" && cargo build -q --release -p witness-cli -p witness-sim &&
	cargo jam-build --out-dir out -p witness-service >/dev/null)
cargo build -q --release -p sat-report
cargo jam-build --out-dir out -p sat-check >/dev/null 2>&1
mark build

if [ ! -s "$U/empty" ]; then
	step "planning"
	"$SR" plan "$CNF" "$PROOF" "$U"
	mark plan
fi
PARAMS=$(cat "$U/params")
CHUNKS=$(($(ls "$U" | grep -c '\.witness$') - 1))

if [ ! -s "$WORK/service" ]; then
	step "deploying witness"
	"$SIM" create-service "$WITNESS_DIR/out/witness-service.jam" 10000000000 --min-memo-gas 300000 >/dev/null
	SVC=$((16#$("$SIM" list | tail -1 | cut -f1)))
	item "$($W propose --service "$SVC" --nonce 0 --fee-asset test --commit-deposit 10 --attest-deposit 10)"
	item "$($W mint --to carol --amount 1000000)"
	item "$($W mint --to dave --amount 1000000)"
	echo "$SVC" >"$WORK/service"
fi
SVC=$(cat "$WORK/service")
echo "service $SVC"

if [ "$(bounty)" = none ]; then
	step "carol attests the formula's anchor, and posts the bounty citing it"
	item "$($W attest --service "$SVC" --attester carol --nonce "$(nonce carol)" --check "$SAT" --params "$PARAMS" \
		--subjects "$U/$(cat "$U/batch-0.subjects")" --witness-file "$U/batch-0.witness" --check-gas 100000000 \
		--claim-out "$U/batch-0.claim" --extrinsics "$X")"
	expect "the anchor is attested" '^0x' storage --attestation "$U/batch-0.claim"
	item "$($W create --service "$SVC" --maker carol --nonce "$(nonce carol)" --check "$SAT" --params "$PARAMS" \
		--blobs "$U/batch-0.claim:0" --reward 100000 --check-gas $GAS --expiry $(( $(slot) + 100000 )))"
	expect "the bounty is open" 'status: Open' bounty
	# dave commits before attesting a chunk: attested chunks are public.
	item "$($W commit --service "$SVC" --bounty 0 --hunter dave --nonce "$(nonce dave)" --salt 0x0d --witness-str dave 2>/dev/null)"
	expect "dave committed" '^999990$' balance dave
	mark "anchor, bounty, commitment"
fi

step "dave attests $CHUNKS chunks"
(cd "$U" && python3 "$WITNESS_DIR/scripts/attest-batches.py" "$U" --witness "$W" --service "$SVC" --check "$SAT" \
	--params "$PARAMS" --check-gas $GAS --attesters dave --sim "$SIM")
mark "attesting $CHUNKS chunks"

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

grep -h 'check used' "$WITNESS_SIM_DIR/log" | grep -oE 'check used [0-9]+' | awk '{s += $3; if ($3 > m) m = $3} END {printf "checks: %d, %.3e gas in all, %.3e at most\n", NR, s, m}'
printf '\nthe UNSAT bounty is paid (%s chunks)\n' "$CHUNKS"
