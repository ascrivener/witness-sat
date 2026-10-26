#!/usr/bin/env bash
# Measures the LRAT check's gas, batch by batch, for a CNF and its LRAT refutation.
#
#   WITNESS_DIR=path/to/witness scripts/gas.sh IN.cnf PROOF.lrat OUT_DIR [GAS_BUDGET...]
#
# Plans the proof once per budget (sat-report plan --gas, default 3×10⁷ and 2×10⁹) into
# OUT_DIR/plan-BUDGET, runs `witness-sim check` on each batch's arguments, and appends a line a
# batch to OUT_DIR/gas.tsv: plan.tsv's columns (what the gas model counts), then the gas measured.
# tools/fit_gas.py fits the model in tools/sat-report/src/plan.rs to it.
#
# witness-sim runs the check in PolkaVM's recompiler and charges PolkaJam v0.1.29's gas. Checks
# get 10¹² gas, so a batch past refine's 5×10⁹ still shows what it would cost.
set -euo pipefail
: "${WITNESS_DIR:?set WITNESS_DIR to a witness checkout}"
WITNESS_DIR=$(cd "$WITNESS_DIR" && pwd)
CNF=$(realpath "${1:?usage: gas.sh IN.cnf PROOF.lrat OUT_DIR [GAS_BUDGET...]}")
PROOF=$(realpath "${2:?}")
OUT=${3:?}
shift 3
cd "$(dirname "$0")/.."
SIM=$WITNESS_DIR/target/release/witness-sim
SR=target/release/sat-report

nice -n 15 cargo build -q --release -p sat-report
nice -n 15 cargo jam-build --out-dir out -p sat-check >/dev/null 2>&1
(cd "$WITNESS_DIR" && nice -n 15 cargo build -q --release -p witness-sim)
mkdir -p "$OUT"
TSV=$OUT/gas.tsv
for budget in ${@:-30000000 2000000000}; do
	plan=$OUT/plan-$budget
	"$SR" plan "$CNF" "$PROOF" "$plan" --gas "$budget" >&2
	[ -s "$TSV" ] || printf 'input\tbudget\t%s\tgas\n' "$(head -1 "$plan/plan.tsv")" >"$TSV"
	tail -n +2 "$plan/plan.tsv" | while IFS= read -r row; do
		b=${row%%$'\t'*}
		"$SR" args "$plan" "$b" "$plan/$b.args"
		gas=$("$SIM" check out/sat-check.jam "$plan/$b.args" 1000000000000 | sed -nE 's/^Ok\(\(\)\): used ([0-9]+) gas.*/\1/p')
		[ -n "$gas" ] || { echo "batch $b of $plan failed in witness-sim" >&2; exit 1; }
		printf '%s\t%s\t%s\t%s\n' "$(basename "$CNF")" "$budget" "$row" "$gas" >>"$TSV"
	done
done
column -t "$TSV" | tail -n 20
