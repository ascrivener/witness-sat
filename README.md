# witness-sat

[witness](https://github.com/ascrivener/witness) checks for SAT certificates, and bounties on
them, checked on JAM:

- **ramsey-check** (`ramsey/`): a graph on `n` vertices with no clique of size `s` and no
  independent set of size `t`, which proves R(s, t) > n. A bounty at `42 5 5` pays for one of
  the known (5,5,42)-graphs (Exoo 1989; McKay and Radziszowski found 656); one at `43 5 5` would
  prove R(5,5) ≥ 44, which is open (43 ≤ R(5,5) ≤ 46).
- **sat-check** (`check/`): a satisfying assignment of a formula (the bounty's blob), or an
  **LRAT refutation**, attested in chunks: each chunk is checked by reverse unit propagation,
  trusting the clauses earlier chunks derived, and a bounty is paid once the empty clause is
  attested. So a proof far bigger than one refine (the Erdős discrepancy proof for C = 2 is the
  target) is checked by many refines, in parallel where the proof allows.

How the LRAT check works, its soundness, and the measured gas: [docs/design.md](docs/design.md).

## Layout

```
check/                sat-check: SAT assignments, and LRAT chunks (enc.rs, lrat.rs, tree.rs)
ramsey/               ramsey-check, with a (5,5,42)-graph in ramsey/testdata
tools/sat-report/     host tool: CNF and LRAT in; chunk plans, attest inputs and check args out
tools/fit_gas.py      fits the planner's gas model to measurements
scripts/demo.sh       the bounties end to end, in witness-sim or on a PolkaJam testnet
scripts/gas.sh        measures each chunk's gas in witness-sim
```

`witness-check` and `witness-types` come from witness by git, pinned in `Cargo.toml`. witness is
private for now, so CI needs a `WITNESS_READ_TOKEN` secret that can read it.

## Build and test

```bash
cargo test                        # the checks, and the planner on a pigeonhole proof
cargo jam-build --out-dir out     # out/sat-check.jam, out/ramsey-check.jam
```

## The LRAT pipeline

```bash
cadical --lrat formula.cnf proof.lrat                   # binary LRAT (CaDiCaL ≥ 1.7)
sat-report split proof.lrat segs                        # a big proof: compressed segments
sat-report trim formula.cnf segs                        # keep what the empty clause needs
sat-report plan formula.cnf segs work                   # chunks, as attest-batches.py reads them
```

A small proof can go straight to `plan` (it trims in memory). `work/params` is the UNSAT
bounty's params, `work/batch-0` the formula's anchor (the bounty cites it), and `work/empty` the
attested empty clause a reveal trusts. witness's `scripts/attest-batches.py` attests the batches,
several at once where they don't depend on each other.

## Demo

```bash
WITNESS_DIR=../witness scripts/demo.sh             # witness-sim, under a minute
WITNESS_DIR=../witness POLKAJAM_DIR=... scripts/demo.sh --testnet
```

Carol posts four bounties: R(5,5) > 42, which alice claims with a known graph (mallory's copy,
one edge off, is refused); R(5,5) > 43, which stays open; a random 3-SAT formula, which bob
satisfies; and the unsatisfiability of 7 pigeons in 6 holes, which dave proves with CaDiCaL's
LRAT proof, attested in 7 chunks.
