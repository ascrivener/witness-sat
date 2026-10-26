# Design: SAT certificates on witness

Status: both checks, the planner and the demo built and measured; the demo passes in witness-sim
and on a local PolkaJam v0.1.29 testnet with the full spec's refine gas (493 s). The Erdős
discrepancy proof is regenerated, attested end to end through witness in witness-sim, and its
bounty paid; a slice of it on a testnet is next. See [The Erdős discrepancy
proof](#the-erdős-discrepancy-proof).

## Summary

A SAT certificate is cheap to check relative to finding it, which is what a witness bounty pays
for. A satisfying assignment or a Ramsey graph fits in one check. A refutation doesn't: famous
ones run to gigabytes. So witness-sat checks LRAT refutations in **chunks**, each one
attestation, each trusting clauses that earlier chunks derived, until one attests the empty
clause, and a bounty pays out on that.

| Check | Witness | Gas (measured in witness-sim) |
|---|---|---|
| Ramsey, R(5,5) > 42 | a 42-vertex graph, 108 bytes | 6.0×10⁵ |
| SAT, 400 variables, 1,700 clauses | an assignment, 50 bytes | 2.5×10⁶ |
| SAT, 10,000 variables, 42,500 clauses | an assignment, 1.25 KB | 7.2×10⁷ |
| LRAT chunk | ~24k gas a step on pigeonhole proofs, ~90k on the Erdős proof | up to 5×10⁹ a chunk |
| The Erdős discrepancy proof, C = 2 | 5.6M steps in 164 chunks | 5.0×10¹¹ in all |
| UNSAT reveal, trusting the attested empty clause | anything | 1.1×10³ |

## The checks

**ramsey-check** takes params `n s t` and the upper triangle of an adjacency matrix. It looks
for an `s`-clique in the graph and a `t`-clique in its complement over 64-bit vertex sets,
extending a clique only by vertices adjacent to all of it and abandoning a branch with too few
left. On the (5,5,42)-graph in the tests it visits a few thousand partial cliques, not the
C(42,5) = 850,668 five-sets. All 328 graphs in McKay's `r55_42some.g6` pass at about 6×10⁵ gas;
of the 861 single-edge flips of the first, 855 make a K5 or an independent 5-set and are
refused, and 6 give other (5,5,42)-graphs.

**sat-check, SAT** (params `[0]`): the bounty's one plain blob is the formula, and the witness
an assignment, a bit a variable. Every clause must have a true literal.

**sat-check, UNSAT** (params `[1] ++ vars ++ clauses ++ root`): the params fix the formula by the
Merkle root of its clauses, in witness's own tree format (`witness_types::merkle`), so the root
is what an attestation of the clauses, in order, would have.

### Encoding

A literal is a *code*, `2(v − 1)` for `v` and `2(v − 1) + 1` for `¬v`, so `code ^ 1` negates. A
clause is its length, then its codes, increasing: the first as it is, each after as its
distance from the one before, all LEB128. A clause has one encoding (the decoder refuses a zero
distance and LEB128 with trailing zero bytes), so one hash; the empty clause is the byte `0`.

### Chunks

An attestation's subjects are *bundles* of clauses (a count, then the clauses' encodings), and
an attestation of this check, with params `F`, says: *`F` implies every clause of each
subject*. A chunk, the attest witness, numbers three kinds of clause in one space:

1. **trusted:** the clauses of earlier attestations' subjects (the op's trusted blobs), implied
   by `F`;
2. **original:** clauses of `F`, with one Merkle multiproof against the params' root;
3. **steps:** clauses the chunk derives, each by RUP over hints naming earlier clauses, as
   distances back.

Each subject must be the bundle of some of them, in order (the chunk's *exports* say which).

**Why bundles.** Citing a subject costs an op a reference and a Merkle path (about 300 bytes)
and refine some hashing, and witness caps an op's blobs at 4,096. A chunk of the Erdős proof
cites hundreds of thousands of earlier clauses: one clause a subject capped its chunks at about
250 steps and 1% of a refine's gas (20,391 chunks). Bundled, a chunk cites at most 1,419 subjects
from 160 attestations, and chunks are cut by gas. The check accepts only if
every step's RUP check succeeds: assume the step's clause false, then each hint must be unit
(its one open literal becomes true) or falsified (the conflict, after which the step holds). A
satisfied hint, or one with two open literals, fails the step.

**Soundness.** By induction on attestations: the trusted clauses are implied by `F` (witness
passes only subjects of this check's own attestations with the same params, and attestations by
this check accept only implied clauses); originals are in `F`, by the multiproof; and a clause
derived by RUP from implied clauses is implied. So every subject is implied by `F`, and an
attested empty clause means `F` is unsatisfiable. Nothing else in the LRAT proof matters to
soundness: its clause ids, its deletions, and which steps a chunk holds are planning.

**The anchor.** witness lets a reveal trust attested subjects only if its bounty cites one, so
that the bounty, not the hunter, fixes the attest params. A bounty for `F` must exist before
its proof (hunters commit before they attest), so it cites an *anchor*: an attestation of `F`'s
first clause, a chunk with no steps that just proves the clause is in the tree. Anyone can make
it from `F` alone.

**Reveal.** The bounty is paid if a trusted bundle holds the empty clause; the witness is then
anything (the hunter's tag). Or the witness is itself a chunk deriving the empty clause, so a
proof small enough for one check needs no attestations at all.

### What the check doesn't do

- **RAT steps** (LRAT's negative hints): checking one needs every clause containing the pivot's
  negation, which no chunk has. CaDiCaL's LRAT has none.
- **The bounty's params and its anchor must agree.** The reveal sees trusted blobs, not the
  params they were attested under, so a bounty whose params name one formula while citing
  another's anchor pays for a refutation of the anchor's formula. `sat-report plan` writes both;
  a maker checks their own bounty.

### Front-running

Attestations are public, and an UNSAT reveal accepts any witness once the empty clause is
attested. witness pays the earliest commitment that reveals, so a hunter who commits before
attesting their first chunk wins against anyone who sees the chunks and commits later. But
anyone can commit *speculatively*, before the hunter, at no cost but the commit deposit, then
reveal once the hunter's empty clause is attested, and be first. The same holds for witness-lean
whenever a reveal adds little to attested work.

Fixing it needs witness: say, a bounty option that pays only a hunter who attested the cited
empty clause themselves. Attestation records already store the attester, and accumulate can
check `record.attester == hunter` for one named claim. Until then, UNSAT bounties suit cases
where the poster is the one paying for the verification, which is the headline's case.

## Planning

`sat-report plan` turns a CNF and an LRAT proof into chunks, in the layout witness's
`scripts/attest-batches.py` reads (`batch-N.subjects`, `.trust`, `.witness`, `.gas`):

1. **Trim.** Only steps the first empty clause depends on are kept: going backwards from it, a
   step is needed if a needed step cites it. A big proof is first `split` into zstd-compressed
   segments of binary LRAT, and `trim` reads them newest first, one in memory at a time, into a
   bitset over clause ids. Needed clauses are then numbered densely, so planning's per-clause
   arrays stay small.
2. **Cut.** Pass 1 takes steps in order into a chunk until it would pass any of the budget's
   limits, and records, for each clause a later chunk cites, the first chunk to cite it.
3. **Bundle.** Chunk `j`'s clauses first cited by chunk `k` make one subject, the bundle
   `(j, k)`. So chunk `k` trusts exactly the clauses it needs from `j`, and a later chunk citing
   any of them trusts the whole bundle (paying for clauses it doesn't use). The empty clause is a
   bundle of its own, so a reveal trusts two bytes.
4. **Write.** Pass 2 writes each chunk: hints renumbered, the formula's clauses it uses with
   their multiproof, the trusted bundles in order of first use, and its bundles as subjects.
   Every chunk is checked natively as it's written.

The budget's limits, each from witness or PolkaJam:

| Limit | Default | Why |
|---|---|---|
| estimated check gas | 3×10⁹ | refine has 5×10⁹; measured gas is at most 1.26× the model |
| witness bytes | 8 MiB | |
| witness and trusted bytes together | 11 MB | a work package carries about 13.8 MB, with the subjects, citations and check; pass 1 underestimates bytes by about 10% |
| trusted bundles | 3,000 | `MAX_BLOBS`, 4,096, with the subjects |
| trusted bytes | 8 MiB | `MAX_BLOBS_LEN`, 16 MiB, with the subjects |
| attestations cited | 1,200 | refine's output lists them, 32 bytes each, in 48 KiB |

Batch 0 is the anchor; trimming guarantees every other batch exports something (its last step
is cited later, or is the empty clause).

## Gas

PolkaJam v0.1.29 charges PolkaVM's full cost model with L2-cache hits: a basic block costs the
cycles a pipeline simulation gives it, a load 25 cycles of latency, and **a conditional branch
20, unless one side is a trap**, which costs 1 (PolkaVM's `get_branch_cost`). So:

- RUP is counted branch-free. Clauses are stored padded to groups of four literals with a
  sentinel that is always false, and a hint's group is counted with comparisons, not branches.
  RV64E's 16 registers make the compiler spill some of that loop to the stack.
- Checks fail by trapping (`sat_check::fail`), which the service counts as false, so validation
  on hot paths is a branch to a trap: 1 gas. Off PolkaVM it's a panic, which tests catch.

Those two changes took the 6,891-step PHP(8,7) chunk from 1.43×10⁸ gas to 1.20×10⁸; the
LEB128 reader rewrite alone changed nothing.

**The model** (`tools/sat-report/src/plan.rs`), fitted by nonnegative least squares
(`tools/fit_gas.py`) to 703 chunks measured in witness-sim (`scripts/gas.sh`): pigeonhole (8 and
10 pigeons) and random 3-SAT proofs at budgets from 2×10⁷ to 2×10⁹
([data/small-proofs-gas.tsv](data/small-proofs-gas.tsv)), and the Erdős proof's 159 chunks at
3×10⁹:

| Per | Gas |
|---|---|
| hint | 99 |
| literal visited (hinted clauses' and the step's own) | 82 |
| byte of chunk witness | 155 |
| hash proving the formula's clauses | 6,900 |
| byte of trusted bundles | 236 |

Measured gas was at most 1.26 times the model (it overestimates small pigeonhole chunks, up to
5×, which only makes them smaller). On the Erdős proof's final plan, measured gas was within −2%
and +10% of it. A trusted byte costs about as much as a witness byte: the check parses each
trusted clause into its padded arena, though few are ever hinted.

What dominates depends on the proof. A pigeonhole step visits about 70 literals over 15 hints.
An Erdős step has 64 hints and visits 323 literals; its hints are three-byte distances, as a chunk
numbers a few hundred thousand clauses; and a chunk trusts about 3 MB of bundles, a quarter of
its gas.

## The Erdős discrepancy proof

Every ±1 sequence of length 1161 has discrepancy greater than 2 (Konev and Lisitsa, SAT 2014
and AIJ 2015).

- **The formula** is Konev and Lisitsa's own: `edp-sinz_d2_l1161.cnf`, from their generator
  with sequential-counter (Sinz) constraints. It has 11,847 variables and 41,971 clauses (the
  AIJ paper reports 41,970). Their server now refuses every file (HTTP 403, in a browser too), so
  it came from the Internet Archive's August 2014 copy.
- **No proof is hosted anywhere.** The 2014 DRUP proof was about 13 GB; for the AIJ encoding,
  Glucose wrote 1.67 GB of DRUP in about 800 s, which drup-trim checked in about 5.5 h. So the
  proof is regenerated here with CaDiCaL 3.0.1's LRAT.

**The proof.** CaDiCaL 3.0.1 (`--lrat`, binary) proves it in 570 s on one core of the fanless
8-core MacBook Air this was built on, with 225 MB of memory, writing 1.53 GB of LRAT zstd-compressed (about 3 GB raw,
10.5M steps). Trimming keeps 5,595,996 steps (53%).

**The plan** (`sat-report split`, `trim`, `plan`: 12 s, 7 s and 57 s):

| | |
|---|---|
| chunks | 164, plus the anchor |
| steps a chunk | median 33,742, at most 50,468 |
| gas a chunk, measured in witness-sim | median 3.15×10⁹, at most 3.37×10⁹ |
| gas in all | 5.02×10¹¹ |

Per chunk: [data/edp2-1161-gas.tsv](data/edp2-1161-gas.tsv) (the plan's counts, and the gas measured).
| witness and trusted bytes a chunk | median 11.1 MB, at most 12.2 MB |
| witness in all | 1.23 GB |
| bundles trusted a chunk | median 727, at most 1,419 |
| attestations cited a chunk | median 82, at most 160 |
| subjects a chunk | median 22, at most 105 |

**End to end in witness-sim** (`scripts/erdos.sh`): carol attests the formula's anchor and
posts a bounty citing it, dave commits, attests every chunk through witness's service with
`attest-batches.py`, reveals trusting the attested empty clause, and is paid.

| Stage | Wall time |
|---|---|
| plan (from the trimmed segments) | 60 s |
| anchor, bounty, commitment | 1 s |
| attesting 164 chunks, in 163 rounds | 685 s |
| reveal and payout | under 1 s |
| in all | 747 s |

witness-sim ran 166 checks, 5.02×10¹¹ gas in all and at most 3.37×10⁹, at about 0.73×10⁹ gas a
second of one core, using at most 580 MB of memory. The reveal costs 1.1×10³ gas.

**No parallelism.** The chunks form a chain 164 deep: every chunk cites the one before it, as
CDCL proofs build each learned clause on recent ones. So attesting is 164 rounds of one refine
each, and it's why the run above took 11 minutes on one core of an 8-core laptop; on a testnet with the full spec's
5×10⁹ refine gas, a round takes a few slots, so about 164 × 3 × 6 s ≈ 50 minutes.

### Go or no-go

**Go**, for witness-sim and a full-gas testnet:

- Each chunk fits one refine with a third of its gas to spare and a work package with about
  1.6 MB to spare. It needs no change to witness.
- 5×10¹¹ gas is 100 refines' worth: about 9 minutes of one core, or 100 cores' worth of one
  6-second slot, though the chain makes it 164 slots at least.
- On PolkaJam's dev chain (10⁹ refine gas), chunks would be about 5× smaller and the chain about
  800 rounds: it would work, slowly. The full-gas wrapper is the testnet to use.

What it would take in production, and what's open:

- **Latency is the chain.** Cutting it needs chunks that don't wait for their predecessors:
  attest each chunk *conditionally*, as "these imports imply these exports", all at once, then
  link them with cheap ops that discharge the imports in order (many chunks a link op, since a
  link only hashes). Or cube-and-conquer proofs, whose cubes are independent.
- **Bytes.** 1.23 GB of witness, plus the trusted bundles, travel as work packages. JAM keeps
  them available for audit, not in state; state holds 165 attestation records.
- **The model's reach.** It's fitted on three kinds of proof; a proof with much longer clauses,
  or many more distinct citations, may need a refit (`scripts/gas.sh`, `tools/fit_gas.py`).

The Keller dimension-7 fallback isn't needed: the Erdős proof fits.
