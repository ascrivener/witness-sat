# Design: SAT certificates on witness

Status: milestone 1 built and measured in witness-sim: both checks, the planner, and the
demo. The Erdős discrepancy re-check (milestone 3) is in progress; see [The Erdős discrepancy
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
| LRAT chunk | ~24k gas a step on pigeonhole and random 3-SAT proofs | up to 5×10⁹ a chunk |
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

An attestation's subjects are clauses, and an attestation of this check, with params `F`,
says: *`F` implies each subject*. A chunk, the attest witness, numbers three kinds of clause in
one space:

1. **trusted:** subjects of earlier attestations (the op's trusted blobs), implied by `F`;
2. **original:** clauses of `F`, with one Merkle multiproof against the params' root;
3. **steps:** clauses the chunk derives, each by RUP over hints naming earlier clauses, as
   distances back.

Each subject must equal one of them (the chunk's *exports* say which). The check accepts only if
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

**Reveal.** The bounty is paid if a trusted blob is the empty clause; the witness is then
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
2. **Cut.** Pass 1 takes steps in order into a chunk until its estimated gas, witness bytes or
   trusted clauses would pass the budget. It marks each clause a later chunk cites.
3. **Write.** Pass 2 writes each chunk: hints renumbered, the formula's clauses it uses with
   their multiproof, the trusted clauses (earlier chunks' exports) in order of first use, and as
   subjects every step a later chunk cites, plus the empty clause. A chunk whose trusted clauses
   and subjects would pass witness's 4,096 blobs is split in two, recursively (the first half
   then also exports what the second cites). Every chunk is checked natively as it's written.

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

**The model** (`tools/sat-report/src/plan.rs`), fitted by least squares (`tools/fit_gas.py`) to
544 chunks of pigeonhole (8 and 10 pigeons) and random 3-SAT proofs, each measured in witness-sim
(`scripts/gas.sh`), at budgets from 2×10⁷ to 2×10⁹:

| Per | Gas |
|---|---|
| hint | 386 |
| literal visited (hinted clauses' and the step's own) | 112 |
| byte of chunk witness | 47 |
| hash proving the formula's clauses | 7,600 |
| byte of trusted clauses | 21 |

Measured gas was within −10% and +22% of the model. The planner budgets chunks at 3×10⁹ of it by
default, which stays under refine's 5×10⁹ at +22%. On these proofs a step averaged about 24k gas,
and a megabyte of chunk witness about 4×10⁸: about 12 MB of witness per refine, under a work
package's 13.8 MB.

What dominates is the RUP loop: per hint and per literal visited. A pigeonhole step visits about
70 literals over 15 hints; a step with long learned clauses visits more.

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

Numbers to follow: CaDiCaL's time and proof size, the trimmed steps, the chunk plan, and gas and
wall time in witness-sim.
