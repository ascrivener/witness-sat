use super::*;
use enc::{clause_bytes, code};
use witness_types::{CheckBlob, CheckMode, check_args};

/// Codes of a DIMACS clause, sorted.
fn cl(lits: &[i32]) -> Vec<u32> {
	let mut c: Vec<u32> = lits.iter().map(|&l| code(l)).collect();
	c.sort();
	c.dedup();
	c
}

/// A formula's clauses, its tree's levels and its UNSAT params.
struct Formula_ {
	clauses: Vec<Vec<u32>>,
	levels: Vec<Vec<tree::Hash>>,
	f: Unsat,
}

fn formula(vars: u32, clauses: &[&[i32]]) -> Formula_ {
	let clauses: Vec<Vec<u32>> = clauses.iter().map(|c| cl(c)).collect();
	let levels = tree::levels(clauses.iter().map(|c| tree::leaf(&clause_bytes(c))).collect());
	let root = *levels.last().unwrap().first().unwrap();
	Formula_ { f: Unsat { vars, clauses: clauses.len() as u32, root }, clauses, levels }
}

impl Formula_ {
	/// A chunk using originals `uses` (increasing), after `trusted` trusted clauses, exporting each
	/// of `exports` as a bundle of its own.
	fn chunk(&self, trusted: u32, uses: &[u32], steps: &[(Vec<u32>, Vec<u32>)], exports: &[u32]) -> Vec<u8> {
		let exports: Vec<Vec<u32>> = exports.iter().map(|&e| vec![e]).collect();
		self.bundling(trusted, uses, steps, &exports)
	}

	fn bundling(&self, trusted: u32, uses: &[u32], steps: &[(Vec<u32>, Vec<u32>)], exports: &[Vec<u32>]) -> Vec<u8> {
		let originals: Vec<(u32, Vec<u32>)> = uses.iter().map(|&i| (i, self.clauses[i as usize].clone())).collect();
		let proof = tree::prove(&self.levels, uses);
		ChunkSpec { originals: &originals, proof: &proof, steps, exports }.encode(trusted)
	}
}

/// Whether `f` returns true; a failure ([`fail`], a panic off PolkaVM) is false.
fn ok(f: impl FnOnce() -> bool + std::panic::UnwindSafe) -> bool {
	let hook = std::panic::take_hook();
	std::panic::set_hook(Box::new(|_| {}));
	let result = std::panic::catch_unwind(f).unwrap_or(false);
	std::panic::set_hook(hook);
	result
}

/// The bundle of one clause.
fn one(codes: &[u32]) -> Vec<u8> {
	bundle([clause_bytes(codes).as_slice()].into_iter())
}

fn run(mode: CheckMode, trusted: &[&[u8]], plain_or_subjects: &[&[u8]], params: &[u8], witness: &[u8]) -> bool {
	let blobs: Vec<CheckBlob> = trusted
		.iter()
		.map(|d| CheckBlob { trusted: true, hash: tree::blake2b256(d), data: d })
		.chain(plain_or_subjects.iter().map(|d| CheckBlob { trusted: false, hash: tree::blake2b256(d), data: d }))
		.collect();
	let args = check_args(mode, &blobs, params, witness);
	ok(move || witness_check::run_full(&args, check) == 1)
}

#[test]
fn leb128_is_canonical() {
	for v in [0, 1, 127, 128, 300, 16383, 16384, u32::MAX] {
		let mut out = Vec::new();
		enc::put_u32(&mut out, v);
		let mut r = Reader::new(&out);
		assert_eq!(r.u32(), Some(v));
		assert!(r.is_empty());
	}
	let reads = |bytes: &'static [u8]| ok(move || Reader::new(bytes).u32().is_some());
	assert!(!reads(&[0x80, 0x00]), "padded zero");
	assert!(!reads(&[0x81, 0x00]), "padded one");
	assert!(!reads(&[0xff, 0xff, 0xff, 0xff, 0x1f]), "over 32 bits");
	assert!(!reads(&[0x80]), "truncated");
	assert!(!reads(&[]), "empty");
}

#[test]
fn clauses_have_one_encoding() {
	let c = cl(&[3, -1, 7]);
	let bytes = clause_bytes(&c);
	let mut out = Vec::new();
	assert_eq!(Reader::new(&bytes).clause(14, &mut out), Some(&bytes[..]));
	assert_eq!(out, c);
	let reads = |bytes: Vec<u8>, limit| ok(move || Reader::new(&bytes).clause(limit, &mut Vec::new()).is_some());
	assert!(!reads(bytes.clone(), 12), "variable 7 of 6");
	// A repeated literal would be a distance of zero.
	assert!(!reads(vec![2, 4, 0], 100));
	assert!(!reads(vec![200, 1], 1000), "length past the end");
	assert!(reads(vec![2, 4, 1], 100));
	assert_eq!(clause_bytes(&[]), EMPTY);
	for l in [1, -1, 5, -5, 1000] {
		assert_eq!(enc::lit(code(l)), l);
	}
}

#[test]
fn multiproofs() {
	for width in 1..40u32 {
		let leaves: Vec<tree::Hash> = (0..width).map(|i| tree::blake2b256(&i.to_le_bytes())).collect();
		let levels = tree::levels(leaves.clone());
		let root = levels.last().unwrap()[0];
		// Agrees with witness's tree.
		assert_eq!(root, witness_types::merkle::root(&leaves));
		for mask in [1u64, 3, 5, 0b1011, (1 << width.min(63)) - 1, 0x5555_5555_5555, 1 << (width - 1)] {
			let indices: Vec<u32> = (0..width).filter(|&i| mask >> i & 1 == 1).collect();
			if indices.is_empty() {
				continue;
			}
			let proof = tree::prove(&levels, &indices);
			let with = |f: &dyn Fn(u32) -> tree::Hash| indices.iter().map(|&i| (i, f(i))).collect::<Vec<_>>();
			assert!(tree::verify(&root, width, with(&|i| leaves[i as usize]), &proof), "width {width} mask {mask:b}");
			assert!(!tree::verify(&root, width, with(&|i| tree::blake2b256(&[i as u8, 9])), &proof));
			let mut longer = proof.clone();
			longer.push([0; 32]);
			assert!(!tree::verify(&root, width, with(&|i| leaves[i as usize]), &longer), "extra hash");
			if let Some((_, shorter)) = proof.split_last() {
				assert!(!tree::verify(&root, width, with(&|i| leaves[i as usize]), shorter), "missing hash");
			}
		}
	}
}

#[test]
fn sat_bounties() {
	// (x1 ∨ x2) ∧ (¬x1 ∨ x3) ∧ (¬x2 ∨ ¬x3)
	let f = Formula::encode(3, &[cl(&[1, 2]), cl(&[-1, 3]), cl(&[-2, -3])]);
	let x = |bits: u8| [bits];
	assert!(satisfies(&f, &x(0b101)), "x1, x3");
	assert!(satisfies(&f, &x(0b010)), "x2");
	assert!(!satisfies(&f, &x(0b111)));
	assert!(!satisfies(&f, &x(0b000)));
	assert!(!satisfies(&f, &x(0b1101)), "padding bit set");
	assert!(!satisfies(&f, &[0b101, 0]), "too long");
	assert!(run(CheckMode::Reveal, &[], &[&f], &[SAT], &x(0b101)));
	assert!(!run(CheckMode::Reveal, &[], &[&f], &[SAT], &x(0b111)));
	assert!(!run(CheckMode::Reveal, &[], &[&f, &f], &[SAT], &x(0b101)), "two blobs");
	assert!(!run(CheckMode::Reveal, &[], &[], &[SAT], &x(0b101)), "no formula");
	assert!(!run(CheckMode::Reveal, &[&f], &[], &[SAT], &x(0b101)), "a trusted formula");
	assert!(!run(CheckMode::Attest, &[], &[&f], &[SAT], &x(0b101)), "SAT never attests");
	assert!(!run(CheckMode::Reveal, &[], &[&f], &[SAT, 0], &x(0b101)), "long params");
	assert!(!run(CheckMode::Reveal, &[], &[&f[..f.len() - 1]], &[SAT], &x(0b101)), "truncated formula");
}

/// (x1) ∧ (¬x1 ∨ x2) ∧ (¬x2 ∨ x3) ∧ (¬x3): unsatisfiable by unit propagation.
fn chain() -> Formula_ {
	formula(3, &[&[1], &[-1, 2], &[-2, 3], &[-3]])
}

#[test]
fn a_refutation_in_one_chunk() {
	let fm = chain();
	let p = fm.f.encode();
	// Originals 0..4 are numbered 0..4; the step is 4.
	let steps = [(vec![], vec![0, 1, 2, 3])];
	let chunk = fm.chunk(0, &[0, 1, 2, 3], &steps, &[4]);
	assert!(check_chunk(&fm.f, [].into_iter(), &chunk, &[EMPTY_BUNDLE]));
	assert!(run(CheckMode::Reveal, &[], &[], &p, &chunk), "a reveal can carry the whole proof");
	assert!(run(CheckMode::Attest, &[], &[EMPTY_BUNDLE], &p, &chunk), "or attest it");
	assert!(!run(CheckMode::Attest, &[], &[EMPTY], &p, &chunk), "a clause isn't a bundle");

	// Hints out of order: x3 isn't unit until x2 is set.
	let bad = fm.chunk(0, &[0, 1, 2, 3], &[(vec![], vec![0, 2, 1, 3])], &[4]);
	assert!(!run(CheckMode::Reveal, &[], &[], &p, &bad));
	// A hint missing: no conflict.
	let bad = fm.chunk(0, &[0, 1, 2, 3], &[(vec![], vec![0, 1, 2])], &[4]);
	assert!(!run(CheckMode::Reveal, &[], &[], &p, &bad));
	// (A hint can't name the step itself or a later one: hints are distances back.) One past the
	// first clause fails.
	let mut bad = fm.chunk(0, &[0, 1, 2, 3], &steps, &[4]);
	// The chunk ends with the hints, then the exports: 1 bundle of 1 clause, number 4.
	let hints_at = bad.len() - 3 - 4;
	assert_eq!(bad[hints_at..hints_at + 4], [3, 2, 1, 0], "the hints, as distances");
	bad[hints_at] = 4;
	assert!(!run(CheckMode::Reveal, &[], &[], &p, &bad));
	// Exporting the wrong clause.
	let bad = fm.chunk(0, &[0, 1, 2, 3], &steps, &[3]);
	assert!(!run(CheckMode::Reveal, &[], &[], &p, &bad));
	// Another formula's params.
	let other = formula(3, &[&[1], &[-1, 2], &[-2, 3]]);
	assert!(!run(CheckMode::Reveal, &[], &[], &other.f.encode(), &chunk));
	let mut fewer_vars = fm.f;
	fewer_vars.vars = 2;
	assert!(!run(CheckMode::Reveal, &[], &[], &fewer_vars.encode(), &chunk), "x3 out of range");
}

#[test]
fn originals_must_be_in_the_formula() {
	let fm = chain();
	let p = fm.f.encode();
	// Claim a unit clause (¬x2), not in the formula, as original 1, with original 1's proof.
	let originals = [(0, cl(&[1])), (1, cl(&[-2]))];
	let proof = tree::prove(&fm.levels, &[0, 1]);
	let steps = [(vec![], vec![0, 1])];
	let forged = ChunkSpec { originals: &originals, proof: &proof, steps: &steps, exports: &[vec![2]] }.encode(0);
	assert!(!run(CheckMode::Reveal, &[], &[], &p, &forged));
	// Or as original 2 (the indices must match the proof too).
	let originals = [(0, cl(&[1])), (2, cl(&[-1, 2]))];
	let proof = tree::prove(&fm.levels, &[0, 1]);
	let forged = ChunkSpec { originals: &originals, proof: &proof, steps: &[], exports: &[vec![1]] }.encode(0);
	assert!(!run(CheckMode::Attest, &[], &[&one(&cl(&[-1, 2]))], &p, &forged));
}

#[test]
fn chunks_build_on_attested_clauses() {
	let fm = chain();
	let p = fm.f.encode();
	// Chunk A: from (x1) and (¬x1 ∨ x2), derive (x2); attest it.
	let x2 = one(&cl(&[2]));
	let a = fm.chunk(0, &[0, 1], &[(cl(&[2]), vec![0, 1])], &[2]);
	assert!(run(CheckMode::Attest, &[], &[&x2], &p, &a));
	// A wrong subject.
	assert!(!run(CheckMode::Attest, &[], &[&one(&cl(&[3]))], &p, &a));
	assert!(!run(CheckMode::Attest, &[], &[], &p, &a), "no subjects");
	// Chunk B: trusting (x2), with (¬x2 ∨ x3) and (¬x3), derive the empty clause. Trusted is
	// clause 0, originals 2 and 3 are 1 and 2, the step 3.
	let b = fm.chunk(1, &[2, 3], &[(vec![], vec![0, 1, 2])], &[3]);
	assert!(run(CheckMode::Attest, &[&x2], &[EMPTY_BUNDLE], &p, &b));
	assert!(!run(CheckMode::Attest, &[], &[EMPTY_BUNDLE], &p, &b), "without the trusted clause");
	// A reveal trusting the attested empty clause is paid, whatever its witness.
	assert!(run(CheckMode::Reveal, &[&x2, EMPTY_BUNDLE], &[], &p, b"hunter's tag"));
	assert!(!run(CheckMode::Reveal, &[&x2], &[], &p, b"hunter's tag"));
	assert!(!run(CheckMode::Reveal, &[EMPTY_BUNDLE], &[], &[SAT], b""), "an UNSAT clause for a SAT bounty");
	// A malformed trusted blob fails the chunk.
	assert!(!run(CheckMode::Attest, &[&[1, 2, 3]], &[EMPTY_BUNDLE], &p, &b));
}

#[test]
fn an_anchor_is_an_original_clause() {
	let fm = chain();
	let p = fm.f.encode();
	let anchor = fm.chunk(0, &[2], &[], &[0]);
	assert!(run(CheckMode::Attest, &[], &[&one(&fm.clauses[2])], &p, &anchor));
	assert!(!run(CheckMode::Attest, &[], &[&one(&fm.clauses[1])], &p, &anchor));
}

#[test]
fn tautologies_and_satisfied_hints() {
	let fm = chain();
	let p = fm.f.encode();
	// (x1 ∨ ¬x1) needs no hints.
	let taut = fm.chunk(0, &[0], &[(cl(&[1, -1]), vec![])], &[1]);
	assert!(run(CheckMode::Attest, &[], &[&one(&cl(&[1, -1]))], &p, &taut));
	// Deriving (x2 ∨ x1) citing (x1), satisfied by the assumption ¬(x2 ∨ x1)? No: (x1) is
	// falsified then, a conflict at once. But citing (¬x1 ∨ x2) when x1 is false satisfies it.
	let good = fm.chunk(0, &[0], &[(cl(&[1, 2]), vec![0])], &[1]);
	assert!(run(CheckMode::Attest, &[], &[&one(&cl(&[1, 2]))], &p, &good));
	let satisfied = fm.chunk(0, &[0, 1], &[(cl(&[-1, 2]), vec![0, 1])], &[2]);
	assert!(!run(CheckMode::Attest, &[], &[&one(&cl(&[-1, 2]))], &p, &satisfied));
}

#[test]
fn bundles_hold_several_clauses() {
	let fm = chain();
	let p = fm.f.encode();
	// Chunk A derives (x2), then (x3), and exports both in one bundle, and (x3) alone in another.
	let steps = [(cl(&[2]), vec![0, 1]), (cl(&[3]), vec![3, 2])];
	let a = fm.bundling(0, &[0, 1, 2], &steps, &[vec![3, 4], vec![4]]);
	let x2 = clause_bytes(&cl(&[2]));
	let x3 = clause_bytes(&cl(&[3]));
	let both = bundle([x2.as_slice(), x3.as_slice()].into_iter());
	assert!(run(CheckMode::Attest, &[], &[&both, &one(&cl(&[3]))], &p, &a));
	let swapped = bundle([x3.as_slice(), x2.as_slice()].into_iter());
	assert!(!run(CheckMode::Attest, &[], &[&swapped, &one(&cl(&[3]))], &p, &a), "order matters");
	assert!(!run(CheckMode::Attest, &[], &[&one(&cl(&[2])), &one(&cl(&[3]))], &p, &a), "a bundle short a clause");
	let mut extra = both.clone();
	extra.push(0);
	assert!(!run(CheckMode::Attest, &[], &[&extra, &one(&cl(&[3]))], &p, &a), "trailing bytes");
	// Chunk B trusts the bundle: its clauses are 0 and 1, then original 3 (¬x3) is 2.
	let b = fm.chunk(2, &[3], &[(vec![], vec![1, 2])], &[3]);
	assert!(run(CheckMode::Attest, &[&both], &[EMPTY_BUNDLE], &p, &b));
	// The empty clause in a bigger bundle pays too.
	let late = bundle([x2.as_slice(), EMPTY].into_iter());
	assert!(run(CheckMode::Reveal, &[&late], &[], &p, b""));
}
