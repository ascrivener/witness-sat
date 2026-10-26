//! Witness check for SAT certificates. One check serves two kinds of bounty, chosen by the first
//! byte of the params:
//!
//! - **SAT** (`[0]`): the bounty's one plain blob is a formula ([`Formula`] encoding); the witness
//!   is an assignment satisfying it, one bit a variable (variable `v` is bit `v − 1`, least
//!   significant first), exactly ⌈vars/8⌉ bytes with the padding bits clear.
//! - **UNSAT** (`[1] ++ vars ++ clauses ++ root`, [`Unsat`]): the formula has `vars` variables
//!   and its `clauses` clauses, in order, have the Merkle root `root` (see [`tree`]). The bounty
//!   pays for a refutation, an LRAT proof, attested in chunks:
//!   - **Attest mode**, with these params: the subjects are clauses the formula implies. The
//!     witness is a chunk of proof steps ([`check_chunk`]), checked by RUP over the trusted
//!     clauses (subjects of earlier attestations, so implied too), the formula's clauses it proves
//!     in the tree, and its own earlier steps; each subject must be one of those clauses. So by
//!     induction every attested subject is implied by the formula.
//!   - **Reveal mode:** the bounty is paid if a trusted blob is the empty clause: an attestation
//!     derived it, so the formula is unsatisfiable. Or the witness is a chunk that derives it,
//!     for a proof small enough to check in one go.
//!
//! witness lets a reveal trust attested subjects only if its bounty cites one, and a bounty fixes
//! the attest params of everything its reveals trust to those of what it cites. So an UNSAT
//! bounty cites an attested clause of its formula: an *anchor*, a chunk with no steps that proves
//! one original clause in the tree. Anyone can attest it from the formula alone, before any proof
//! exists, so the bounty can be posted first.
//!
//! Clauses, as subjects and in chunks, are encoded canonically ([`enc`]), so a clause has one
//! hash.

#![cfg_attr(not(test), no_std)]

extern crate alloc;

pub mod enc;
pub mod lrat;
pub mod tree;

/// Fail the check: on PolkaVM, a trap, which the service counts as false; elsewhere a panic.
///
/// A conditional branch costs about 20 gas unless it leads straight to a trap, which costs 1,
/// so hot loops check what they rely on with [`ensure`] rather than returning `None`.
#[inline(always)]
pub fn fail() -> ! {
	#[cfg(target_env = "polkavm")]
	unsafe {
		core::arch::asm!("unimp", options(noreturn))
	}
	#[cfg(not(target_env = "polkavm"))]
	panic!("the check fails")
}

/// Fail the check unless `cond`.
#[inline(always)]
pub fn ensure(cond: bool) {
	if !cond {
		fail()
	}
}

use alloc::vec::Vec;
use enc::Reader;
use lrat::Chunk;
use witness_check::{Input, Mode};

// A chunk's steps live on the heap; the stack only needs the usual room.
#[cfg(any(target_arch = "riscv32", target_arch = "riscv64"))]
polkavm_derive::min_stack_size!(64 * 1024);

pub const SAT: u8 = 0;
pub const UNSAT: u8 = 1;

/// The empty clause's encoding.
pub const EMPTY: &[u8] = &[0];

/// An unsatisfiable bounty's formula, as its params commit to it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Unsat {
	pub vars: u32,
	pub clauses: u32,
	pub root: tree::Hash,
}

impl Unsat {
	pub fn parse(params: &[u8]) -> Option<Self> {
		let [UNSAT, rest @ ..] = params else { return None };
		let (vars, rest) = rest.split_first_chunk::<4>()?;
		let (clauses, rest) = rest.split_first_chunk::<4>()?;
		let root = rest.try_into().ok()?;
		Some(Unsat { vars: u32::from_le_bytes(*vars), clauses: u32::from_le_bytes(*clauses), root })
	}

	pub fn encode(&self) -> Vec<u8> {
		[&[UNSAT][..], &self.vars.to_le_bytes(), &self.clauses.to_le_bytes(), &self.root].concat()
	}
}

/// A formula as a SAT bounty's blob: LEB128 `vars` and `clauses`, then the clauses ([`enc`]).
pub struct Formula;

impl Formula {
	pub fn encode(vars: u32, clauses: &[Vec<u32>]) -> Vec<u8> {
		let mut out = Vec::new();
		enc::put_u32(&mut out, vars);
		enc::put_u32(&mut out, clauses.len() as u32);
		for c in clauses {
			enc::put_clause(&mut out, c);
		}
		out
	}
}

/// Whether `assignment` satisfies the formula `formula`.
pub fn satisfies(formula: &[u8], assignment: &[u8]) -> bool {
	let mut r = Reader::new(formula);
	let (Some(vars), Some(clauses)) = (r.u32(), r.u32()) else { return false };
	let Some(limit) = vars.checked_mul(2) else { return false };
	if assignment.len() != vars.div_ceil(8) as usize ||
		(vars % 8 != 0 && assignment.last().is_some_and(|b| b >> (vars % 8) != 0))
	{
		return false;
	}
	let is_true = |c: u32| (assignment[(c / 16) as usize] >> (c / 2 % 8) & 1) as u32 != c & 1;
	let mut codes = Vec::new();
	for _ in 0..clauses {
		codes.clear();
		if r.clause(limit, &mut codes).is_none() || !codes.iter().any(|&c| is_true(c)) {
			return false;
		}
	}
	r.is_empty()
}

/// Check a chunk: the witness `chunk`, given the formula `f` and the `trusted` clauses (each an
/// encoding), derives every clause in `subjects`. A chunk is, in LEB128 ([`enc`]):
///
/// ```text
/// originals  count, then each one's index in the formula (the first as it is, then each as
///            its distance from the one before), then each clause; then the multiproof's
///            hash count and hashes (32 bytes each), proving them in the tree
/// steps      count, then each one's clause, hint count, and hints, each as how far back from
///            the step the clause it names is numbered (0 for the one just before it)
/// exports    count, then each one's number: subject i must be clause exports[i]
/// ```
///
/// Clauses are numbered trusted first, then originals, then steps ([`lrat`]).
pub fn check_chunk<'a>(f: &Unsat, trusted: impl Iterator<Item = &'a [u8]>, chunk: &'a [u8], subjects: &[&[u8]]) -> bool {
	chunk_derives(f, trusted, chunk, subjects).is_some()
}

/// A chunk to encode: hints and exports are clause numbers (trusted, then originals, then steps).
pub struct ChunkSpec<'a> {
	/// The formula's clauses the chunk uses, by index, increasing, with their codes.
	pub originals: &'a [(u32, Vec<u32>)],
	pub proof: &'a [tree::Hash],
	/// Each step's clause codes (increasing) and hints.
	pub steps: &'a [(Vec<u32>, Vec<u32>)],
	pub exports: &'a [u32],
}

impl ChunkSpec<'_> {
	/// The chunk's encoding, given how many trusted clauses come before its originals.
	pub fn encode(&self, trusted: u32) -> Vec<u8> {
		let mut out = Vec::new();
		let put = enc::put_u32;
		put(&mut out, self.originals.len() as u32);
		let mut prev = 0;
		for (k, &(i, _)) in self.originals.iter().enumerate() {
			put(&mut out, if k == 0 { i } else { i - prev });
			prev = i;
		}
		for (_, codes) in self.originals {
			enc::put_clause(&mut out, codes);
		}
		put(&mut out, self.proof.len() as u32);
		for h in self.proof {
			out.extend_from_slice(h);
		}
		put(&mut out, self.steps.len() as u32);
		let first = trusted + self.originals.len() as u32;
		for (s, (codes, hints)) in self.steps.iter().enumerate() {
			enc::put_clause(&mut out, codes);
			put(&mut out, hints.len() as u32);
			for &h in hints {
				put(&mut out, first + s as u32 - 1 - h);
			}
		}
		put(&mut out, self.exports.len() as u32);
		for &e in self.exports {
			put(&mut out, e);
		}
		out
	}
}

fn chunk_derives<'a>(f: &Unsat, trusted: impl Iterator<Item = &'a [u8]>, chunk: &'a [u8], subjects: &[&[u8]]) -> Option<()> {
	let mut c = Chunk::new(f.vars)?;
	for t in trusted {
		c.push_whole(t)?;
	}
	let mut r = Reader::new(chunk);

	let originals = r.u32()?;
	let mut indices: Vec<u32> = Vec::with_capacity(originals.min(f.clauses) as usize);
	for k in 0..originals {
		let step = r.u32()?;
		let i = if k == 0 { step } else if step == 0 { return None } else { indices.last().copied()?.checked_add(step)? };
		indices.push(i);
	}
	let mut leaves = Vec::with_capacity(indices.len());
	for &i in &indices {
		leaves.push((i, tree::leaf(c.push(&mut r)?)));
	}
	let hashes = r.u32()? as usize;
	let proof: Vec<tree::Hash> = (0..hashes).map(|_| r.hash().copied()).collect::<Option<_>>()?;
	if !tree::verify(&f.root, f.clauses, leaves, &proof) {
		return None;
	}

	for _ in 0..r.u32()? {
		c.step(&mut r)?;
	}

	let exports = r.u32()? as usize;
	if exports != subjects.len() {
		return None;
	}
	for s in subjects {
		if c.encoding(r.u32()? as usize)? != *s {
			return None;
		}
	}
	r.is_empty().then_some(())
}

fn check(input: &Input) -> bool {
	match (input.params.first(), input.mode) {
		(Some(&SAT), Mode::Reveal) => {
			let mut blobs = input.blobs();
			input.params.len() == 1 &&
				input.blobs().len() == 1 &&
				blobs.next().is_some_and(|b| !b.trusted && satisfies(b.data, input.witness))
		},
		(Some(&UNSAT), mode) => {
			let Some(f) = Unsat::parse(input.params) else { return false };
			let trusted = input.trusted().map(|b| b.data);
			match mode {
				Mode::Attest => {
					let subjects: Vec<&[u8]> = input.subjects().map(|b| b.data).collect();
					!subjects.is_empty() && check_chunk(&f, trusted, input.witness, &subjects)
				},
				Mode::Reveal => {
					input.trusted().any(|b| b.data == EMPTY) || check_chunk(&f, trusted, input.witness, &[EMPTY])
				},
			}
		},
		_ => false,
	}
}

witness_check::declare_full_check!(check);

#[cfg(test)]
mod tests;
