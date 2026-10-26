//! Checking a chunk of an LRAT proof: clauses added by reverse unit propagation (RUP) over the
//! clauses their hints name.
//!
//! A chunk sees three kinds of clause, numbered in one space, in this order:
//!
//! 1. **trusted:** clauses earlier chunks derived, attested (the check's trusted blobs);
//! 2. **original:** clauses of the formula, proven in it by a Merkle multiproof;
//! 3. **steps:** clauses the chunk derives, each from clauses before it.
//!
//! Every one is implied by the formula, so a chunk that checks derives only implied clauses. An
//! LRAT proof's clause ids, its deletions, and its steps no later chunk uses aren't the check's
//! business: `sat-report plan` renumbers each chunk's hints into this space, drops deletions (they
//! only save a checker memory), and trims steps the empty clause doesn't need.
//!
//! RAT steps (LRAT's negative hints) aren't supported: checking one needs every clause holding
//! the pivot's negation, which a chunk doesn't have. CaDiCaL's LRAT has none.

use crate::{enc::Reader, ensure};
use alloc::{vec, vec::Vec};

/// Literals a clause is stored in groups of, padded with [`Chunk::pad`].
const GROUP: usize = 4;

/// The clauses a chunk has seen, by number, and the assignment RUP checks build.
///
/// Checks pay about 20 gas a conditional branch (PolkaVM's cost model takes every one for a
/// misprediction, unless it leads to a trap) and 25 cycles a load, and nearly all of a chunk's
/// gas goes on visiting hint clauses' literals. So clauses are stored padded to whole groups of
/// [`GROUP`] literals with a sentinel literal that is always false, and a hint's literals are
/// counted a group at a time without branching.
pub struct Chunk<'a> {
	/// Literal codes are below this: twice the formula's variables. The sentinel is `limit`, its
	/// negation `limit + 1`.
	limit: u32,
	codes: Vec<u32>,
	/// Clause `i`'s codes, padded, are `codes[starts[i]..starts[i + 1]]`.
	starts: Vec<u32>,
	/// Each clause's encoding, to compare with subjects.
	encodings: Vec<&'a [u8]>,
	/// A literal is true in the current check when its entry is `stamp`.
	true_at: Vec<u32>,
	stamp: u32,
}

impl<'a> Chunk<'a> {
	pub fn new(vars: u32) -> Option<Self> {
		let limit = vars.checked_mul(2)?;
		Some(Chunk {
			limit,
			codes: Vec::new(),
			starts: vec![0],
			encodings: Vec::new(),
			true_at: vec![0; limit.checked_add(2)? as usize],
			stamp: 0,
		})
	}

	pub fn len(&self) -> usize {
		self.encodings.len()
	}

	pub fn encoding(&self, i: usize) -> Option<&'a [u8]> {
		self.encodings.get(i).copied()
	}

	/// Read a clause off `r` and number it next. Its encoding is returned.
	pub fn push(&mut self, r: &mut Reader<'a>) -> Option<&'a [u8]> {
		let encoding = r.clause(self.limit, &mut self.codes)?;
		let pad = self.codes.len().next_multiple_of(GROUP);
		self.codes.resize(pad, self.limit);
		self.starts.push(self.codes.len() as u32);
		self.encodings.push(encoding);
		Some(encoding)
	}

	/// Number a clause whose encoding is all of `bytes`.
	pub fn push_whole(&mut self, bytes: &'a [u8]) -> Option<()> {
		let mut r = Reader::new(bytes);
		self.push(&mut r)?;
		r.is_empty().then_some(())
	}

	/// Read a step (its clause, then its hints as distances back from it), check it by RUP, and
	/// number it next.
	pub fn step(&mut self, r: &mut Reader<'a>) -> Option<()> {
		let at = self.len() as u32;
		self.push(r)?;
		let hints = r.u32()?;
		self.stamp = self.stamp.checked_add(1)?;
		let stamp = self.stamp;
		let t = &mut self.true_at;
		let codes = &self.codes;
		// The sentinel is false.
		t[self.limit as usize + 1] = stamp;
		// Assume the clause false. A clause holding both a literal and its negation is a tautology,
		// implied by anything.
		let mut tautology = false;
		for &c in &codes[self.starts[at as usize] as usize..] {
			tautology |= t[c as usize] == stamp;
			t[(c ^ 1) as usize] = stamp;
		}
		let mut conflict = tautology;
		for _ in 0..hints {
			let distance = r.u32()?;
			if conflict {
				continue;
			}
			// Hints are distances back, so `hint < at` unless it wrapped.
			let hint = at.wrapping_sub(distance).wrapping_sub(1) as usize;
			ensure(hint < at as usize);
			// SAFETY: `starts` has an entry for every clause numbered, and one past.
			let (start, end) = unsafe { (*self.starts.get_unchecked(hint), *self.starts.get_unchecked(hint + 1)) };
			// SAFETY: `starts` are offsets into `codes`, increasing.
			let clause = unsafe { codes.get_unchecked(start as usize..end as usize) };
			// The hint must be unit (one literal not yet false, which becomes true) or falsified
			// (the conflict). A satisfied hint or one with two open literals fails the step.
			let (mut open, mut satisfied, mut unit) = (0u32, 0u32, 0u32);
			for group in clause.chunks_exact(GROUP) {
				for &c in group {
					// SAFETY: every code is below `limit + 2`, the length of `t`: `Reader::clause`
					// refuses codes from `limit`, and padding is `limit`.
					let (is_false, is_true) =
						unsafe { (*t.get_unchecked((c ^ 1) as usize) == stamp, *t.get_unchecked(c as usize) == stamp) };
					open += !is_false as u32;
					satisfied |= is_true as u32;
					let keep = (is_false as u32).wrapping_neg();
					unit = (unit & keep) | (c & !keep);
				}
			}
			ensure(open == 0 || open == 1 && satisfied == 0);
			conflict = open == 0;
			// SAFETY: `unit` is a code from the clause, below `limit + 2`; with no open literal
			// it's 0, and the conflict ends the step anyway.
			unsafe { *t.get_unchecked_mut(unit as usize) = stamp };
		}
		conflict.then_some(())
	}
}
