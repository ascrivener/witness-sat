//! The binary encodings: LEB128 numbers, and clauses as sorted literal codes.
//!
//! A literal is coded `2(v − 1)` for variable `v` and `2(v − 1) + 1` for its negation, so codes
//! of a formula over `n` variables are below `2n`, and `code ^ 1` negates. A clause is its length,
//! then its codes in strictly increasing order, the first as it is and each after as its
//! distance from the one before: all LEB128. So a clause has exactly one encoding, and the empty
//! clause is the single byte 0.

use alloc::vec::Vec;

/// Reads LEB128 numbers and clauses off the front of a byte slice. Running off the end, or a
/// clause that isn't canonical, fails the check ([`crate::fail`]); other malformations are `None`.
///
/// Checks pay for every load and store (PolkaVM's cost model charges an L2 hit each), and a check
/// spends most of its gas here, so the reader is inlined into its callers, which keep its
/// position in a register, and a one-byte number, the usual kind, takes one load.
pub struct Reader<'a> {
	bytes: &'a [u8],
	pos: usize,
}

impl<'a> Reader<'a> {
	pub fn new(bytes: &'a [u8]) -> Self {
		Reader { bytes, pos: 0 }
	}

	/// An unsigned LEB128 number of at most 32 bits, in its shortest form.
	#[inline(always)]
	pub fn u32(&mut self) -> Option<u32> {
		crate::ensure(self.pos < self.bytes.len());
		// SAFETY: just checked.
		let b = unsafe { *self.bytes.get_unchecked(self.pos) };
		self.pos += 1;
		if b < 0x80 {
			return Some(b as u32);
		}
		self.u32_long(b)
	}

	#[inline(never)]
	fn u32_long(&mut self, first: u8) -> Option<u32> {
		let mut value = (first & 0x7f) as u32;
		for shift in [7, 14, 21, 28] {
			let b = *self.bytes.get(self.pos)?;
			self.pos += 1;
			let bits = (b & 0x7f) as u32;
			if shift == 28 && bits > 0x0f {
				return None;
			}
			value |= bits << shift;
			if b & 0x80 == 0 {
				// A trailing zero byte would make a second encoding of the same number.
				return (b != 0).then_some(value);
			}
		}
		None
	}

	pub fn bytes(&mut self, n: usize) -> Option<&'a [u8]> {
		let out = self.bytes.get(self.pos..self.pos.checked_add(n)?)?;
		self.pos += n;
		Some(out)
	}

	pub fn hash(&mut self) -> Option<&'a [u8; 32]> {
		self.bytes(32)?.try_into().ok()
	}

	/// A clause's codes, appended to `out`, each below `limit`. Returns its encoding.
	#[inline(always)]
	pub fn clause(&mut self, limit: u32, out: &mut Vec<u32>) -> Option<&'a [u8]> {
		let start = self.pos;
		let len = self.u32()?;
		// Every code takes a byte at least: refuse lengths the input can't hold before reserving.
		if len as usize > self.bytes.len() - self.pos {
			return None;
		}
		out.reserve(len as usize);
		// The first code as it is, the rest by distance: at least 1, so increasing.
		let mut wide = 0u64;
		for i in 0..len {
			let step = self.u32()? as u64;
			crate::ensure(step > 0 || i == 0);
			wide += step;
			crate::ensure(wide < limit as u64);
			out.push(wide as u32);
		}
		Some(&self.bytes[start..self.pos])
	}

	pub fn is_empty(&self) -> bool {
		self.pos == self.bytes.len()
	}
}

pub fn put_u32(out: &mut Vec<u8>, mut v: u32) {
	loop {
		let b = (v & 0x7f) as u8;
		v >>= 7;
		if v == 0 {
			out.push(b);
			return;
		}
		out.push(b | 0x80);
	}
}

/// Append the encoding of the clause with these codes, which must be strictly increasing.
pub fn put_clause(out: &mut Vec<u8>, codes: &[u32]) {
	put_u32(out, codes.len() as u32);
	let mut prev = 0;
	for (i, &c) in codes.iter().enumerate() {
		debug_assert!(i == 0 || c > prev, "codes must be strictly increasing");
		put_u32(out, if i == 0 { c } else { c - prev });
		prev = c;
	}
}

/// The encoding of the clause with these codes, which must be strictly increasing.
pub fn clause_bytes(codes: &[u32]) -> Vec<u8> {
	let mut out = Vec::with_capacity(codes.len() + 1);
	put_clause(&mut out, codes);
	out
}

/// The code of the DIMACS literal `lit` (nonzero).
pub fn code(lit: i32) -> u32 {
	2 * (lit.unsigned_abs() - 1) + (lit < 0) as u32
}

/// The DIMACS literal of `code`.
pub fn lit(code: u32) -> i32 {
	let v = (code / 2 + 1) as i32;
	if code & 1 == 1 { -v } else { v }
}
