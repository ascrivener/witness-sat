//! Streaming LRAT, text or binary (as CaDiCaL writes with `--lrat` and `--lrat --binary`).
//!
//! Text: `ID LIT… 0 HINT… 0` adds a clause, `ID d ID… 0` deletes. Binary: `a`, then the id, the
//! literals and a 0, the hints and a 0; or `d`, then ids and a 0; every number as a LEB128 of
//! `2|x| + (x < 0)`. Deletions are skipped. A negative hint is a RAT step, which the check doesn't
//! support, so reading one is an error.

use std::io::{self, BufRead, BufReader, Read};

/// One added clause.
#[derive(Clone, Debug, Default)]
pub struct Step {
	pub id: u64,
	pub lits: Vec<i32>,
	pub hints: Vec<u64>,
}

pub struct Reader {
	input: BufReader<Box<dyn Read>>,
	binary: bool,
	line: Vec<u8>,
}

fn bad(msg: impl Into<String>) -> io::Error {
	io::Error::new(io::ErrorKind::InvalidData, msg.into())
}

impl Reader {
	pub fn new(input: Box<dyn Read>) -> io::Result<Self> {
		let mut input = BufReader::with_capacity(1 << 20, input);
		let binary = matches!(input.fill_buf()?.first(), Some(b'a' | b'd'));
		Ok(Reader { input, binary, line: Vec::new() })
	}

	fn byte(&mut self) -> io::Result<Option<u8>> {
		let buf = self.input.fill_buf()?;
		let Some(&b) = buf.first() else { return Ok(None) };
		self.input.consume(1);
		Ok(Some(b))
	}

	fn signed(&mut self) -> io::Result<i64> {
		let mut v = 0u64;
		for shift in (0..64).step_by(7) {
			let b = self.byte()?.ok_or_else(|| bad("truncated binary LRAT"))?;
			v |= ((b & 0x7f) as u64) << shift;
			if b & 0x80 == 0 {
				let magnitude = (v >> 1) as i64;
				return Ok(if v & 1 == 1 { -magnitude } else { magnitude });
			}
		}
		Err(bad("overlong number in binary LRAT"))
	}

	/// The next added clause, filled into `step`; false at the end.
	pub fn next(&mut self, step: &mut Step) -> io::Result<bool> {
		step.lits.clear();
		step.hints.clear();
		if self.binary { self.next_binary(step) } else { self.next_text(step) }
	}

	fn next_binary(&mut self, step: &mut Step) -> io::Result<bool> {
		loop {
			match self.byte()? {
				None => return Ok(false),
				Some(b'd') => while self.signed()? != 0 {},
				Some(b'a') => {
					step.id = self.signed()? as u64;
					loop {
						match self.signed()? {
							0 => break,
							l => step.lits.push(i32::try_from(l).map_err(|_| bad("literal too large"))?),
						}
					}
					loop {
						match self.signed()? {
							0 => return Ok(true),
							h if h < 0 => return Err(bad(format!("clause {}: a RAT hint", step.id))),
							h => step.hints.push(h as u64),
						}
					}
				},
				Some(b) => return Err(bad(format!("binary LRAT: unexpected byte {b:#x}"))),
			}
		}
	}

	fn next_text(&mut self, step: &mut Step) -> io::Result<bool> {
		loop {
			self.line.clear();
			if self.input.read_until(b'\n', &mut self.line)? == 0 {
				return Ok(false);
			}
			let line = std::str::from_utf8(&self.line).map_err(|_| bad("LRAT is not text"))?;
			let mut words = line.split_ascii_whitespace();
			let Some(id) = words.next() else { continue };
			if id.starts_with('c') {
				continue;
			}
			let mut words = words.peekable();
			if words.peek() == Some(&"d") {
				continue;
			}
			step.id = id.parse().map_err(|_| bad(format!("bad id {id}")))?;
			let mut in_hints = false;
			for w in words {
				let x: i64 = w.parse().map_err(|_| bad(format!("bad number {w}")))?;
				match (x, in_hints) {
					(0, false) => in_hints = true,
					(0, true) => return Ok(true),
					(l, false) => step.lits.push(l as i32),
					(h, true) if h < 0 => return Err(bad(format!("clause {}: a RAT hint", step.id))),
					(h, true) => step.hints.push(h as u64),
				}
			}
			return Err(bad(format!("clause {}: unterminated", step.id)));
		}
	}
}
