//! DIMACS CNF in, and the encodings and tree witness-sat's check uses out.

use sat_check::{Unsat, enc, tree};
use std::{fs, io};

pub struct Cnf {
	pub vars: u32,
	/// Each clause's literal codes, sorted and deduplicated ([`enc`]).
	pub clauses: Vec<Vec<u32>>,
}

fn bad(msg: impl Into<String>) -> io::Error {
	io::Error::new(io::ErrorKind::InvalidData, msg.into())
}

/// Sort and deduplicate a clause's codes.
pub fn canonical(mut codes: Vec<u32>) -> Vec<u32> {
	codes.sort_unstable();
	codes.dedup();
	codes
}

impl Cnf {
	pub fn read(path: &str) -> io::Result<Self> {
		let text = fs::read_to_string(path)?;
		let mut vars = None;
		let mut declared = 0usize;
		let mut clauses = Vec::new();
		let mut clause = Vec::new();
		for line in text.lines() {
			let line = line.trim();
			if line.starts_with('c') || line.is_empty() || line.starts_with('%') {
				continue;
			}
			if let Some(header) = line.strip_prefix("p cnf") {
				let mut it = header.split_whitespace().map(|w| w.parse::<u32>());
				match (it.next(), it.next()) {
					(Some(Ok(v)), Some(Ok(c))) => (vars, declared) = (Some(v), c as usize),
					_ => return Err(bad(format!("bad header: {line}"))),
				}
				continue;
			}
			let vars = vars.ok_or_else(|| bad("a clause before the header"))?;
			for w in line.split_whitespace() {
				let lit: i32 = w.parse().map_err(|_| bad(format!("bad literal {w}")))?;
				if lit == 0 {
					clauses.push(canonical(std::mem::take(&mut clause)));
				} else if lit.unsigned_abs() > vars {
					return Err(bad(format!("literal {lit} of {vars} variables")));
				} else {
					clause.push(enc::code(lit));
				}
			}
		}
		if !clause.is_empty() {
			return Err(bad("the last clause has no terminating 0"));
		}
		if clauses.len() != declared {
			eprintln!("warning: {path}: the header says {declared} clauses, found {}", clauses.len());
		}
		Ok(Cnf { vars: vars.ok_or_else(|| bad("no header"))?, clauses })
	}

	pub fn write(&self, path: &str) -> io::Result<()> {
		let mut out = format!("p cnf {} {}\n", self.vars, self.clauses.len());
		for c in &self.clauses {
			for &code in c {
				out += &format!("{} ", enc::lit(code));
			}
			out += "0\n";
		}
		fs::write(path, out)
	}

	/// The levels of the Merkle tree over the clauses, leaves first.
	pub fn levels(&self) -> Vec<Vec<tree::Hash>> {
		tree::levels(self.clauses.iter().map(|c| tree::leaf(&enc::clause_bytes(c))).collect())
	}

	/// The params of a bounty for this formula's unsatisfiability.
	pub fn unsat(&self, levels: &[Vec<tree::Hash>]) -> Unsat {
		let root = levels.last().and_then(|l| l.first()).copied().unwrap_or([0; 32]);
		Unsat { vars: self.vars, clauses: self.clauses.len() as u32, root }
	}
}
