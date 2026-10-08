use crate::{Clauseish, Literal, SATState};

mod paint {
    use alloc::string::String;
    use core::fmt::Display;

    #[derive(Clone, Copy)]
    pub enum State {
        Satisfied,
        Unit,
        Contradictory,
        Plain,
    }

    #[cfg(feature = "pretty")]
    mod inner {
        use super::State;
        use colored::Colorize;
        use core::fmt::Display;

        pub fn sat(v: impl Display) -> String {
            v.to_string().bold().green().to_string()
        }
        pub fn unsat(v: impl Display) -> String {
            v.to_string().bold().red().to_string()
        }
        pub fn bold(v: impl Display) -> String {
            v.to_string().bold().to_string()
        }
        pub fn state(v: &str, state: State) -> String {
            let color = match state {
                State::Satisfied => colored::Color::Green,
                State::Unit => colored::Color::Yellow,
                State::Contradictory => colored::Color::Red,
                State::Plain => colored::Color::White,
            };
            v.color(color).to_string()
        }
    }

    #[cfg(not(feature = "pretty"))]
    mod inner {
        use super::State;
        use alloc::string::{String, ToString};
        use core::fmt::Display;

        pub fn sat(v: impl Display) -> String {
            v.to_string()
        }
        pub fn unsat(v: impl Display) -> String {
            v.to_string()
        }
        pub fn bold(v: impl Display) -> String {
            v.to_string()
        }
        pub fn state(v: &str, _state: State) -> String {
            v.to_string()
        }
    }

    pub fn sat(v: impl Display) -> String {
        inner::sat(v)
    }
    pub fn unsat(v: impl Display) -> String {
        inner::unsat(v)
    }
    pub fn bold(v: impl Display) -> String {
        inner::bold(v)
    }
    pub fn state(v: &str, state: State) -> String {
        inner::state(v, state)
    }
}

impl core::fmt::Debug for SATState {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "SATState ")?;

        for contra in self.solos.forced_contradictions.iter().take(20) {
            write!(f, "X{contra:?} ")?;
        }
        if self.solos.forced_contradictions.len() > 20 {
            write!(f, "... ")?;
        }

        for literal in self.solos.forced_assignments.iter().take(20) {
            if self.assignments[literal.var_index()].is_none() {
                write!(f, "{literal:?} ")?;
            } else if literal.matching(self.assignments[literal.var_index()].unwrap()) {
                write!(f, "{} ", paint::sat(format_args!("{literal:?}")))?;
            } else {
                write!(f, "{} ", paint::unsat(format_args!("{literal:?}")))?;
            }
        }
        if self.solos.forced_assignments.len() > 20 {
            write!(f, "... ")?;
        }

        write!(f, "[")?;

        for clause in self.iter_all_clauses().take(20) {
            let satisfied = clause.satisfying_count() > 0;
            let state = if satisfied {
                paint::State::Satisfied
            } else if clause.unassigned_count() == 1 {
                paint::State::Unit
            } else if clause.definitely_contradictory() {
                paint::State::Contradictory
            } else {
                paint::State::Plain
            };
            write!(f, " {}", paint::state("(", state))?;
            let mut first = true;
            for (i, lit) in clause.dyn_iter_all().enumerate() {
                if !first {
                    write!(f, " {} ", paint::state("|", state))?;
                }
                first = false;
                if clause.is_unassigned(i) {
                    write!(f, "{lit:?}?")?;
                } else if let Some(satisfying) = clause.is_satisfying(i) {
                    if satisfying {
                        write!(f, "{}", paint::sat(format_args!("{lit:?}")))?;
                    } else {
                        write!(f, "{}", paint::unsat(format_args!("{lit:?}")))?;
                    }
                } else {
                    write!(f, "{}", paint::bold(format_args!("{lit:?}")))?;
                }
            }
            write!(f, "{}", paint::state(")", state))?;
        }
        if self.iter_all_clauses().count() > 20 {
            write!(f, " ...")?;
        }

        for implier in 0..self.duals.implication_graph.len().min(20) {
            let implier_lit = Literal(implier as u32);
            if self.duals.implication_graph[implier].is_empty() {
                continue;
            }
            write!(f, " {:?} -> [", implier_lit)?;
            for &implied in &self.duals.implication_graph[implier] {
                write!(f, " {implied:?}")?;
            }
            write!(f, " ]")?;
        }

        if self.duals.implication_graph.len() > 20 {
            write!(f, " ...")?;
        }

        write!(f, " ][")?;
        for (i, &assignment) in self.assignments.iter().enumerate().take(80) {
            if i > 0 {
                write!(f, ", ")?;
            }
            match assignment {
                Some(true) => write!(f, "{}", paint::sat(format_args!("{i}")))?,
                Some(false) => write!(f, "¬{}", paint::unsat(format_args!("{i}")))?,
                None => write!(f, "{i}?")?,
            }
        }
        if self.assignments.len() > 80 {
            write!(f, ", ...")?;
        }
        write!(f, "]")
    }
}
