#![no_std]
#![no_main]

extern crate alloc;

use alloc::boxed::Box;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;
use core::fmt;
use core::ops;

use nexus_rt::{println, Write};

type Id = u32;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Polarity {
    Positive,
    Negative,
}

impl ops::Not for Polarity {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Self::Positive => Self::Negative,
            Self::Negative => Self::Positive,
        }
    }
}

impl Polarity {
    fn as_bool(self) -> bool {
        match self {
            Self::Positive => true,
            Self::Negative => false,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Purity {
    Pure(Polarity),
    Impure,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Clause {
    Literal(bool),
    Variable(Id, Polarity),
    Disjunction(Box<Clause>, Box<Clause>),
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Clause::*;
        use Polarity::*;
        match self {
            Literal(b) => write!(f, "{}", b),
            Variable(var, Positive) => write!(f, "{}", var),
            Variable(var, Negative) => write!(f, "!{}", var),
            Disjunction(lhs, rhs) => write!(f, "{} \\/ {}", lhs, rhs),
        }
    }
}

impl ops::Not for Clause {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Self::Variable(id, p) => Self::Variable(id, !p),
            _ => panic!("Illegal negation of {}", self),
        }
    }
}

impl ops::BitOr for Clause {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self::Disjunction(Box::new(self), Box::new(rhs))
    }
}

impl Clause {
    pub fn var(var: Id) -> Self {
        Self::Variable(var, Polarity::Positive)
    }

    pub fn parse(s: &str) -> Option<Self> {
        s.split(" \\/ ")
            .map(|term_str| {
                if let Some(var_str) = term_str.strip_prefix('!') {
                    !Self::var(var_str.parse::<Id>().unwrap())
                } else {
                    Self::var(term_str.parse::<Id>().unwrap())
                }
            })
            .reduce(|lhs, rhs| lhs | rhs)
    }

    pub fn is_true(&self) -> bool {
        matches!(self, Self::Literal(true))
    }

    pub fn is_false(&self) -> bool {
        matches!(self, Self::Literal(false))
    }

    // Choose an arbitrary variable to instantiate.
    pub fn choose_var(&self) -> Option<Id> {
        use Clause::*;
        match self {
            Literal(_) => None,
            Variable(var, _) => Some(*var),
            Disjunction(lhs, rhs) => lhs.choose_var().or_else(|| rhs.choose_var()),
        }
    }

    // If this clause a unit, return its variable name and polarity.
    pub fn get_unit(&self) -> Option<(Id, Polarity)> {
        use Clause::*;
        match self {
            Variable(var, p) => Some((*var, *p)),
            _ => None,
        }
    }

    // Check if `var` is "pure". `purity` tracks the purity seen so far.
    fn check_purity(&self, var: Id, purity: Option<Purity>) -> Option<Purity> {
        use Clause::*;
        use Purity::*;
        match self {
            Variable(var_, p) if *var_ == var => match purity {
                Some(Pure(p_)) if p_ == *p => Some(Pure(*p)),
                Some(_) => Some(Impure),
                None => Some(Pure(*p)),
            },
            Literal(_) | Variable(_, _) => purity,
            Disjunction(lhs, rhs) => {
                let lhs_polarity = lhs.check_purity(var, purity);
                rhs.check_purity(var, lhs_polarity)
            }
        }
    }

    // Check if `var` is "pure"; i.e., is it always used with the same polarity
    // everywhere in the clause.
    pub fn get_purity(&self, var: Id) -> Option<Purity> {
        self.check_purity(var, None)
    }

    // Collect all variable names.
    pub fn all_vars(&self) -> BTreeSet<Id> {
        use Clause::*;
        match self {
            Literal(_) => BTreeSet::new(),
            Variable(var, _) => BTreeSet::from([*var]),
            Disjunction(lhs, rhs) => lhs.all_vars().union(&rhs.all_vars()).copied().collect(),
        }
    }

    // Substitute `b` for `var`.
    pub fn subst(self, var: Id, b: bool) -> Self {
        use Clause::*;
        use Polarity::*;
        match self {
            Variable(var_, Positive) if var_ == var => Literal(b),
            Variable(var_, Negative) if var_ == var => Literal(!b),
            Disjunction(lhs, rhs) => {
                Disjunction(Box::new(lhs.subst(var, b)), Box::new(rhs.subst(var, b)))
            }
            Literal(_) | Variable(_, _) => self,
        }
    }

    // Simplify disjunctions by replacing `true \/ x` or `x \/ true` with
    // `true` and `false \/ x` or `x \/ false` with `x`.
    fn simplify_step(&mut self) -> bool {
        use Clause::*;
        match self {
            Literal(_) | Variable(_, _) => false,
            Disjunction(lhs, rhs) => {
                let did_simplify_lhs = lhs.simplify_step();
                let did_simplify_rhs = rhs.simplify_step();
                match (*lhs.clone(), *rhs.clone()) {
                    (Literal(true), _) | (_, Literal(true)) => {
                        *self = Literal(true);
                        true
                    }
                    (Literal(false), rhs) => {
                        *self = rhs;
                        true
                    }
                    (lhs, Literal(false)) => {
                        *self = lhs;
                        true
                    }
                    _ => did_simplify_lhs || did_simplify_rhs,
                }
            }
        }
    }

    // Repeatedly simplify until a fixed point is reached.
    pub fn simplify(mut self) -> Self {
        while self.simplify_step() {}
        self
    }
}

// #[test]
// fn test_subst() {
//     assert_eq!(Clause::var(0).subst(0, true), Clause::Literal(true));
//     assert_eq!(Clause::var(1).subst(0, true), Clause::var(1));
//     assert_eq!((!Clause::var(0)).subst(0, true), Clause::Literal(false));
//     assert_eq!(
//         (Clause::Literal(false) | !Clause::var(0)).subst(0, true),
//         Clause::Literal(false) | Clause::Literal(false)
//     );
// }

// #[test]
// fn test_simplify() {
//     assert_eq!(
//         (Clause::Literal(true) | Clause::Literal(false)).simplify(),
//         Clause::Literal(true)
//     );
//     assert_eq!(
//         (Clause::Literal(true) | !Clause::var(0)).simplify(),
//         Clause::Literal(true)
//     );
//     assert_eq!(
//         (Clause::var(1) | Clause::Literal(false)).simplify(),
//         Clause::var(1)
//     );
// }

#[allow(clippy::upper_case_acronyms)]
#[derive(Clone, Debug)]
struct CNF {
    clauses: Vec<Clause>,
    unassigned: BTreeSet<Id>,
    assigned: BTreeMap<Id, bool>,
}

impl fmt::Display for CNF {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (idx, clause) in self.clauses.iter().enumerate() {
            if idx > 0 {
                write!(f, " /\\ ")?;
            }
            write!(f, "({})", clause)?;
        }
        Ok(())
    }
}

impl CNF {
    pub fn new(clauses: Vec<Clause>) -> Self {
        let unassigned = clauses
            .iter()
            .map(|clause| clause.all_vars())
            .fold(BTreeSet::new(), |unassigned, vars| {
                unassigned.union(&vars).copied().collect()
            });
        (CNF {
            clauses,
            unassigned,
            assigned: BTreeMap::new(),
        })
        .simplify()
    }

    pub fn parse(s: &str) -> Option<Self> {
        let clauses: Vec<Clause> = s
            .split(" /\\ ")
            .map(Clause::parse)
            .collect::<Option<Vec<Clause>>>()?;
        Some(Self::new(clauses))
    }

    // Choose an arbitrary variable to instantiate.
    fn choose_var(&self) -> Id {
        self.clauses
            .iter()
            .find_map(|clause| clause.choose_var())
            .unwrap()
    }

    // Check if `var` is "pure"; i.e., is it always used with the same polarity
    // in every clause.
    fn get_purity(&self, var: Id) -> Option<Purity> {
        self.clauses
            .iter()
            .map(|clause| clause.get_purity(var))
            .fold(None, |polarity_acc, polarity| {
                if polarity_acc == polarity {
                    polarity_acc
                } else {
                    Some(Purity::Impure)
                }
            })
    }

    // Substitute `b` for `var` in every clause and update the assigned and
    // unassigned variables.
    pub fn subst(self, var: Id, b: bool) -> Self {
        let mut assigned = self.assigned;
        assert!(assigned.insert(var, b).is_none());
        let mut unassigned = self.unassigned;
        assert!(unassigned.remove(&var));
        Self {
            clauses: self
                .clauses
                .into_iter()
                .map(|clause| clause.subst(var, b))
                .collect(),
            unassigned,
            assigned,
        }
    }

    // Simplify every clause and drop satisfied ones.
    fn simplify(self) -> Self {
        Self {
            clauses: self
                .clauses
                .into_iter()
                .map(|clause| clause.simplify())
                .filter(|clause| !clause.is_true())
                .collect(),
            unassigned: self.unassigned,
            assigned: self.assigned,
        }
    }

    // Ref: https://en.wikipedia.org/wiki/DPLL_algorithm
    pub fn find_sat(self) -> Option<BTreeMap<Id, bool>> {
        let mut cnf = self;
        // Eliminate unit clauses.
        while let Some((var, polarity)) = cnf.clauses.iter().find_map(|clause| clause.get_unit()) {
            cnf = cnf.subst(var, polarity.as_bool()).simplify();
        }
        // Eliminate pure clauses.
        while let Some((var, polarity)) =
            cnf.unassigned
                .iter()
                .find_map(|var| match cnf.get_purity(*var) {
                    Some(Purity::Pure(p)) => Some((*var, p)),
                    Some(Purity::Impure) | None => None,
                })
        {
            cnf = cnf.subst(var, polarity.as_bool());
        }
        // Have all the clauses been satisfied?
        if cnf.clauses.is_empty() {
            return Some(cnf.assigned);
        }
        // Are any clauses unsatisfiable?
        if cnf.clauses.iter().any(|clause| clause.is_false()) {
            return None;
        }
        // Pick a variable and try assigning it.
        let var = cnf.choose_var();
        let cnf_true = cnf.clone().subst(var, true).simplify();
        let cnf_false = cnf.subst(var, false).simplify();
        cnf_true.find_sat().or_else(|| cnf_false.find_sat())
    }
}

// #[test]
// fn test_sat() {
//     let tests = [
//         r#"0"#,
//         r#"0 \/ 1"#,
//         r#"0 /\ 1"#,
//         r#"0 \/ !1 /\ 1"#,
//         r#"0 \/ !1 /\ !1 \/ !0"#,
//     ];
//     for clauses in tests {
//         assert!(CNF::parse(clauses).unwrap().find_sat().is_some());
//     }
// }

// #[test]
// fn test_unsat() {
//     let tests = [r#"0 /\ !0"#, r#"0 \/ !1 \/ 2 /\ 1 \/ 0 /\ !2 /\ !0"#];
//     for clauses in tests {
//         assert!(CNF::parse(clauses).unwrap().find_sat().is_none());
//     }
// }

#[nexus_rt::main]
fn main() {
    // Most tests are commented out to speed up proving.
    let sat_tests = [
        // r#"0"#,
        r#"0 \/ 1"#,
        // r#"0 /\ 1"#,
        // r#"0 \/ !1 /\ 1"#,
        // r#"0 \/ !1 /\ !1 \/ !0"#,
        // r#"!4 /\ 2 \/ 3 /\ !0 \/ 1 /\ 3 /\ 2"#,
        // r#"6 \/ 1 /\ !5 \/ !0 /\ !0 /\ !4 \/ !6 /\ 4 /\ 5 /\ !0 \/ 2 /\ 5 /\ 5 \/ 0"#,
    ];
    let unsat_tests = [
        r"0 /\ !0",
        // r#"0 \/ !1 \/ 2 /\ 1 \/ 0 /\ !2 /\ !0"#,
        // r#"!1 /\ 5 \/ 0 /\ !2 /\ 5 \/ !2 \/ 1 /\ 3 \/ 5 /\ 7 /\ 7 \/ !2 /\ !0 /\ 5 \/ !3 \/ !3 /\ 2 /\ !2"#,
        // r#"5 /\ !5 /\ 0 \/ 4 /\ 0 /\ 5 \/ 1 /\ !6 \/ 7"#,
    ];
    for test in sat_tests.iter().chain(unsat_tests.iter()) {
        let cnf = CNF::parse(test).unwrap();
        if let Some(assignments) = cnf.find_sat() {
            println!("{}: {:?}", test, assignments);
        } else {
            println!("{}: unsat", test);
        }
    }
}
