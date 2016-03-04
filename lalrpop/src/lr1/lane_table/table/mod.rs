//! The "Lane Table". In the paper, this is depicted like so:
//!
//! ```
//! +-------+----+-----+----+------------+
//! + State | C1 | ... | Cn | Successors |
//! +-------+----+-----+----+------------+
//! ```
//!
//! where each row summarizes some state that potentially contributes
//! lookahead to the conflict. The columns `Ci` represent each of the
//! conflicts we are trying to disentangle; their values are each
//! `TokenSet` indicating the lookahead contributing by this state.
//! The Successors is a vector of further successors. For simplicity
//! though we store this using maps, at least for now.

use collections::{Map, Multimap, Set};
use grammar::repr::*;
use lr1::core::*;
use lr1::lookahead::*;
use std::default::Default;
use std::fmt::{Debug, Error, Formatter};
use std::iter;

#[derive(Copy, Clone, Debug, PartialOrd, Ord, PartialEq, Eq)]
pub struct ConflictIndex {
    index: usize,
}

impl ConflictIndex {
    pub fn new(index: usize) -> ConflictIndex {
        ConflictIndex { index: index }
    }
}

pub struct LaneTable<'grammar> {
    grammar: &'grammar Grammar,
    conflicts: usize,
    lookaheads: Map<(StateIndex, ConflictIndex), TokenSet>,
    successors: Multimap<StateIndex, Set<StateIndex>>,
}

impl<'grammar> LaneTable<'grammar> {
    pub fn new(grammar: &'grammar Grammar, conflicts: usize) -> LaneTable {
        LaneTable {
            grammar: grammar,
            conflicts: conflicts,
            lookaheads: Map::default(),
            successors: Multimap::default(),
        }
    }

    pub fn add_lookahead(&mut self,
                         state: StateIndex,
                         conflict: ConflictIndex,
                         tokens: &TokenSet) {
        let grammar = self.grammar;
        self.lookaheads
            .entry((state, conflict))
            .or_insert_with(|| TokenSet::new(grammar))
            .insert_set(&tokens);
    }

    pub fn add_successor(&mut self, state: StateIndex, succ: StateIndex) {
        self.successors.push(state, succ);
    }
}

impl<'grammar> Debug for LaneTable<'grammar> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        let indices: Set<StateIndex> = self.lookaheads
                                           .keys()
                                           .map(|&(state, _)| state)
                                           .chain(self.successors
                                                      .iter()
                                                      .map(|(key, _)| key.clone()))
                                           .collect();

        let header = iter::once(format!("State"))
                         .chain((0..self.conflicts).map(|i| format!("C{}", i)))
                         .chain(Some(format!("Successors")))
                         .collect();

        let rows = indices.iter().map(|&index| {
            iter::once(format!("{:?}", index))
                .chain((0..self.conflicts).map(|i| {
                    self.lookaheads
                        .get(&(index, ConflictIndex::new(i)))
                        .map(|token_set| format!("{:?}", token_set.debug(self.grammar)))
                        .unwrap_or(String::new())
                }))
                .chain(Some(self.successors
                                .get(&index)
                                .map(|c| format!("{:?}", c))
                                .unwrap_or(String::new())))
                .collect()
        });

        let table: Vec<Vec<_>> = iter::once(header).chain(rows).collect();

        let columns = 2 + self.conflicts;

        let widths: Vec<_> = (0..columns)
                                 .map(|c| {
                                     // find the max width of any row at this column
                                     table.iter()
                                          .map(|r| r[c].len())
                                          .max()
                                          .unwrap()
                                 })
                                 .collect();

        for row in &table {
            try!(write!(fmt, "| "));
            for (i, column) in row.iter().enumerate() {
                if i > 0 {
                    try!(write!(fmt, " | "));
                }
                try!(write!(fmt, "{0:1$}", column, widths[i]));
            }
            try!(write!(fmt, " |\n"));
        }

        Ok(())
    }
}
