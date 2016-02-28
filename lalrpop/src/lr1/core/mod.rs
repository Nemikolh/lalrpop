//! Core LR(1) types.

use collections::Map;
use grammar::repr::*;
use std::fmt::{Debug, Formatter, Error};
use std::rc::Rc;
use util::Prefix;

use super::lookahead::Lookahead;

#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Item<'grammar, L: Clone> {
    pub production: &'grammar Production,
    /// the dot comes before `index`, so `index` would be 1 for X = A (*) B C
    pub index: usize,
    pub lookahead: L,
}

pub type LR0Item<'grammar> = Item<'grammar, ()>;

pub type LR1Item<'grammar> = Item<'grammar, Lookahead>;

impl<'grammar> Item<'grammar, ()> {
    #[cfg(test)]
    pub fn lr0(production: &'grammar Production,
               index: usize)
               -> Self {
        Item { production: production, index: index, lookahead: () }
    }
}

impl<'grammar, L: Clone> Item<'grammar, L> {
    pub fn prefix(&self) -> &'grammar [Symbol] {
        &self.production.symbols[..self.index]
    }

    pub fn symbol_sets(&self) -> SymbolSets<'grammar> {
        let symbols = &self.production.symbols;
        if self.can_shift() {
            SymbolSets {
                prefix: &symbols[..self.index],
                cursor: Some(&symbols[self.index]),
                suffix: &symbols[self.index+1..],
            }
        } else {
            SymbolSets {
                prefix: &symbols[..self.index],
                cursor: None,
                suffix: &[],
            }
        }
    }

    pub fn to_lr0(&self) -> LR0Item<'grammar> {
        Item { production: self.production, index: self.index, lookahead: () }
    }

    pub fn can_shift(&self) -> bool {
        self.index < self.production.symbols.len()
    }

    pub fn can_reduce(&self) -> bool {
        self.index == self.production.symbols.len()
    }

    pub fn shifted_item(&self) -> Option<(Symbol, Item<'grammar, L>)> {
        if self.can_shift() {
            Some((self.production.symbols[self.index],
                  Item { production: self.production,
                         index: self.index + 1,
                         lookahead: self.lookahead.clone() }))
        } else {
            None
        }
    }

    pub fn shift_symbol(&self) -> Option<(Symbol, &[Symbol])> {
        if self.can_shift() {
            Some((self.production.symbols[self.index], &self.production.symbols[self.index+1..]))
        } else {
            None
        }
    }
}

#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct StateIndex(pub usize);

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Items<'grammar, L: Clone> {
    pub vec: Rc<Vec<Item<'grammar, L>>>
}

pub type LR0Items<'grammar> = Items<'grammar, ()>;
pub type LR1Items<'grammar> = Items<'grammar, Lookahead>;

#[derive(Debug)]
pub struct State<'grammar, L: Clone> {
    pub index: StateIndex,
    pub items: Items<'grammar, L>,
    pub tokens: Map<Lookahead, Action<'grammar>>,
    pub conflicts: Map<Lookahead, Vec<Conflict<'grammar>>>,
    pub gotos: Map<NonterminalString, StateIndex>,
}

pub type LR0State<'grammar> = State<'grammar, ()>;
pub type LR1State<'grammar> = State<'grammar, Lookahead>;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Action<'grammar> {
    Shift(StateIndex),
    Reduce(&'grammar Production),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Conflict<'grammar> {
    // when in this state...
    pub state: StateIndex,

    // we can reduce...
    pub production: &'grammar Production,

    // but we can also...
    pub action: Action<'grammar>,
}

#[derive(Debug)]
pub struct TableConstructionError<'grammar> {
    // LR(1) state set. Some of these states are in error.
    pub states: Vec<LR1State<'grammar>>,
}

impl<'grammar, L: Clone+Debug> Debug for Item<'grammar, L> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        let mut lookahead_debug = format!("{:?}", self.lookahead);
        if lookahead_debug != "()" {
            lookahead_debug = format!(" [{}]", lookahead_debug);
        } else {
            lookahead_debug = format!("");
        }

        write!(fmt, "{} ={} (*){}{}",
               self.production.nonterminal,
               Prefix(" ", &self.production.symbols[..self.index]),
               Prefix(" ", &self.production.symbols[self.index..]),
               lookahead_debug)
    }
}

impl Debug for Lookahead {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        match *self {
            Lookahead::EOF => write!(fmt, "EOF"),
            Lookahead::Terminal(s) => write!(fmt, "{}", s),
        }
    }
}

impl Debug for StateIndex {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        write!(fmt, "S{}", self.0)
    }
}

impl<'grammar, L: Clone> State<'grammar, L> {
    pub fn prefix(&self) -> &'grammar [Symbol] {
        // Each state fn takes as argument the longest prefix of any
        // item. Note that all items must have compatible prefixes.
        let (_, prefix) =
            self.items.vec
                      .iter()
                      .map(|item| &item.production.symbols[..item.index])
                      .map(|symbols| (symbols.len(), symbols))
                      .max() // grr, max_by is unstable :(
                      .unwrap();

        debug_assert!(
            self.items.vec
                      .iter()
                      .all(|item| prefix.ends_with(&item.production.symbols[..item.index])));

        prefix
    }
}

impl<'grammar> Action<'grammar> {
    pub fn shift(&self) -> Option<StateIndex> {
        match *self {
            Action::Shift(next_index) => Some(next_index),
            _ => None
        }
    }
    pub fn reduce(&self) -> Option<&'grammar Production> {
        match *self {
            Action::Reduce(production) => Some(production),
            _ => None,
        }
    }
}

/// `A = B C (*) D E F` or `A = B C (*)`
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SymbolSets<'grammar> {
    pub prefix: &'grammar [Symbol], // both cases, [B, C]
    pub cursor: Option<&'grammar Symbol>, // first [D], second []
    pub suffix: &'grammar [Symbol], // first [E, F], second []
}

impl<'grammar> SymbolSets<'grammar> {
    pub fn new() -> Self {
        SymbolSets {
            prefix: &[],
            cursor: None,
            suffix: &[],
        }
    }
}
