//! Core LR(1) types.

use collections::Map;
use grammar::repr::*;
use std::fmt::{Debug, Display, Formatter, Error};
use std::rc::Rc;
use util::Prefix;

use super::lookahead::*;

#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Item<'grammar, L: Lookahead> {
    pub production: &'grammar Production,
    /// the dot comes before `index`, so `index` would be 1 for X = A (*) B C
    pub index: usize,
    pub lookahead: L,
}

pub type LR0Item<'grammar> = Item<'grammar, Nil>;

pub type LR1Item<'grammar> = Item<'grammar, Token>;

impl<'grammar> Item<'grammar, Nil> {
    pub fn lr0(production: &'grammar Production,
               index: usize)
               -> Self {
        Item { production: production, index: index, lookahead: Nil }
    }
}

impl<'grammar, L: Lookahead> Item<'grammar, L> {
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
        Item { production: self.production, index: self.index, lookahead: Nil }
    }

    pub fn can_shift(&self) -> bool {
        self.index < self.production.symbols.len()
    }

    pub fn can_shift_nonterminal(&self, nt: NonterminalString) -> bool {
        match self.shift_symbol() {
            Some((Symbol::Nonterminal(shifted), _)) => shifted == nt,
            _ => false,
        }
    }

    pub fn can_shift_terminal(&self, term: TerminalString) -> bool {
        match self.shift_symbol() {
            Some((Symbol::Terminal(shifted), _)) => shifted == term,
            _ => false,
        }
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
pub struct Items<'grammar, L: Lookahead> {
    pub vec: Rc<Vec<Item<'grammar, L>>>
}

pub type LR0Items<'grammar> = Items<'grammar, Nil>;
pub type LR1Items<'grammar> = Items<'grammar, Token>;

#[derive(Debug)]
pub struct State<'grammar, L: Lookahead> {
    pub index: StateIndex,
    pub items: Items<'grammar, L>,
    pub shifts: Map<TerminalString, StateIndex>,
    pub reductions: Map<L, &'grammar Production>,
    pub conflicts: Vec<Conflict<'grammar, L>>,
    pub gotos: Map<NonterminalString, StateIndex>,
}

pub type LR0State<'grammar> = State<'grammar, Nil>;
pub type LR1State<'grammar> = State<'grammar, Token>;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Action<'grammar> {
    Shift(TerminalString, StateIndex),
    Reduce(&'grammar Production),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Conflict<'grammar, L: Lookahead> {
    // when in this state...
    pub state: StateIndex,

    // with the following lookahead...
    pub lookahead: L,

    // we can reduce...
    pub production: &'grammar Production,

    // but we can also...
    pub action: Action<'grammar>,
}

pub type LR0Conflict<'grammar> = Conflict<'grammar, Nil>;
pub type LR1Conflict<'grammar> = Conflict<'grammar, Token>;

#[derive(Debug)]
pub struct TableConstructionError<'grammar, L: Lookahead> {
    // LR(1) state set. Some of these states are in error.
    pub states: Vec<State<'grammar, L>>,
}

pub type LR0TableConstructionError<'grammar> = TableConstructionError<'grammar, Nil>;
pub type LR1TableConstructionError<'grammar> = TableConstructionError<'grammar, Token>;

impl<'grammar, L: Lookahead> Debug for Item<'grammar, L> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        try!(write!(fmt, "{} ={} (*){}",
                    self.production.nonterminal,
                    Prefix(" ", &self.production.symbols[..self.index]),
                    Prefix(" ", &self.production.symbols[self.index..])));

        self.lookahead.fmt_as_item_suffix(fmt)
    }
}

impl Display for Token {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        match *self {
            Token::EOF => write!(fmt, "EOF"),
            Token::Terminal(s) => write!(fmt, "{}", s),
        }
    }
}

impl Debug for Token {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        write!(fmt, "{}", self)
    }
}

impl Debug for StateIndex {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        write!(fmt, "S{}", self.0)
    }
}

impl<'grammar, L: Lookahead> State<'grammar, L> {
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
