use collections::{Set, set};
use lr1::core::*;
use lr1::first::FirstSets;
use lr1::state_graph::StateGraph;
use grammar::repr::*;

mod reduce;
mod shift;
mod trace_graph;

pub struct Tracer<'trace, 'grammar: 'trace> {
    grammar: &'trace Grammar,
    states: &'trace [LR1State<'grammar>],
    first_sets: &'trace FirstSets,
    state_graph: StateGraph,
    trace_graph: TraceGraph<'grammar>,
    visited_set: Set<(StateIndex, NonterminalString)>,
}

impl<'trace, 'grammar> Tracer<'trace, 'grammar> {
    pub fn new(grammar: &'grammar Grammar,
               first_sets: &'trace FirstSets,
               states: &'trace [LR1State<'grammar>])
               -> Self {
        Tracer {
            grammar: grammar,
            states: states,
            first_sets: first_sets,
            state_graph: StateGraph::new(states),
            trace_graph: TraceGraph::new(),
            visited_set: set(),
        }
    }
}

pub use self::trace_graph::TraceGraph;
