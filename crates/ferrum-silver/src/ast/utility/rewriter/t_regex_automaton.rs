//! Tree-regex state machine and transition actions.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/rewriter/TRegexAutomaton.scala
//! Status: implemented generic state machine; regex strategy integration remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use std::collections::HashSet;
use std::sync::Arc;
pub type StateId = usize;
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TransitionInfo<N, C> {
    ChildSelect(N),
    MarkedForRewrite,
    Context(C),
}
pub type Predicate<N> = Arc<dyn Fn(&N) -> bool + Send + Sync>;
pub type Actions<N, C> = Arc<dyn Fn(&N) -> Vec<TransitionInfo<N, C>> + Send + Sync>;
#[derive(Clone)]
pub struct Matcher<N, C> {
    pub predicate: Predicate<N>,
    pub actions: Actions<N, C>,
}
struct State<N, C> {
    matching: Option<(StateId, Matcher<N, C>)>,
    epsilon: Vec<StateId>,
    effective_cache: HashSet<StateId>,
}
impl<N, C> Default for State<N, C> {
    fn default() -> Self {
        Self {
            matching: None,
            epsilon: Vec::new(),
            effective_cache: HashSet::new(),
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TRegexAutomaton {
    pub start: StateId,
    pub end: StateId,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AutomatonError {
    InvalidState,
    InputOnEpsilonState,
}
pub struct Automaton<N, C> {
    states: Vec<State<N, C>>,
}
impl<N, C> Default for Automaton<N, C> {
    fn default() -> Self {
        Self { states: Vec::new() }
    }
}
impl<N, C> Automaton<N, C> {
    pub fn new_state(&mut self) -> StateId {
        let id = self.states.len();
        self.states.push(State::default());
        id
    }
    pub fn set_match(
        &mut self,
        from: StateId,
        to: StateId,
        matcher: Matcher<N, C>,
    ) -> Result<(), AutomatonError> {
        if to >= self.states.len() {
            return Err(AutomatonError::InvalidState);
        }
        self.states
            .get_mut(from)
            .ok_or(AutomatonError::InvalidState)?
            .matching = Some((to, matcher));
        Ok(())
    }
    pub fn add_epsilon(&mut self, from: StateId, to: StateId) -> Result<(), AutomatonError> {
        if to >= self.states.len() {
            return Err(AutomatonError::InvalidState);
        }
        let state = self
            .states
            .get_mut(from)
            .ok_or(AutomatonError::InvalidState)?;
        state.epsilon.push(to);
        state.effective_cache.clear();
        Ok(())
    }
    pub fn is_accepting(&self, id: StateId) -> Result<bool, AutomatonError> {
        let s = self.states.get(id).ok_or(AutomatonError::InvalidState)?;
        Ok(s.epsilon.is_empty() && s.matching.is_none())
    }
    pub fn is_epsilon(&self, id: StateId) -> Result<bool, AutomatonError> {
        let s = self.states.get(id).ok_or(AutomatonError::InvalidState)?;
        Ok(s.matching.is_none() && !self.is_accepting(id)?)
    }
    pub fn valid_input(&self, id: StateId, node: &N) -> Result<bool, AutomatonError> {
        Ok(self
            .states
            .get(id)
            .ok_or(AutomatonError::InvalidState)?
            .matching
            .as_ref()
            .is_some_and(|(_, m)| (m.predicate)(node)))
    }
    pub fn effective(&mut self, id: StateId) -> Result<HashSet<StateId>, AutomatonError> {
        if id >= self.states.len() {
            return Err(AutomatonError::InvalidState);
        }
        if !self.states[id].effective_cache.is_empty() {
            return Ok(self.states[id].effective_cache.clone());
        }
        fn collect<N, C>(
            machine: &Automaton<N, C>,
            id: StateId,
            mut seen: HashSet<StateId>,
        ) -> HashSet<StateId> {
            if !seen.insert(id) {
                return seen;
            }
            let state = &machine.states[id];
            if state.epsilon.is_empty() {
                return seen;
            }
            state
                .epsilon
                .iter()
                .map(|target| collect(machine, *target, seen.clone()))
                .fold(HashSet::new(), |mut a, b| {
                    a.extend(b);
                    a
                })
        }
        let result = collect(self, id, HashSet::new())
            .into_iter()
            .filter(|s| !self.is_epsilon(*s).expect("known state"))
            .collect::<HashSet<_>>();
        self.states[id].effective_cache = result.clone();
        Ok(result)
    }
    pub fn transition(
        &mut self,
        id: StateId,
        node: &N,
    ) -> Result<(HashSet<StateId>, Vec<TransitionInfo<N, C>>), AutomatonError> {
        let (target, matcher) = self
            .states
            .get(id)
            .ok_or(AutomatonError::InvalidState)?
            .matching
            .as_ref()
            .ok_or(AutomatonError::InputOnEpsilonState)?;
        if !(matcher.predicate)(node) {
            return Ok((HashSet::new(), Vec::new()));
        }
        let target = *target;
        let actions = (matcher.actions)(node);
        Ok((self.effective(target)?, actions))
    }
}
