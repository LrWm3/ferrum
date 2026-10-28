//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/renderer/Renderer.scala
//!
//! Purpose:
//! Define rendering of member logs and collections.
//!
//! Planned Rust structure:
//! Port Renderer renderMember and render interface.
//!
//! Behavior to preserve:
//! Keep renderer result generic and preserve input member order.
//!
//! Integration:
//! logger::renderer::simple_tree_renderer and logger::symb_ex_logger.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for owned log views.
//!
//! Open decisions:
//! Agree on renderer input/output lifetimes with logger.
//!
//! Status: native member/list renderer contract implemented.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

pub trait Renderer<S: ?Sized> {
    type Output;
    type Error;
    fn render_member(&self, member: &S) -> Result<Self::Output, Self::Error>;
    fn render(&self, members: &[&S]) -> Result<Self::Output, Self::Error>;
}
