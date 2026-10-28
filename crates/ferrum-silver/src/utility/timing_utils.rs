//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/utility/TimingUtils.scala
//!
//! Purpose:
//! Format and measure elapsed milliseconds.
//!
//! Planned Rust structure:
//! Port TimingUtils formatTimeForTable, formatTime and time closure helper.
//!
//! Behavior to preserve:
//! Use seconds with two decimals only when millis > 1000; otherwise milliseconds, including table
//! widths and suffix spacing. Return closure result with elapsed milliseconds.
//!
//! Integration:
//! Frontend and reporting timing callers.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Choose clock abstraction with frontend timing while preserving observable formatting.
//!
//! Status: implemented; not yet wired or validated.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use std::time::{SystemTime, UNIX_EPOCH};

pub fn format_time_for_table(millis: i64) -> String {
    if millis > 1000 {
        format!("{:6.2} sec ", millis as f64 / 1000.0)
    } else {
        format!("{millis:>6} msec")
    }
}

pub fn format_time(millis: i64) -> String {
    if millis > 1000 {
        format!("{:.2} sec", millis as f64 / 1000.0)
    } else {
        format!("{millis} msec")
    }
}

fn current_millis() -> i64 {
    match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(d) => d.as_millis() as i64,
        Err(e) => -(e.duration().as_millis() as i64),
    }
}

pub fn time<T>(f: impl FnOnce() -> T) -> (T, i64) {
    let start = current_millis();
    let result = f();
    (result, current_millis() - start)
}
