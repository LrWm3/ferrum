//! Port plan: Format elapsed milliseconds for human-readable reports.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/reporter/format/package.scala
//!
//! Purpose:
//! Format elapsed milliseconds for human-readable reports.
//!
//! Planned Rust structure:
//! formatMillisReadably and minute/hour thresholds.
//!
//! Behavior to preserve:
//! Below one minute output seconds to two decimals; below one hour output minute/second fields; at
//! least one hour output hours and residual minute/second fields. Preserve Java formatting
//! behavior at boundaries.
//!
//! Integration:
//! reporter::reporter and other reporting clients.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, lifecycle, error handling and provisional
//! ownership; retain observable source behavior.
//!
//! Open decisions:
//! Check Rust formatting and rounding against JVM edge cases before selecting time representation.
//!
//! Status: partial; local-time formatting implemented. Floating-point rounding and chrono
//! timestamp limits may differ from the JVM on exceptional inputs.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use chrono::{Local, TimeZone, Timelike};

/// Java formats the epoch timestamp in the default local timezone for the minute and
/// second fields. Chrono has a smaller supported timestamp range than Java `Date`;
/// such out-of-range values are returned as an error rather than misformatted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TimestampOutOfRange(pub i64);

pub fn format_millis_readably(millis: i64) -> Result<String, TimestampOutOfRange> {
    const MINUTE: i64 = 60_000;
    const HOUR: i64 = 3_600_000;
    if millis < MINUTE {
        return Ok(format!("{:.2}s", millis as f32 / 1000.0));
    }
    let timestamp = if millis < HOUR { millis } else { millis % HOUR };
    let date = Local
        .timestamp_millis_opt(timestamp)
        .single()
        .ok_or(TimestampOutOfRange(timestamp))?;
    let fields = format!("{:02}m:{:02}s", date.minute(), date.second());
    if millis < HOUR {
        Ok(fields)
    } else {
        Ok(format!("{}h:{fields}", millis / HOUR))
    }
}
