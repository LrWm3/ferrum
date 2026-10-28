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
//! Status: local-time formatting and Java Formatter's half-up floating-point rounding implemented;
//! chrono reports unsupported timestamps rather than fabricating local-time fields.

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
        let seconds = millis as f32 / 1000.0;
        // Formatter rounds the binary float half away from zero. Below 2^23 the f32
        // value times 100 is exactly representable in f64, so the integer rounding
        // avoids Rust's ties-to-even formatter without changing the f32 division.
        if seconds.abs() < 8_388_608.0 {
            let cents = ((seconds as f64) * 100.0).round() as i64;
            let sign = if seconds.is_sign_negative() { "-" } else { "" };
            let magnitude = cents.unsigned_abs();
            return Ok(format!("{sign}{}.{:02}s", magnitude / 100, magnitude % 100));
        }
        // At this magnitude an f32 has no fractional bits, so no tie is possible.
        return Ok(format!("{seconds:.2}s"));
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

#[cfg(test)]
mod tests {
    use super::format_millis_readably;
    #[test]
    fn java_formatter_rounds_f32_ties_away_from_zero() {
        for (millis, expected) in [
            (125, "0.13s"),
            (375, "0.38s"),
            (1015, "1.01s"),
            (1025, "1.02s"),
            (1125, "1.13s"),
            (-1, "-0.00s"),
            (-125, "-0.13s"),
            (-375, "-0.38s"),
            (-1015, "-1.01s"),
            (-1025, "-1.02s"),
            (-1125, "-1.13s"),
            (-8_388_608_000, "-8388608.00s"),
            (i64::MIN, "-9223372474941440.00s"),
        ] {
            assert_eq!(
                format_millis_readably(millis).unwrap(),
                expected,
                "{millis}"
            );
        }
    }
}
