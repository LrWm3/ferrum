//! Collection helpers.
//!
//! Port of [`package.scala`](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/common/src/main/scala/collections/package.scala).
//! Status: implemented; integration with callers remains pending.
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

/// Cartesian product in outer-to-inner iteration order.
pub fn cross_product<T: Clone>(
    sequences: impl IntoIterator<Item = impl IntoIterator<Item = T>>,
) -> Vec<Vec<T>> {
    sequences
        .into_iter()
        .fold(vec![Vec::new()], |prefixes, values| {
            let values: Vec<T> = values.into_iter().collect();
            prefixes
                .into_iter()
                .flat_map(|prefix| {
                    values.iter().map(move |value| {
                        let mut next = prefix.clone();
                        next.push(value.clone());
                        next
                    })
                })
                .collect()
        })
}
