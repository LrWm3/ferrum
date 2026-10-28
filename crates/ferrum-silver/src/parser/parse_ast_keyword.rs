//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/parser/ParseAstKeyword.scala
//!
//! Purpose:
//! Represent source tokens, delimiters and operator typing and formatting rules.
//!
//! Planned Rust structure:
//! Port PReserved, PGrouped, PDelimited, ND, PKw, PSym, PSymOp, PKwOp and operator signature
//! categories. Retain grouping/delimiter helpers, update and implied constructors.
//!
//! Behavior to preserve:
//! Keep position-independent PDelimited equality/hash, delimiter order and update length
//! assertion. Preserve each token spelling, formatting pads and ordered overload signatures,
//! including integer versus permission division and collection membership return types.
//!
//! Integration:
//! parser::parse_ast, fast_parser, resolver and reformat_pretty_printer; utility::common hash
//! helper.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors, source positions and collection
//! semantics; parser and node representations are provisional.
//!
//! Open decisions:
//! Choose token and generic grouping representation consistent with parser and formatter without
//! changing signatures.
//!
//! Status: description only; implementation has not started.
