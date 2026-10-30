# Selected stdlib Viper inputs

These are byte-preserved copies of fresh, matching native/JVM Prusti dumps at
integration build pin `a59ed917c` and Ferrum runtime `afdf10c`. `oracles.json`
records the exact outcomes, diagnostic positions, hashes and original paths.
Generated trailing spaces are preserved; the local Git attributes prevent text
normalization or whitespace corrections from changing the measured bytes.
Resolve its relative file paths when creating a frozen run manifest. The first
three cases verify; `mut_element_array_wrong` must fail with the listed exhale
error. The corresponding Rust source revision, file paths and calibration
provenance are recorded in the origin entries and performance validation report.

The input set was selected before timing. It is a four-workload sample, not the
full Rust stdlib matrix. These files contain no import/include tokens and the
preserved copies passed both parsed backend oracles and all 96 worker/branch/
session configuration gates. Their checked hashes must remain fixed during any
comparison. Existing build artifacts and configurations still need independent
provenance; these inputs alone do not establish a fair performance experiment.
