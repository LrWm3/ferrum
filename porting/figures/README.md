# Performance figure

`prusti-client-wall.png` and `.svg` plot the audited direct Prusti report at one
worker with branch parallelism off. Dots are medians, whiskers are observed
minimum–maximum values across three paired blocks. A later-service observation
is the mean of two requests within a block. Whiskers are not confidence intervals.

Render from the repository root, outside any benchmark timing interval:

```sh
python3 -m venv /tmp/ferrum-plot-venv
/tmp/ferrum-plot-venv/bin/pip install matplotlib==3.9.4 numpy==2.1.3
/tmp/ferrum-plot-venv/bin/python tools/performance/plot_prusti.py
```

`--input` selects another compatible audited report; `--output-dir` selects the
destination. The default input is `porting/performance-prusti.json`. The renderer
checks the audit status and three-sample groups and writes the PNG, SVG and
`prusti-client-wall.json` with input, script and output hashes plus Python,
Matplotlib and NumPy versions. SVG identifiers and metadata are deterministic;
font/platform differences can still affect output. The committed PNG was visually
reviewed for labels, legend, ranges and footnote readability.
