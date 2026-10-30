#!/usr/bin/env python3
"""Plot audited direct-Prusti wall results and write figure provenance."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DEFAULT = ROOT / 'porting/performance-prusti.json'
CASES = [('observation_pass', 'Observation\npass'), ('mut_element_array_pass', 'Array\npass'), ('mut_element_option_pass', 'Option\npass'), ('mut_element_array_wrong', 'Array\nwrong')]

def load(path):
    data = json.loads(path.read_text())
    if not data['analysis']['primary_valid'] or data['analysis']['integrity_errors']:
        raise ValueError('Input report did not pass its independent integrity audit')
    groups = data['analysis']['groups']
    values = {}
    for mode in ('fresh', 'service_later_mean'):
        for backend in ('native', 'jvm'):
            for case, _ in CASES:
                matching = [g for g in groups if g['case'] == case and g['mode'] == mode and g['backend'] == backend and g['workers'] == 1 and g['parallel_branches'] is False]
                if len(matching) != 1:
                    raise ValueError(f'Expected one group for {mode}, {backend}, {case}')
                metric = matching[0]['metrics']['wall_s']
                if metric['count'] != 3 or len(metric['values']) != 3 or not metric['min'] <= metric['median'] <= metric['max']:
                    raise ValueError(f'Incomplete or malformed observations: {mode}, {backend}, {case}')
                values[mode, backend, case] = metric
    return values

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=DEFAULT)
    parser.add_argument('--output-dir', type=Path, default=ROOT / 'porting/figures')
    args = parser.parse_args()
    values = load(args.input)
    # Keep rendering outside all benchmark timing intervals.
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    import numpy
    import platform
    matplotlib.rcParams['svg.hashsalt'] = 'ferrum-prusti-client-wall-v1'
    fig, axes = plt.subplots(1, 2, figsize=(12, 5.3), sharey=True, layout='constrained')
    colors = {'native': '#126782', 'jvm': '#c65d31'}
    for ax, mode, title in zip(axes, ('fresh', 'service_later_mean'), ('Fresh process', 'Later service requests')):
        for backend, label, offset in [('native', 'Ferrum native', -0.13), ('jvm', 'Bundled JVM Silicon', 0.13)]:
            metrics = [values[mode, backend, case] for case, _ in CASES]
            med = [m['median'] for m in metrics]
            errors = [[m['median'] - m['min'] for m in metrics], [m['max'] - m['median'] for m in metrics]]
            ax.errorbar([i + offset for i in range(4)], med, yerr=errors, fmt='o', color=colors[backend], capsize=4, linewidth=1.4, markersize=6, label=label)
        ax.set_title(title)
        ax.set_xticks(range(4), [label for _, label in CASES])
        ax.set_ylim(bottom=0)
        ax.grid(axis='y', color='#dddddd', linewidth=.7)
        ax.set_axisbelow(True)
        ax.spines[['top', 'right']].set_visible(False)
    axes[0].set_ylabel('Client command wall time (seconds)')
    axes[0].legend(frameon=False, loc='upper left')
    fig.suptitle('Direct Prusti: client wall time, one worker and branch parallelism off', fontsize=13)
    fig.text(.5, -.055, 'Points: median; whiskers: min–max across 3 paired blocks. Later service: mean of 2 requests per block.\nDevelopment builds; warm file cache. Native Ferrum afdf10c; bundled JVM Silicon 6b540aa.', ha='center', fontsize=9)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    outputs = {}
    for suffix in ('png', 'svg'):
        path = args.output_dir / f'prusti-client-wall.{suffix}'
        metadata = {'Creator': 'tools/performance/plot_prusti.py'}
        if suffix == 'svg':
            metadata['Date'] = None
        fig.savefig(path, dpi=180, bbox_inches='tight', metadata=metadata)
        if suffix == 'svg':
            # Matplotlib leaves spaces before path-data newlines; retain the
            # separators while making generated text pass git diff --check.
            path.write_text('\n'.join(line.rstrip() for line in path.read_text().splitlines()) + '\n')
        outputs[path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
        print(path)
    manifest = {
        'input': args.input.name,
        'input_sha256': hashlib.sha256(args.input.read_bytes()).hexdigest(),
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'python': platform.python_version(),
        'matplotlib': matplotlib.__version__,
        'numpy': numpy.__version__,
        'output_sha256': outputs,
        'scope': 'One worker, branch off; median and min-max of three paired blocks; later service values are means of two requests within each block.',
    }
    (args.output_dir / 'prusti-client-wall.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print('input_sha256', manifest['input_sha256'])

if __name__ == '__main__':
    main()
