#!/usr/bin/env python3
"""Instantiate an isolated tools-only driver crate against a frozen runtime."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runtime', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    runtime = args.runtime.resolve(strict=True)
    if not (runtime / 'Cargo.toml').is_file():
        parser.error('runtime must contain the frozen Ferrum Cargo.toml')
    source = Path(__file__).resolve().parent / 'rust'
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    shutil.copytree(source / 'src', output / 'src')
    shutil.copy2(source / 'Cargo.lock', output / 'Cargo.lock')
    manifest = (source / 'Cargo.toml.in').read_text().replace(
        '@RUNTIME_PATH@', json.dumps(str(runtime)))
    (output / 'Cargo.toml').write_text(manifest)
    files = {str(p.relative_to(output)): hashlib.sha256(p.read_bytes()).hexdigest()
             for p in sorted(output.rglob('*')) if p.is_file()}
    (output / 'preparation.json').write_text(json.dumps({
        'runtime': str(runtime), 'files': files,
        'limitation': 'This instantiates files; it does not build or validate the runtime.'
    }, indent=2) + '\n')


if __name__ == '__main__':
    main()
