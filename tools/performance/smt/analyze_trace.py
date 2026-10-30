#!/usr/bin/env python3
"""Audit relayed SMT bytes and pair commands with protocol responses."""
import argparse
import bisect
from collections import Counter
import hashlib
import json
from pathlib import Path
import re


def expressions(data):
    """Yield top-level byte spans, ignoring SMT comments and quoted delimiters."""
    pos, size = 0, len(data)
    while pos < size:
        if data[pos] in b' \t\r\n':
            pos += 1
            continue
        if data[pos] == 59:
            end = data.find(b'\n', pos)
            pos = size if end < 0 else end + 1
            continue
        start, depth, quote = pos, 0, None
        while pos < size:
            char = data[pos]
            if quote is not None:
                if char == quote:
                    if quote == 34 and pos + 1 < size and data[pos + 1] == 34:
                        pos += 2
                        continue
                    quote = None
                elif quote == 124 and char == 92 and pos + 1 < size:
                    pos += 2
                    continue
                pos += 1
                if quote is None and depth == 0:
                    break
                continue
            if char in (34, 124):
                quote = char
                pos += 1
            elif char == 59:
                end = data.find(b'\n', pos)
                pos = size if end < 0 else end + 1
            elif char == 40:
                depth += 1
                pos += 1
            elif char == 41:
                depth -= 1
                pos += 1
                if depth < 0:
                    raise ValueError(f'Unexpected close parenthesis at {pos}')
                if depth == 0:
                    break
            elif depth == 0 and char in b' \t\r\n':
                break
            else:
                pos += 1
        if quote is not None or depth:
            raise ValueError(f'Incomplete expression at {start}')
        yield start, pos


def canonical(data):
    # Keep quoted tokens intact while dropping comments and insignificant space.
    pattern = rb';[^\n]*|"(?:[^"]|"")*"|\|(?:[^|\\]|\\.)*\||[()]|[^\s();"|]+'
    return b' '.join(m.group() for m in re.finditer(pattern, data)
                     if not m.group().startswith(b';'))


def analyze(folder):
    metadata = json.loads((folder / 'metadata.json').read_text())
    data = {name: (folder / f'{name}.bin').read_bytes() for name in ('stdin', 'stdout')}
    chunks = [json.loads(line) for line in (folder / 'chunks.jsonl').read_text().splitlines()]
    streams = {}
    for name in data:
        stream = [c for c in chunks if c['stream'] == name]
        offset = 0
        for chunk in stream:
            if chunk['offset'] != offset:
                raise ValueError(f'Noncontiguous {name} capture')
            offset += chunk['length']
        if offset != len(data[name]):
            raise ValueError(f'Incomplete {name} chunk index')
        streams[name] = (stream, [c['offset'] + c['length'] for c in stream])

    def timestamp(name, end, field):
        stream, ends = streams[name]
        return stream[bisect.bisect_left(ends, end)][field]

    responses = list(expressions(data['stdout']))
    response_index = 0
    print_success = False
    commands, queries, issues = [], [], []
    for index, (start, end) in enumerate(expressions(data['stdin'])):
        text = data['stdin'][start:end]
        match = re.match(rb'\(\s*([^\s()]+)', text)
        if not match:
            issues.append(f'Non-command input at {start}')
            continue
        name = match.group(1).decode()
        normalized = canonical(text)
        row = {'index': index, 'name': name, 'start': start, 'end': end,
               'bytes': end - start, 'sha256': hashlib.sha256(text).hexdigest(),
               'canonical_sha256': hashlib.sha256(normalized).hexdigest(),
               'forwarded_ns': timestamp('stdin', end, 'forwarded_ns'),
               'received_ns': timestamp('stdin', end, 'received_ns'),
               'preview': normalized[:400].decode(errors='replace')}
        setting = re.match(rb'\(\s*set-option\s+:print-success\s+(true|false)\s*\)', normalized)
        if setting:
            print_success = setting.group(1) == b'true'
        always = name.startswith(('check-sat', 'get-')) or name in ('echo', 'eval')
        if always or print_success:
            if response_index >= len(responses):
                issues.append(f'Missing response to command {index} {name}')
            else:
                a, b = responses[response_index]
                response = data['stdout'][a:b].decode(errors='replace')
                observed = timestamp('stdout', b, 'received_ns')
                row.update(response_index=response_index, response=response,
                           response_received_ns=observed,
                           response_wait_s=(observed - row['received_ns']) / 1e9)
                if not always and response != 'success':
                    issues.append(f'Unexpected response to {index} {name}: {response[:80]}')
                if observed < row['received_ns']:
                    issues.append(f'Response timestamp precedes command {index}')
                response_index += 1
        if name.startswith('check-sat'):
            queries.append(row)
        if name == 'assert':
            row['forall_count'] = len(re.findall(rb'\(\s*forall\b', normalized))
            row['exists_count'] = len(re.findall(rb'\(\s*exists\b', normalized))
            row['pattern_count'] = normalized.count(b':pattern')
        commands.append(row)
    if response_index != len(responses):
        issues.append(f'{len(responses) - response_index} unmatched responses')
    return {'folder': str(folder), 'metadata': metadata, 'issues': issues,
            'command_counts': dict(Counter(c['name'] for c in commands)),
            'response_count': len(responses), 'commands': commands, 'queries': queries,
            'forall_count': sum(c.get('forall_count', 0) for c in commands),
            'exists_count': sum(c.get('exists_count', 0) for c in commands),
            'pattern_count': sum(c.get('pattern_count', 0) for c in commands),
            'input_bytes': len(data['stdin']), 'output_bytes': len(data['stdout']),
            'input_sha256': hashlib.sha256(data['stdin']).hexdigest(),
            'output_sha256': hashlib.sha256(data['stdout']).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('folder', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = analyze(args.folder)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('commands', 'queries')}))
    if result['issues']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
