#!/usr/bin/env python3
"""Find dead and duplicated MoonBit declarations in this package.

Two analyses, both purely syntactic (the package shares one namespace, so a name
reference anywhere in the directory counts):

  dead     a private (`fn`/`let`/`struct`/`enum`/`type` without `pub`) top-level
           declaration that no other block mentions -- not even a test.
  dupe     two declarations whose normalised bodies are identical.

Report only; nothing is edited.  Usage:
    python3 tools/deadcode.py [--dead] [--dupe] [--json FILE]
"""
import json
import pathlib
import re
import sys
from collections import defaultdict

ROOT = pathlib.Path(__file__).resolve().parent.parent
DECL = re.compile(
    r'^(?P<pub>pub(?:\s*\([^)]*\))?\s+)?'
    r'(?:(?:async|priv)\s+)?'
    r'(?P<kind>fn|let|const|struct|enum|type|trait|impl)\s+'
    r'(?P<name>[A-Za-z_][A-Za-z0-9_]*)'
)
EXTEND = re.compile(r'^pub\s+extend\s+(?P<ty>[A-Za-z_][A-Za-z0-9_]*)')


def blocks(path):
    """Yield (name, kind, is_pub, text) for every `///|` block of a file."""
    raw = path.read_text(encoding='utf-8')
    for chunk in raw.split('///|'):
        lines = [l for l in chunk.splitlines()]
        body = '\n'.join(lines).strip('\n')
        if not body.strip():
            continue
        m = DECL.match(body.lstrip())
        if m:
            yield m.group('name'), m.group('kind'), bool(m.group('pub')), body
            continue
        m = EXTEND.match(body.lstrip())
        if m:
            yield m.group('ty'), 'extend', True, body


def normalise(body):
    """Body with the declaration line removed, whitespace and comments stripped."""
    lines = body.splitlines()[1:]
    out = []
    for l in lines:
        l = re.sub(r'//.*$', '', l)
        l = ''.join(l.split())
        if l:
            out.append(l)
    return '\n'.join(out)


def main():
    files = sorted(p for p in ROOT.glob('*.mbt'))
    src = {p.name: p.read_text(encoding='utf-8') for p in files}
    test_files = {n for n in src if n.endswith(('_wbtest.mbt', '_test.mbt'))}
    all_text = '\n'.join(src.values())

    # ---- dead -------------------------------------------------------------
    dead = []
    for name in sorted(src):
        if name in test_files:
            continue
        for dname, kind, is_pub, body in blocks(ROOT / name):
            if is_pub or kind in ('impl', 'extend', 'trait'):
                continue
            if dname in ('main', 'init'):
                continue
            # occurrences outside this block
            rest = all_text.replace(body, '', 1)
            hits = len(re.findall(r'(?<![A-Za-z0-9_])' + re.escape(dname) + r'(?![A-Za-z0-9_])', rest))
            if hits == 0:
                dead.append({'name': dname, 'kind': kind, 'file': name,
                             'lines': body.count('\n') + 1})

    # ---- duplicate bodies -------------------------------------------------
    seen = defaultdict(list)
    for name in sorted(src):
        if name in test_files:
            continue
        for dname, kind, is_pub, body in blocks(ROOT / name):
            if kind in ('impl', 'extend', 'struct', 'enum', 'type', 'trait'):
                continue
            norm = normalise(body)
            if len(norm) < 40:          # trivial one-liners are not interesting
                continue
            seen[norm].append({'name': dname, 'file': name, 'kind': kind,
                               'lines': body.count('\n') + 1})

    dupes = []
    for norm, where in seen.items():
        names = {w['name'] for w in where}
        if len(where) > 1 and len(names) > 1:
            dupes.append({'names': sorted(names), 'sites': where, 'size': len(norm)})
    dupes.sort(key=lambda d: -d['size'])

    if '--json' in sys.argv:
        out = sys.argv[sys.argv.index('--json') + 1]
        pathlib.Path(out).write_text(
            json.dumps({'dead': dead, 'duplicates': dupes}, ensure_ascii=False, indent=1),
            encoding='utf-8')

    print(f'== dead private declarations: {len(dead)} ==')
    for d in dead:
        print(f"  {d['file']:<28} {d['kind']:<7} {d['name']}  ({d['lines']} lines)")
    print(f'\n== duplicated bodies: {len(dupes)} groups ==')
    for g in dupes[:40]:
        sites = ', '.join(f"{s['name']}@{s['file']}" for s in g['sites'])
        print(f"  [{g['size']:>4} chars] {sites}")
    return 0


if __name__ == '__main__':
    sys.exit(main())
