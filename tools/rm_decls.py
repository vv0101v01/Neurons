#!/usr/bin/env python3
"""Remove whole `///|` blocks by declaration name (used to delete dead code).

    python3 tools/rm_decls.py NAME[@file.mbt] ...

If every named declaration lives in one file the `@file` suffix may be omitted
when it is unambiguous.  Nothing is compiled here -- run `moon check` after.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
DECL = re.compile(r'^(?:pub(?:\s*\([^)]*\))?\s+)?(?:(?:async|priv)\s+)?'
                  r'(?:fn|let|const|struct|enum|type|trait)\s+([A-Za-z_][A-Za-z0-9_]*)')


def split_blocks(text):
    """Return [prefix, block, block, ...] such that ''.join == text."""
    parts = text.split('///|')
    return parts


def remove(text, name):
    parts = text.split('///|')
    hits = 0
    keep = [parts[0]]
    for block in parts[1:]:
        m = DECL.match(block.lstrip())
        if m and m.group(1) == name:
            hits += 1
            continue
        keep.append(block)
    return '///|'.join(keep), hits


def main(argv):
    targets = []
    for a in argv:
        if '@' in a:
            n, f = a.split('@', 1)
            targets.append((n, f))
        else:
            targets.append((a, None))
    files = {p.name: p for p in ROOT.glob('*.mbt')}
    src = {n: p.read_text(encoding='utf-8') for n, p in files.items()}
    removed = []
    for name, want in targets:
        cand = [n for n, t in src.items() if re.search(
            r'(?m)^(?:pub\s+)?fn\s+' + re.escape(name) + r'\b', t)]
        if want:
            cand = [c for c in cand if c == want]
        if len(cand) != 1:
            print(f'  SKIP {name}: found in {cand}')
            continue
        f = cand[0]
        src[f], hits = remove(src[f], name)
        if not hits:
            print(f'  SKIP {name}: no ///| block matched in {f}')
            continue
        removed.append((name, f))
    for n, p in files.items():
        if src[n] != p.read_text(encoding='utf-8'):
            p.write_text(src[n], encoding='utf-8')
    print(f'removed {len(removed)} declarations')
    for n, f in removed:
        print(f'  - {n} ({f})')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
