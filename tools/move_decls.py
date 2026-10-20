#!/usr/bin/env python3
"""Move top-level declarations between files of the same MoonBit package.

MoonBit packages are a single namespace: every `.mbt` file in a package shares
it and declarations may be moved between files freely.  A move is therefore an
*isomorphism of interfaces* — the exported symbol set is unchanged, which is
exactly what `pkg.generated.mbti` records and what `moon info` re-checks.

A source file is a sequence of `///|` blocks.  Each block belongs to the
declarations it introduces, so moving a block moves the declaration together
with its doc comment.

Usage:
  python3 tools/move_decls.py NAME... --from SRC --to DST [--dry-run]
  python3 tools/move_decls.py --extract DST NAME... --from SRC...  # merge many
  python3 tools/move_decls.py --list FILE
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MARK = "///|"
DECL = re.compile(r"^(?:pub\s+)?(?:fn|struct|enum|type|let|trait)\s+([A-Za-z_][A-Za-z0-9_]*)")
# `pub extend T with ...` implements traits for T; it travels with T.
EXTEND = re.compile(r"^pub\s+extend\s+([A-Za-z_][A-Za-z0-9_]*)\s+with")


def parse(path):
    """[(block_text, declared_names)] — the first item is the file header."""
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines(keepends=True)
    blocks, cur = [], []
    for line in lines:
        if line.startswith(MARK):
            blocks.append(cur)
            cur = [line]
        else:
            cur.append(line)
    blocks.append(cur)
    out = []
    for b in blocks:
        names = set()
        for line in b:
            m = DECL.match(line) or EXTEND.match(line)
            if m:
                names.add(m.group(1))
        out.append(("".join(b), names))
    return out


def decl_names(path):
    names = []
    for _, ns in parse(path):
        names.extend(sorted(ns))
    return names


def main(argv):
    if "--list" in argv:
        f = Path(argv[argv.index("--list") + 1])
        print("\n".join(decl_names(f)))
        return 0
    srcs = [Path(a) for a in _after(argv, "--from")]
    dest = Path(argv[argv.index("--to") + 1]) if "--to" in argv else \
        Path(argv[argv.index("--extract") + 1])
    wanted = [a for a in argv[1:] if not a.startswith("--") and
              a not in srcs and a != dest and not a.endswith(".mbt")]
    dry = "--dry-run" in argv
    if not wanted:
        sys.exit("no declaration names given")
    _do_move(srcs, dest, wanted, dry)
    return 0


def _after(argv, flag):
    i = argv.index(flag)
    out = []
    for a in argv[i + 1:]:
        if a.startswith("--"):
            break
        out.append(a)
    return out


def _do_move(sources, dest, wanted, dry_run=False):
    dest_blocks = parse(dest) if dest.exists() else []
    dest_names = set()
    for _, ns in dest_blocks:
        dest_names |= ns
    clash = sorted(set(wanted) & dest_names)
    if clash:
        sys.exit(f"already declared in {dest.name}: {clash}")

    moved_blocks, moved = [], []
    for src in sources:
        keep = []
        for text, names in parse(src):
            if names and names & set(wanted):
                if not names <= set(wanted):
                    sys.exit(f"{src.name}: block declares {sorted(names)}, not all wanted")
                moved_blocks.append(text if text.endswith("\n") else text + "\n")
                moved.append((src.name, sorted(names)))
            else:
                keep.append(text)
        body = "".join(keep).rstrip() + "\n"
        if body != src.read_text(encoding="utf-8"):
            if not dry_run:
                src.write_text(body, encoding="utf-8")

    found = {n for _, ns in moved for n in ns}
    missing = sorted(set(wanted) - found)
    if missing:
        sys.exit(f"not found: {missing}")

    if dry_run:
        for f, ns in moved:
            print(f"  {f}: {ns} -> {dest.name}")
        return

    existing = "".join(t for t, _ in parse(dest)).rstrip() + "\n" if dest.exists() else ""
    addition = "".join(moved_blocks)
    dest.write_text(existing + "\n" + addition, encoding="utf-8")
    for f, ns in moved:
        print(f"moved {ns} from {f} -> {dest.name}")


if __name__ == "__main__":
    sys.exit(main(sys.argv))
