#!/usr/bin/env python3
"""Static dependency analysis of the MoonBit sources.

Nodes are *public* symbols (unique across the package, as `moon info`
guarantees), so the graph is unambiguous.  For every `///|` block we record
which public symbols of other files it mentions; that gives the file-level
dependency graph.  Symbols are then condensed into strongly connected
components (MoonBit allows mutual recursion inside a package, so cycles are
expected) and each file gets a layer = longest path from the DAG sources.

Usage:
  python3 tools/arch_report.py            # human readable
  python3 tools/arch_report.py --json f   # machine readable
  python3 tools/arch_report.py --mermaid  # mermaid diagram
"""
import json
import re
import sys
from collections import defaultdict, namedtuple
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MBTI = ROOT / "pkg.generated.mbti"

DECL = re.compile(r"^(\s*)(pub\s+)?(?:fn|struct|enum|type|let|trait)\s+([A-Za-z_][A-Za-z0-9_]*)")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def strip_noise(text):
    text = re.sub(r"//[^\n]*", "", text)
    text = re.sub(r'"(?:[^"\\]|\\.)*"', '""', text)
    return text


def public_symbols():
    """Public symbols and the file that declares them."""
    owner = {}
    for path in sorted(ROOT.glob("*.mbt")):
        for line in path.read_text(encoding="utf-8").splitlines():
            m = DECL.match(line)
            if m and m.group(2):
                owner.setdefault(m.group(3), path.name)
    return owner


def blocks(path):
    """(declared public names, identifiers) per `///|` block, comments removed."""
    src = path.read_text(encoding="utf-8")
    for block in src.split("///|"):
        code = strip_noise(block)
        names = set()
        for line in code.splitlines():
            m = DECL.match(line)
            if m and m.group(2):
                names.add(m.group(3))
        yield names, set(IDENT.findall(code))


def main():
    owner = public_symbols()
    files = sorted(p.name for p in ROOT.glob("*.mbt"))
    edges = defaultdict(set)          # file -> files it uses
    edges_sym = defaultdict(set)      # symbol -> symbols it uses
    metrics = {}
    for name in files:
        path = ROOT / name
        src = path.read_text(encoding="utf-8")
        pub_decl = [l for l in src.splitlines() if DECL.match(l) and DECL.match(l).group(2)]
        metrics[name] = {
            "lines": len(src.splitlines()),
            "public": len([l for l in pub_decl]),
        }
        for names, ids in blocks(path):
            ext = {owner[i] for i in ids if i in owner and owner[i] != name}
            for n in names:
                edges[name] |= ext
                edges_sym[n] |= {i for i in ids if i in owner and owner[i] != name}

    # symbol level condensation
    graph = {s: {t for t in edges_sym[s]} for s in owner}
    index, low, on, stack, comps = {}, {}, set(), [], []
    counter = [0]
    sys.setrecursionlimit(200000)

    def strong(v):
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on.add(v)
        for w in graph.get(v, ()):
            if w not in index:
                strong(w)
                low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                on.discard(w)
                comp.append(w)
                if w == v:
                    break
            comps.append(comp)

    for v in graph:
        if v not in index:
            strong(v)
    comp_of = {v: i for i, c in enumerate(comps) for v in c}
    cadj = defaultdict(set)
    for v, ws in graph.items():
        for w in ws:
            if comp_of[v] != comp_of[w]:
                cadj[comp_of[v]].add(comp_of[w])
    depth = {i: 0 for i in range(len(comps))}
    for _ in range(len(comps) + 1):
        changed = False
        for i in range(len(comps)):
            d = 0 if not cadj[i] else 1 + max(depth[j] for j in cadj[i])
            if d != depth[i]:
                depth[i] = d
                changed = True
        if not changed:
            break

    # File-level condensation and layering: 0 = uses nothing, else 1 + max dep.
    fidx, flow, fon, fstack, fcomps = {}, {}, set(), [], []
    fcounter = [0]

    def fstrong(v):
        fidx[v] = flow[v] = fcounter[0]
        fcounter[0] += 1
        fstack.append(v)
        fon.add(v)
        for w in edges[v]:
            if w not in fidx:
                fstrong(w)
                flow[v] = min(flow[v], flow[w])
            elif w in fon:
                flow[v] = min(flow[v], fidx[w])
        if flow[v] == fidx[v]:
            comp = []
            while True:
                w = fstack.pop()
                fon.discard(w)
                comp.append(w)
                if w == v:
                    break
            fcomps.append(comp)

    for v in files:
        if v not in fidx:
            fstrong(v)
    fcomp_of = {v: i for i, c in enumerate(fcomps) for v in c}
    fadj2 = defaultdict(set)
    for a in edges:
        for b in edges[a]:
            if fcomp_of[a] != fcomp_of[b]:
                fadj2[fcomp_of[a]].add(fcomp_of[b])
    fdepth = {i: 0 for i in range(len(fcomps))}
    for _ in range(len(fcomps) + 1):
        changed = False
        for i in range(len(fcomps)):
            d = 0 if not fadj2[i] else 1 + max(fdepth[j] for j in fadj2[i])
            if d != fdepth[i]:
                fdepth[i] = d
                changed = True
        if not changed:
            break
    file_layer = {name: fdepth[fcomp_of[name]] for name in files}

    print(f"== per file ({len(files)} files, {len(owner)} public symbols) ==")
    for name in sorted(files, key=lambda n: (-file_layer[n], n)):
        print(
            f"{name:34s} layer={file_layer[name]:2d} lines={metrics[name]['lines']:5d} "
            f"pub={metrics[name]['public']:4d} uses={len(edges[name]):2d} "
            f"used_by={sum(1 for g in edges if name in edges[g]):2d}"
        )

    print("\n== file dependencies (uses -> used) ==")
    for a in sorted(edges):
        if edges[a]:
            print(f"{a:34s} -> {', '.join(sorted(edges[a]))}")

    print("\n== file-level cycles (one package: allowed, blocks .pkg splitting) ==")
    for c in sorted(fcomps, key=lambda c: -len(c)):
        if len(c) > 1:
            print(f"  {len(c):2d} files: {', '.join(sorted(c))}")

    print("\n== multi-file symbol cycles ==")
    seen = set()
    for c in comps:
        fs = sorted({owner[v] for v in c if v in owner})
        if len(fs) > 1:
            key = tuple(fs)
            if key in seen:
                continue
            seen.add(key)
            print(f"{len(c):4d} symbols / {len(fs):2d} files: {', '.join(fs)}")

    if "--mermaid" in sys.argv:
        print("\n== mermaid ==")
        print("graph TD")
        for a in sorted(edges):
            for b in sorted(edges[a]):
                print(f"  {a.replace('.', '_').replace('-', '_')} --> {b.replace('.', '_').replace('-', '_')}")

    if "--json" in sys.argv:
        out = sys.argv[sys.argv.index("--json") + 1]
        Path(out).write_text(json.dumps({
            "files": [
                {
                    "name": n,
                    "layer": file_layer[n],
                    **metrics[n],
                    "uses": sorted(edges[n]),
                    "used_by": sorted(g for g in edges if n in edges[g]),
                }
                for n in files
            ],
            "cycles": [
                {"symbols": len(c), "files": sorted({owner[v] for v in c if v in owner})}
                for c in comps if len({owner[v] for v in c if v in owner}) > 1
            ],
        }, indent=1, ensure_ascii=False))
        print(f"\nwritten {out}")


if __name__ == "__main__":
    main()
