#!/usr/bin/env python3
"""Public declarations that no other declaration, test, check or spec entry mentions."""
import pathlib, re, sys, json
from collections import defaultdict
ROOT = pathlib.Path(__file__).resolve().parent.parent
DECL = re.compile(r'^(?P<pub>pub(?:\s*\([^)]*\))?\s+)?(?:(?:async|priv)\s+)?(?P<kind>fn|let|const|struct|enum|type|trait)\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)')
src = {p.name: p.read_text(encoding='utf-8') for p in sorted(ROOT.glob('*.mbt'))}
main_txt = (ROOT/'cmd'/'main'/'main.mbt').read_text(encoding='utf-8')
spec_txt = src.get('spec.mbt','')
out=[]
for f,txt in src.items():
    for chunk in txt.split('///|'):
        body=chunk.strip('\n')
        m=DECL.match(body.lstrip())
        if not m or not m.group('pub'): continue
        name,kind=m.group('name'),m.group('kind')
        if kind=='impl' or name=='main': continue
        # references outside this block
        others=[t.replace(body,'',1) for n,t in src.items()]
        others.append(main_txt)
        hits=sum(len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(name)+r'(?![A-Za-z0-9_])', t)) for t in others)
        # registered in spec.mbt / print-line in cmd/main
        in_spec = name in spec_txt
        in_main = name in main_txt
        if hits==0:
            out.append(dict(name=name,kind=kind,file=f,spec=in_spec,main=in_main,lines=body.count('\n')+1))
print(f'== public declarations with zero in-package references: {len(out)} ==')
for d in sorted(out,key=lambda x:(-x['lines'])):
    print(f"  {d['file']:<26} {d['kind']:<7} {d['name']:<40} spec={d['spec']} main={d['main']} ({d['lines']} lines)")
json.dump(out,open('/tmp/deadapi.json','w'),ensure_ascii=False,indent=1)
