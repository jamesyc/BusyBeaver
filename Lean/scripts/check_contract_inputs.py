#!/usr/bin/env python3
"""Verify projected proof inputs against the complete published contract census.

Read-only provenance/input audit; Lean's kernel checks the actual mathematical
certificates. The gzip copy is lossless and its decompression is bounded.
"""
from pathlib import Path
import gzip
import hashlib
import json
ROOT = Path(__file__).resolve().parents[1]
p = ROOT / 'data/original_contracts.json.gz'
with gzip.open(p, 'rb') as f:
    raw = f.read(16037505)
assert len(raw) == 16037504
assert hashlib.sha256(raw).hexdigest() == '7cc47482b8ffcaad47dac92c9033a54a93d1a43d4686db2ccd165542897dfffe'
cs = json.loads(raw)
assert len(cs) == 5134 and [c['index'] for c in cs] == list(range(5134))
def seg(x):
    if x[0] == 'r':
        assert x[1] in (0, 1) and x[2] >= 0 and x[3] >= 0
        return f'.run {str(bool(x[1])).lower()} {x[2]} {x[3]}'
    assert x[0] == 'b'
    if x[1] == 'none':
        assert x[2] == -1
        return '.box (.plain .none)'
    if x[1] in ('inc', 'dec'):
        assert 0 <= x[2] < 9
        return f'.box (.plain (.{x[1]} {x[2]}))'
    assert x[1] == 'mark' and 0 <= x[2] < 9
    return f'.box (.mark {x[2]})'
def state(x):
    return (f'({x["q"]}, {str(x["on_left"]).lower()}, [' + ', '.join(map(seg, x['left']))
            + '], [' + ', '.join(map(seg, x['right'])) + '])')
def branch(c):
    return 'none' if c['branch'] is None else f'some ({c["branch"][0]}, {str(c["branch"][1]).lower()})'
r = json.loads((ROOT / 'data/contract_pilot.json').read_text())
ids = [0, 1, 2, 5, 6, 7, 5085, 5086, 5087, 5088]
assert r['indices'] == ids and r['original_contracts'] == [cs[k] for k in ids]
lean = (ROOT / 'PA215/ContractPilot.lean').read_text()
for k in ids:
    c = cs[k]
    assert not c['halt']
    decl = f'def c{k} : Contract := ⟨{branch(c)}, {state(c["initial"])}, {state(c["target"])}⟩\n'
    assert decl in lean, f'Changed original input at index{k}'
c = json.loads((ROOT / 'data/contract5114.json').read_text())
assert c == cs[5114] and c['halt'] and c['target'] is None and c['branch'] is None
lean = (ROOT / 'PA215/Contract5114.lean').read_text()
assert f'def initial : SConf := {state(c["initial"])}\n' in lean
assert 'theorem checked : check 4000 none initial = true' in lean
print('PASS: pinned5134-census bytes; all10pilot inputs and terminal5114 input match exactly.')
