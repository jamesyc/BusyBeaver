#!/usr/bin/env python3
"""Input audit only: bind the Lean literals to the original contract projection."""
from pathlib import Path
import json
import hashlib
import sys
ROOT = Path(__file__).resolve().parents[1]
r = json.loads((ROOT / 'data/contract4942.json').read_text())
c = r['original_contract']
assert r['source_corpus_sha256'] == '7cc47482b8ffcaad47dac92c9033a54a93d1a43d4686db2ccd165542897dfffe'
assert c['index'] == 4942 and c['branch'] is None and not c['halt']
assert c['tag'] == 'EBreak' and c['arg'] == 1 and c['path'] == '1010011'
def seg(x):
    if x[0] == 'r':
        assert x[1] in (0, 1) and x[2] >= 0 and x[3] >= 0
        return f'.run {str(bool(x[1])).lower()} {x[2]} {x[3]}'
    assert x == ['b', 'none', -1]
    return '.box (.plain .none)'
def state(x):
    return (f'({x["q"]}, {str(x["on_left"]).lower()}, [' + ', '.join(map(seg, x['left']))
            + '], [' + ', '.join(map(seg, x['right'])) + '])')
lean = (ROOT / 'PA215/Contract4942.lean').read_text()
for name in ('initial', 'target'):
    assert f'def {name} : SConf := {state(c[name])}\n' in lean
assert 'def result := exec machine none (fun s => sMatches s target) 500 initial false' in lean
if len(sys.argv) > 1:
    raw = Path(sys.argv[1]).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == r['source_corpus_sha256']
    assert json.loads(raw)[4942] == c
    print('PASS: projection is byte-identity-bound to the original full corpus.')
print('PASS: Lean initial/target/branch exactly match the stored original4942 input.')
