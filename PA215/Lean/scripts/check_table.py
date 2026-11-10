#!/usr/bin/env python3
"""Audit Lean's literal row/source records against the pinned published table.

This is an input-import audit, not a proof checker. Lean's exact_source_rows
proves semanticRows = sourceRows independently. The accepted logical chain does
not assume Python correctness or this script's output.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
EXPECTED = '89c0a1007a7a670463fd6edb78f14d1312a1ad9dc949916d39ce7aebbde4e2ac'
raw = (ROOT / 'data/pa215.tm').read_bytes()
assert hashlib.sha256(raw).hexdigest() == EXPECTED, 'Published table identity mismatch'
text = raw.decode('ascii')
rows = []
for line in text.splitlines():
    if line.startswith('#'):
        continue
    q, b, w, d, t = line.split()
    q, b, w, t = map(int, (q, b, w, t))
    assert 0 <= q < 215 and b in (0, 1) and w in (0, 1)
    assert d in ('L', 'R') and 0 <= t <= 215
    rows.append((q, bool(b), bool(w), d == 'R', t))
assert len(rows) == 430
assert [(q, b) for q, b, *_ in rows] == [(q, b) for q in range(215) for b in (False, True)]
lean = (ROOT / 'PA215/Machine.lean').read_text()
source_text = re.search(r'def sourceText : String := ("(?:[^"\\]|\\.)*")', lean)
assert source_text and json.loads(source_text.group(1)).encode('ascii') == raw
literal = lean.split('def sourceRows : List (Nat × Bool × Bool × Bool × Nat) := [', 1)[1].split(']\n', 1)[0]
pat = r'\((\d+), (true|false), (true|false), (true|false), (\d+)\)'
parsed = [(int(q), b == 'true', w == 'true', d == 'true', int(t))
          for q, b, w, d, t in re.findall(pat, literal)]
assert parsed == rows, 'Lean literal row data differs from published bytes'
assert re.sub(pat, '', literal).strip(' ,\n\r\t') == '', 'Unexpected literal content'
print('PASS: exact published bytes, literal source text, and all 430 literal row records agree.')
print('SHA256:', EXPECTED)
