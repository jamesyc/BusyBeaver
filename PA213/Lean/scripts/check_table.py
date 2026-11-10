#!/usr/bin/env python3
"""Bind the published PA213 inputs to their literal Lean representations."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT.parent / "evidence/pa213"


def check_inputs(root):
    raw = (root / "data/pa213.tm").read_bytes()
    assert hashlib.sha256(raw).hexdigest() == (
        "b332b36d8ed9c909c51df27727a2c68a6890c122e102a4e7a6d411a483094989")
    rows = []
    for line in raw.decode("ascii").splitlines():
        if line.startswith("#"):
            continue
        q, b, w, direction, target = line.split()
        assert direction in ("L", "R")
        assert b in ("0", "1") and w in ("0", "1")
        rows.append((int(q), b == "1", w == "1", direction == "R", int(target)))
    active = set(range(215)) - {122, 214}
    assert len(rows) == 426
    assert {(q, b) for q, b, *_ in rows} == {
        (q, b) for q in active for b in (False, True)}
    assert all(target in active | {215} for *_, target in rows)
    candidate = (root / "PA213/CandidateTable.lean").read_text()
    labels = json.loads(re.search(r"def denseLabels : List Nat := (\[[^\n]+\])",
                                 candidate).group(1))
    assert len(labels) == 215 and len(set(labels)) == 215
    label = labels + [254]
    assert label[0] == 74 and label[215] == 254
    pattern = r"\| (\d+), (false|true) => some \((false|true), (false|true), (\d+)\)"
    physical = [(int(q), b == "true", w == "true", d == "true", int(t))
                for q, b, w, d, t in re.findall(pattern, candidate)]
    assert len(physical) == 426
    assert set(physical) == {
        (label[q], b, w, d, label[t]) for q, b, w, d, t in rows}, "Physical table differs"
    dense = (root / "PA213/Machine.lean").read_text()
    pattern = (r"\| (\d+) => if b then ⟨(true|false), (true|false), target (\d+)⟩"
               r" else ⟨(true|false), (true|false), target (\d+)⟩")
    auxiliary = []
    for q, w1, d1, t1, w0, d0, t0 in re.findall(pattern, dense):
        auxiliary.extend([(int(q), False, w0 == "true", d0 == "true", int(t0)),
                          (int(q), True, w1 == "true", d1 == "true", int(t1))])
    assert len(auxiliary) == 430
    assert [row for row in auxiliary if row[0] in active] == rows, "Dense table differs"
    assert all(q == t for q, _, _, _, t in auxiliary if q not in active)
    source = (root / "data/candidate_source.json").read_bytes()
    assert hashlib.sha256(source).hexdigest() == (
        "e5e8bae79278c83b5ed96a6981a81252916deb702473e6f186f3ba32467289ba")
    sites = (root / "PA213/SourceSites.lean").read_text()
    parsed = []
    operations = {"inc": "EInc", "dec": "EDecnz", "breakTo": "EBreak",
                  "continueTo": "EContinue", "halt": "EHalt"}
    for path, op, argument in re.findall(r"⟨\[([a-z,]*)\],\.(\w+)(?: (\d+))?⟩", sites):
        bits = "".join("1" if bit == "true" else "0" for bit in path.split(",") if bit)
        instruction = [operations[op], int(argument) if argument else None]
        parsed.append([bits, instruction])
    assert len(parsed) == 3947 and parsed == json.loads(source), "Source sites differ"


def main():
    check_inputs(ROOT)
    receipt = json.loads((EVIDENCE / "FINAL_PA_RECEIPT.json").read_text())
    frozen = (EVIDENCE / "FINAL_PA_MANIFEST.json").read_bytes()
    assert hashlib.sha256(frozen).hexdigest() == receipt["source_manifest"]["sha256"]
    overlays = json.loads((ROOT / "proof_overlays/MANIFEST.json").read_text())
    count = 0
    for entry in json.loads(frozen)["files"]:
        if entry["module"].startswith(("PA213.", "PA213PA.")) or entry["path"] in overlays:
            assert hashlib.sha256((ROOT / entry["path"]).read_bytes()).hexdigest() == entry["sha256"], entry["path"]
            count += 1
    assert count == 519
    print("PASS: PA213's 426 rows, 213 controls, 3,947 source sites, and 519 reviewed modules.")


if __name__ == "__main__":
    main()
