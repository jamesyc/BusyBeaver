#!/usr/bin/env python3
"""Bind the published PA211 table and source to their literal Lean definitions."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def source_sites(text):
    """Parse the frozen tree declarations independently of Lean's resolver."""
    nodes = {}
    operations = {"inc": "EInc", "dec": "EDecnz", "breakTo": "EBreak",
                  "continueTo": "EContinue", "halt": "EHalt"}
    for name, expression in re.findall(r"^private def (node\d+) : Tree := (.+)$", text, re.M):
        tokens = iter(re.findall(r"\.\w+|node\d+|\d+|[()]", expression))

        def parse():
            token = next(tokens)
            if token == "(":
                value = parse()
                assert next(tokens) == ")"
                return value
            if token == ".node":
                return (parse(), parse())
            if token == ".leaf":
                value = parse()
                assert isinstance(value, list)
                return value
            if token.startswith("."):
                operation = token[1:]
                return [operations[operation], None if operation == "halt" else int(next(tokens))]
            return nodes[token]

        nodes[name] = parse()
        assert next(tokens, None) is None, name
    assert len(nodes) == 173
    root = re.search(r"^def trie : Tree := (node\d+)$", text, re.M).group(1)
    sites = []

    def walk(node, path):
        if isinstance(node, list):
            sites.append([path, node])
        else:
            walk(node[0], path + "0")
            walk(node[1], path + "1")

    walk(nodes[root], "")
    return sites


def check_inputs(root):
    raw = (root / "data/pa211.tm").read_bytes()
    assert hashlib.sha256(raw).hexdigest() == (
        "fd986dc8cb7f30c3d9f6e4a1767e3335f06679aeadeedb8d1d7fecd442f232c3")
    rows = []
    for line in raw.decode("ascii").splitlines():
        if line.startswith("#"):
            continue
        q, b, w, direction, target = line.split()
        assert direction in ("L", "R")
        assert b in ("0", "1") and w in ("0", "1")
        rows.append((int(q), b == "1", w == "1", direction == "R", int(target)))
    active = set(range(215)) - {122, 150, 205, 214}
    assert len(rows) == 422
    assert {(q, b) for q, b, *_ in rows} == {
        (q, b) for q in active for b in (False, True)}
    assert all(target in active | {215} for *_, target in rows)
    pattern = r"\| (\d+), (false|true) => some \((false|true), (false|true), (\d+)\)"

    def parsed_table(text):
        return [(int(q), b == "true", w == "true", d == "true", int(t))
                for q, b, w, d, t in re.findall(pattern, text)]

    base = root / "PA211/UserCandidate"
    literal = parsed_table((base / "Dense.lean").read_text())
    assert literal == rows, "Literal table differs"
    candidate = (base / "CandidateTable.lean").read_text()
    labels = json.loads(re.search(r"def denseLabels : List Nat := (\[[^\n]+\])",
                                 candidate).group(1))
    assert len(labels) == 215 and len(set(labels)) == 215
    working = json.loads(re.search(r"def workingDense : List Nat := (\[[^\n]+\])",
                                  candidate).group(1))
    assert len(working) == 211 and set(working) == active
    label = labels + [254]
    assert label[0] == 74 and label[215] == 254
    physical = parsed_table(candidate)
    assert len(physical) == 422
    assert set(physical) == {
        (label[q], b, w, d, label[t]) for q, b, w, d, t in rows}, "Physical table differs"
    dense = (root / "metamathematics/User211PAMachine.lean").read_text()
    row_pattern = (r"\| (\d+) => if b then ⟨(true|false), (true|false), target (\d+)⟩"
                   r" else ⟨(true|false), (true|false), target (\d+)⟩")
    auxiliary = []
    for q, w1, d1, t1, w0, d0, t0 in re.findall(row_pattern, dense):
        auxiliary.extend([(int(q), False, w0 == "true", d0 == "true", int(t0)),
                          (int(q), True, w1 == "true", d1 == "true", int(t1))])
    assert len(auxiliary) == 430
    assert [row for row in auxiliary if row[0] in active] == rows, "Arithmetic table differs"
    assert all(q == t for q, _, _, _, t in auxiliary if q not in active)
    source = (root / "data/candidate_source.json").read_bytes()
    assert hashlib.sha256(source).hexdigest() == (
        "d7f77b32dbc6546c5015c6a596044506060e534def3d04cf8bcd49811161c36b")
    parsed = source_sites((root / "User211Source.lean").read_text())
    assert len(parsed) == 3947 and parsed == json.loads(source), "Source sites differ"


def main():
    check_inputs(ROOT)
    print("PASS: PA211's 422 rows, 211 controls, and 3,947 source sites.")


if __name__ == "__main__":
    main()
