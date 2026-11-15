"""Source preflight; --audit checks Lean's output, not a substitute for Comparator."""

import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MACHINE_SHA256 = "6b8acf3cf8523e2c2db2020f69c19f7ced2b1343e1b09621697515ed54b6eabd"
SKIP = re.compile(r'/\-|--[^\n]*|"(?:[^"\\]|\\.)*"')
BLOCK = re.compile(r'/\-|-/')
IMPORT = re.compile(r"^(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([^\n]+)", re.M)
FORBIDDEN = re.compile(r"\b(?:sorry|admit|sorryAx|native_decide|ofReduceBool)\b|"
                       r"^\s*(?:(?:public|private|protected)\s+)*axiom\s", re.M)


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def code_only(text):
    """Mask comments (including nested ones) and strings for lexical checks."""
    parts, pos = [], 0
    while match := SKIP.search(text, pos):
        parts.append(text[pos:match.start()])
        end = match.end()
        if match[0] == "/-":
            depth = 1
            while depth:
                token = BLOCK.search(text, end)
                require(token is not None, "Unterminated Lean block comment")
                depth += 1 if token[0] == "/-" else -1
                end = token.end()
        parts.append(" " + "\n" * text[match.start():end].count("\n"))
        pos = end
    parts.append(text[pos:])
    return "".join(parts)


def preflight():
    paths = {}
    for directory in ("ProofSources", "Vendor"):
        for path in (ROOT / directory).rglob("*.lean"):
            name = ".".join(path.relative_to(ROOT / directory).with_suffix("").parts)
            require(name not in paths, f"Duplicate module: {name}")
            paths[name] = path
    paths["Audit"] = ROOT / "Audit.lean"
    imports, total_lines, total_bytes = {}, 0, 0
    for name, path in paths.items():
        require(not path.is_symlink(), f"Lean symlink: {path}")
        raw = path.read_bytes()
        lines = raw.splitlines()
        total_lines += len(lines)
        total_bytes += len(raw)
        require(len(lines) <= 10_000, f"Over 10,000 lines: {path}")
        code = code_only(raw.decode())
        require(re.match(r"\s*module\b", code), f"Missing module header: {path}")
        imports[name] = [i for line in IMPORT.findall(code) for i in line.split()]
        markers = FORBIDDEN.findall(code)
        require(markers == (["sorry"] if name == "Challenge" else []),
                f"Unexpected proof escape in {path}: {markers}")
    challenge = paths["Challenge"].read_bytes()
    require(len(challenge) <= 100 * 1024 and len(challenge.splitlines()) <= 1_000,
            "Challenge exceeds Palomar limits")
    require(imports["Challenge"] == ["Std"], "Unexpected Challenge imports")
    visited, todo = set(), ["Solution"]
    while todo:
        name = todo.pop()
        if name in visited:
            continue
        visited.add(name)
        if name in imports:
            todo.extend(imports[name])
        else:
            require(name.split(".")[0] in {"Mathlib", "Std", "Lean", "Aesop"},
                    f"Unresolved import: {name}")
    require("Challenge" not in visited, "Solution imports the Challenge placeholder")
    hashes = json.loads((ROOT / "VENDORED_FOUNDATION_HASHES.json").read_text())
    patches = json.loads((ROOT / "provenance/FOUNDATION_PATCHES.json").read_text())
    require(patches.keys() <= hashes.keys(), "Patch manifest names an unknown upstream file")
    for relative, digest in hashes.items():
        if relative in patches:
            require(patches[relative]["original_sha256"] == digest,
                    f"Patch changes the recorded upstream identity: {relative}")
            digest = patches[relative]["patched_sha256"]
        actual = hashlib.sha256((ROOT / "Vendor" / relative).read_bytes()).hexdigest()
        require(actual == digest, f"Foundation source hash mismatch: {relative}")
    imported = json.loads((ROOT / "provenance/FOUNDATION_FROM_PA196.json").read_text())["files"]
    require(not (imported.keys() & hashes.keys()), "A PA196 import duplicates an upstream entry")
    for relative, digest in imported.items():
        actual = hashlib.sha256((ROOT / "Vendor" / relative).read_bytes()).hexdigest()
        require(actual == digest, f"PA196 Foundation import hash mismatch: {relative}")
    listed = hashes.keys() | imported.keys()
    present = {str(p.relative_to(ROOT / "Vendor")) for p in (ROOT / "Vendor/Foundation").rglob("*.lean")}
    require(present == listed, f"Unrecorded or missing Foundation files: {sorted(present ^ listed)[:5]}")
    machine = (ROOT / "data/zf209.tm").read_bytes()
    require(hashlib.sha256(machine).hexdigest() == MACHINE_SHA256, "ZF209 machine bytes changed")
    rows = [line.split() for line in machine.decode().splitlines()]
    encoded = re.findall(r"some \((true|false), (true|false), (\d+)\)",
                         challenge.decode().split("section InternalSets")[0])
    expected = [("true" if w == "1" else "false", "true" if d == "R" else "false", t)
                for q, b, w, d, t in rows]
    require(len(rows) == 418 and encoded == expected, "Challenge table differs from the exact machine")
    config = json.loads((ROOT / "comparator.json").read_text())
    require(config["challenge_module"] == "Challenge" and config["solution_module"] == "Solution",
            "Unexpected Comparator modules")
    require(config["theorem_names"] == ["PalomarZF209.exact209Claim"], "Compared statement changed")
    require(set(config["permitted_axioms"]) == AXIOMS, "Unexpected permitted axioms")
    print(f"PASS: {len(paths)} Lean files, {total_lines:,} lines, {total_bytes:,} source bytes; "
          f"{len(visited & paths.keys())} local Solution imports; "
          f"{len(hashes) - len(patches)} original Foundation hashes, {len(patches)} documented patches "
          f"and {len(imported)} PA196 Foundation imports; "
          "all 418 machine rows.")
    print("PASS: only the deliberate Challenge placeholder; Solution excludes Challenge.")
    print("Source checks do not establish compilation, axiom closure, Comparator, or NanoDa success.")


def audit(path):
    output = path.read_text()
    expected = re.findall(r"^#print axioms (\S+)", (ROOT / "Audit.lean").read_text(), re.M)
    compared = json.loads((ROOT / "comparator.json").read_text())["theorem_names"]
    require(set(compared) <= set(expected), "Audit omits a compared theorem")
    for name in expected:
        result = re.search(rf"'{re.escape(name)}' (?:depends on axioms: \[([^]]*)\]|"
                           r"does not depend on any axioms)", output)
        require(result is not None, f"Missing axiom report for {name}")
        found = {a.strip() for a in result[1].split(",")} if result[1] else set()
        require(found <= AXIOMS, f"Unexpected axioms for {name}: {found - AXIOMS}")
    print(f"PASS: {len(expected)} ZF209 declarations have only permitted axioms.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit", type=Path)
    args = parser.parse_args()
    if args.audit:
        audit(args.audit)
    else:
        preflight()
