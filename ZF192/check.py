"""Source preflight; --audit checks Lean's output, not a substitute for Comparator."""

import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MACHINE_SHA256 = "be1db915a6f40e37a601d3cb54bc0cf0d9597bdf0c75e97098cf4c201c6d5585"
SOURCE_SHA256 = "8c258c075daf5e37cea26129d4273b5c1dd12cd4e9d8fc206dde6704bd5f9771"
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
    for directory in ("ProofSources", "Support", "Vendor"):
        for path in (ROOT / directory).rglob("*.lean"):
            name = ".".join(path.relative_to(ROOT / directory).with_suffix("").parts)
            require(name not in paths, f"Duplicate module: {name}")
            paths[name] = path
    paths["Audit"] = ROOT / "Audit.lean"
    imports, owned_lines = {}, 0
    for name, path in paths.items():
        require(not path.is_symlink(), f"Lean symlink: {path}")
        raw = path.read_bytes()
        lines = raw.splitlines()
        if not path.is_relative_to(ROOT / "Vendor"):
            owned_lines += len(lines)
        require(len(lines) <= 10_000, f"Over 10,000 lines: {path}")
        code = code_only(raw.decode())
        require(re.match(r"\s*module\b", code), f"Missing module header: {path}")
        imports[name] = [i for line in IMPORT.findall(code) for i in line.split()]
        markers = FORBIDDEN.findall(code)
        require(markers == (["sorry", "sorry"] if name == "ZF192.Challenge" else []),
                f"Unexpected proof escape in {path}: {markers}")
    require(owned_lines < 100_000,
            f"ZF192 has {owned_lines:,} project Lean lines (limit: under 100,000)")
    challenge = paths["ZF192.Challenge"].read_bytes()
    require(len(challenge) <= 100 * 1024 and len(challenge.splitlines()) <= 1_000,
            "Challenge exceeds Palomar limits")
    require(imports["ZF192.Challenge"] == ["Std"], "Unexpected Challenge imports")
    visited, todo = set(), ["ZF192.Solution"]
    while todo:
        name = todo.pop()
        if name in visited:
            continue
        visited.add(name)
        if name in imports:
            todo.extend(imports[name])
        else:
            require(name.split(".")[0] in {"Mathlib", "Std", "Lean", "Init", "Aesop"},
                    f"Unresolved import: {name}")
    require("ZF192.Challenge" not in visited, "Solution imports the Challenge placeholder")
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
    machine = (ROOT / "data/zf192.tm").read_bytes()
    require(hashlib.sha256(machine).hexdigest() == MACHINE_SHA256, "ZF192 machine bytes changed")
    rows = [line.split() for line in machine.decode().splitlines()]
    encoded = re.findall(r"some \((true|false), (true|false), (\d+)\)",
                         challenge.decode().split("def literalRows", 1)[1].split("]", 1)[0])
    expected = [("true" if w == "1" else "false", "true" if d == "R" else "false", t)
                for q, b, w, d, t in rows]
    require([(int(q), int(b)) for q, b, _, _, _ in rows] ==
            [(q, b) for q in range(192) for b in range(2)], "Invalid transition keys")
    require(len(rows) == 384 and encoded == expected, "Challenge table differs from the exact machine")
    literal = paths["ZF192.Machine.Literal"].read_text().split("def literal :")[0]
    require(re.findall(r"some \((true|false), (true|false), (\d+)\)", literal) == expected,
            "Solution table differs from the exact machine")
    check_source_data(paths["ZF192.Machine.Decoder.SourceData"])
    paper_path = ROOT / "paper/zf192.tex"
    if paper_path.is_file():
        # The two parts of the appendix each have three 32-row groups.
        paper = paper_path.read_text().split(r"\section{Complete transition table}", 1)[1]
        paper_rows = re.findall(r"\$\(([01]),\\mathsf\{([LR])\},(\d+)\)\$", paper)
        order = [q for start in (0, 96) for i in range(32)
                 for group in range(3) for q in [start + group * 32 + i]]
        require(paper_rows == [tuple(rows[2*q+b][2:]) for q in order for b in (0, 1)],
                "Paper table differs from the exact machine")
    config = json.loads((ROOT / "comparator.json").read_text())
    require(config["challenge_module"] == "ZF192.Challenge" and config["solution_module"] == "ZF192.Solution",
            "Unexpected Comparator modules")
    require(config["theorem_names"] == ["PalomarZF192.exact192Claim", "PalomarZF192.nonhalting_of_consistent"],
            "Compared declarations changed")
    require(set(config["permitted_axioms"]) == AXIOMS, "Unexpected permitted axioms")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        require(package["type"] == "git" and re.fullmatch(r"[0-9a-f]{40}", package["rev"]) and
                re.fullmatch(r"https://github\.com/[\w.-]+/[\w.-]+", package["url"]),
                f"Unexpected external dependency: {package['name']}")
    print(f"PASS: {len(paths)} Lean files scanned; {owned_lines:,} project Lean lines; "
          f"{len(visited & paths.keys())} local Solution imports; "
          f"{len(hashes) - len(patches)} original Foundation hashes, {len(patches)} documented patches "
          f"and {len(imported)} PA196 Foundation imports; "
          "all 384 machine rows.")
    print("PASS: only the two deliberate Challenge placeholders; Solution excludes Challenge.")
    print("Source checks do not establish compilation, axiom closure, Comparator, or NanoDa success.")


def check_source_data(path):
    raw = (ROOT / "data/source.json").read_bytes()
    require(hashlib.sha256(raw).hexdigest() == SOURCE_SHA256, "Contextual source input changed")
    source = json.loads(raw)
    removed = set(source["removed"])
    entries = re.findall(r"\((0x[0-9a-f]+|0), (none|some \.halt|some \(\.[a-z]+(?: \d+)+\))\)",
                         path.read_text())
    expected = []
    for pc, ((address, _), instruction) in enumerate(zip(source["sites"], source["cfg"], strict=True)):
        if pc in removed:
            expected.append(("0", "none"))
        else:
            word = (1 << len(address)) | sum(int(bit) << i for i, bit in enumerate(address))
            opcode, *operands = instruction
            row = "some .halt" if opcode == "halt" else f"some (.{opcode} {' '.join(map(str, operands))})"
            expected.append((hex(word), row))
    require(entries == expected, "Lean contextual source data differs from the retained input")

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
    print(f"PASS: {len(expected)} ZF192 declarations have only permitted axioms.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit", type=Path)
    args = parser.parse_args()
    if args.audit:
        audit(args.audit)
    else:
        preflight()
