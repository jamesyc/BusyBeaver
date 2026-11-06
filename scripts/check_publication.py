#!/usr/bin/env python3
"""Publication integrity checks; not a proof checker."""
import hashlib
import json
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "Lean/scripts"))
from build_serial import build_order
from check_source_hygiene import without_comments

ENDPOINTS = (
    "PA215PA.MachineNonhaltingV2",
    "PA215PA.NonhaltingUnprovability",
)


def checked_file(root, name, expected):
    path = (root / name).resolve()
    if not path.is_relative_to(root.resolve()) or not path.is_file():
        raise ValueError(f"Missing or out-of-tree file: {name}")
    if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise ValueError(f"SHA256 mismatch: {name}")


def manifest_files(value):
    if isinstance(value, dict):
        if "path" in value and "sha256" in value:
            yield value["path"], value["sha256"]
        for child in value.values():
            yield from manifest_files(child)
    elif isinstance(value, list):
        for child in value:
            yield from manifest_files(child)


def lean_program_sha256(text):
    lines = without_comments(text).splitlines()
    program = "\n".join(line.rstrip() for line in lines if line.strip())
    return hashlib.sha256(program.encode()).hexdigest()


def main():
    manifest = json.loads((ROOT / "evidence/source-manifest.json").read_text())
    for name, record in manifest["files"].items():
        checked_file(ROOT, name, record["sha256"])
        if "lean_program_sha256" in record:
            if lean_program_sha256((ROOT / name).read_text()) != record["lean_program_sha256"]:
                raise ValueError(f"Lean program differs from its recorded source: {name}")
    lean = ROOT / "Lean"
    roots = {"PA215PA": lean / "metamathematics"}
    closure = set(build_order(lean, "PA215PA", roots))
    for endpoint in ENDPOINTS:
        if endpoint not in closure:
            raise ValueError(f"Default root does not expose {endpoint}")
        build_order(lean, endpoint, roots)
    # Also validate the standalone core audit's import root.
    build_order(lean, "PA215")
    references = 0
    for path in sorted((lean / "data").glob("*manifest.json")):
        for name, digest in manifest_files(json.loads(path.read_text())):
            checked_file(lean, name, digest)
            references += 1
    historical = json.loads((ROOT / "evidence/nonhalting/PROJECT_SOURCE_OUTPUT_IDENTITIES.json").read_text())
    for entry in historical["modules"]:
        module = entry["module"]
        base = lean / "metamathematics" if module.startswith("PA215PA.") else lean
        path = (base / (module.replace(".", "/") + ".lean")).relative_to(ROOT)
        record = manifest["files"][path.as_posix()]
        # The immutable build ledger identifies the source it actually checked.
        # Comment-edited modules additionally bind the original program text.
        digest = record["original_sha256"] if "lean_program_sha256" in record else record["sha256"]
        if digest != entry["source_sha256"]:
            raise ValueError(f"Nonhalting source ledger mismatch: {path}")
    expected_axioms = {
        "PA215.PA.CachedV2.consistent_machine_nonhalting",
        "PA215.PA.CachedV2.consistent_nonhalting_sentence",
        "PA215.PA.InternalUnprovability.pa_proves_nonhalting_consistency",
        "PA215.PA.InternalUnprovability.nonhalting_unprovable",
    }
    audit = (lean / "metamathematics/Audit.lean").read_text()
    if set(re.findall(r"^#print axioms (\S+)$", audit, re.M)) != expected_axioms:
        raise ValueError("The final axiom audit must name all four theorem roots")
    docs = {ROOT / name for name in manifest["files"] if name.endswith(".md")}
    docs.add(ROOT / "evidence/README.md")
    docs.update((ROOT / "docs").glob("*.md"))
    for doc in sorted(docs):
        for target in re.findall(r"\[[^\]]*\]\(([^\s)]+)\)", doc.read_text()):
            parsed = urlsplit(target)
            if parsed.scheme or not parsed.path:
                continue
            dest = (doc.parent / unquote(parsed.path)).resolve()
            if not dest.is_relative_to(ROOT) or not dest.exists():
                raise ValueError(f"Broken file link in {doc.relative_to(ROOT)}: {target}")
    print(f"PASS: {len(manifest['files'])} source identities, {len(closure)} "
          f"default-root local modules, {references} input-manifest references, "
          "and publication documentation links.")


if __name__ == "__main__":
    main()
