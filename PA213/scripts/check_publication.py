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

ENDPOINT = "PA213PA.NonhaltingUnprovability"
INDEPENDENCE = "PA213PA.TwoSidedIndependence"


def checked_file(root, name, expected):
    path = (root / name).resolve()
    if not path.is_relative_to(root.resolve()) or not path.is_file():
        raise ValueError(f"Missing or out-of-tree file: {name}")
    if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise ValueError(f"SHA256 mismatch: {name}")


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
    for package, expected in ((lean, {"PA213"}),
                              (lean / "metamathematics", {"PA213PA"})):
        config = (package / "lakefile.toml").read_text()
        targets = re.search(r"^defaultTargets = (\[[^\n]*\])$", config, re.M)
        if targets is None or set(json.loads(targets.group(1))) != expected:
            raise ValueError(f"Default target must be PA213: {package}")
    roots = {"PA215PA": lean / "metamathematics", "PA213PA": lean / "metamathematics"}
    closure = set(build_order(lean, "PA213PA", roots))
    if ENDPOINT not in closure:
        raise ValueError(f"Default root does not expose {ENDPOINT}")
    if INDEPENDENCE not in closure:
        raise ValueError(f"Default root does not expose {INDEPENDENCE}")
    closure.update(build_order(lean, "PA213"))
    expected_axioms = {
        "PA213.PA.consistent_machine_nonhalting",
        "PA213.PA.InternalUnprovability.nonhalting_true",
        "PA213.PA.InternalUnprovability.pa_proves_nonhalting_consistency",
        "PA213.PA.InternalUnprovability.nonhalting_unprovable",
        "PA213.PA.InternalUnprovability.final_endpoint",
        "PA213.PA.Independence.nonhalting_irrefutable",
        "PA213.PA.Independence.two_sided_independence",
        "PA213.PA.Independence.machine_nonhalting",
    }
    audit = (lean / "metamathematics/Audit.lean").read_text()
    if set(re.findall(r"^#print axioms (\S+)$", audit, re.M)) != expected_axioms:
        raise ValueError("The final axiom audit must name the five original PA213 roots and the three independence roots")
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
          f"PA213 dependency modules, "
          "and publication documentation links.")


if __name__ == "__main__":
    main()
