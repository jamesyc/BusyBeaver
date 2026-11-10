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

ENDPOINT = "User211LiteralEndpoint"
INDEPENDENCE = "PA211PA.TwoSidedIndependence"
PA211_BASELINE_SHA256 = "7adf9362e4e2b1fdc0af633dd7fd08a22747f553a778c5574a6f8acf6a03a85b"


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
    baseline = {name: record["sha256"] for name, record in manifest["files"].items()
                if record.get("pa211_baseline")}
    encoded = json.dumps(baseline, sort_keys=True, separators=(",", ":")).encode()
    if hashlib.sha256(encoded).hexdigest() != PA211_BASELINE_SHA256:
        raise ValueError("The 395-module PA211 source baseline differs from its pinned hash")
    for name, record in manifest["files"].items():
        checked_file(ROOT, name, record["sha256"])
        if "lean_program_sha256" in record:
            if lean_program_sha256((ROOT / name).read_text()) != record["lean_program_sha256"]:
                raise ValueError(f"Lean program differs from its recorded source: {name}")
    lean = ROOT / "Lean"
    for package, expected in ((lean, {"PA211"}),
                              (lean / "metamathematics", {"PA211PA"})):
        config = (package / "lakefile.toml").read_text()
        targets = re.search(r"^defaultTargets = (\[[^\n]*\])$", config, re.M)
        if targets is None or set(json.loads(targets.group(1))) != expected:
            raise ValueError(f"Default target must be PA211: {package}")
    roots = {"PA215PA": lean / "metamathematics", "PA213PA": lean / "metamathematics",
             "PA211PA": lean / "metamathematics"}
    closure = set(build_order(lean, "PA211PA", roots))
    if ENDPOINT not in closure:
        raise ValueError(f"Default root does not expose {ENDPOINT}")
    if INDEPENDENCE not in closure:
        raise ValueError(f"Default root does not expose {INDEPENDENCE}")
    closure.update(build_order(lean, "PA211"))
    sources = {"PA211", "PA211PA", "TreeSite"}
    for base, namespaces in ((lean, ("PA211", "PA213", "PA215")),
                             (lean / "metamathematics", ("PA211PA", "PA213PA", "PA215PA"))):
        sources.update(p.stem for p in base.glob("User211*.lean"))
        for namespace in namespaces:
            sources.update(".".join(p.relative_to(base).with_suffix("").parts)
                           for p in (base / namespace).rglob("*.lean"))
    if sources != closure:
        raise ValueError(f"Proof sources outside the PA211 closure: {sorted(sources - closure)}")
    for obsolete in ("Lean/PA213.lean", "Lean/metamathematics/PA213PA.lean",
                     "Lean/data/pa213.tm", "docs/pa213-independence.tex",
                     "docs/pa213-independence.pdf", "evidence/pa213"):
        if (ROOT / obsolete).exists():
            raise ValueError(f"Obsolete publication artifact: {obsolete}")
    expected_axioms = {
        "PA211.UserCandidate.PA.literal_final_endpoint",
        "PA211.UserCandidate.PA.consistent_literal_nonhalting",
        "PA211.UserCandidate.PA.InternalUnprovability.nonhalting_true",
        "PA211.UserCandidate.PA.InternalUnprovability.pa_proves_nonhalting_consistency",
        "PA211.UserCandidate.PA.InternalUnprovability.nonhalting_unprovable",
        "PA211.UserCandidate.PA.literal_arithmetic_binding",
        "PA211.UserCandidate.PA.Independence.nonhalting_irrefutable",
        "PA211.UserCandidate.PA.Independence.two_sided_independence",
        "PA211.UserCandidate.PA.Independence.machine_nonhalting",
    }
    audit = (lean / "metamathematics/Audit.lean").read_text()
    if set(re.findall(r"^#print axioms (\S+)$", audit, re.M)) != expected_axioms:
        raise ValueError("The final axiom audit must name all nine PA211 roots")
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
          f"PA211 dependency modules, "
          "and publication documentation links.")


if __name__ == "__main__":
    main()
