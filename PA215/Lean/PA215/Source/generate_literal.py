#!/usr/bin/env python3
"""Untrusted data transcription/check: never a mathematical proof checker."""
import argparse
import hashlib
import json
from pathlib import Path

DIGEST = "e4814e0d968b86a8cd4cf2df2623b2f5558a7a61bf43b99f798c73156eb91c45"


def render(raw):
    if hashlib.sha256(raw).hexdigest() != DIGEST:
        raise ValueError("wrong exact source JSON identity")
    sites = json.loads(raw)
    if len(sites) != 3947:
        raise ValueError("wrong source count")
    out = ["import PA215.Source.Syntax", "set_option maxHeartbeats 8000000",
           "set_option maxRecDepth 50000", "",
           "/-! Literal 3947 source leaves transcribed from the published reconstructed source.",
           f"Original JSON SHA256: {DIGEST}.",
           "This data definition is not a source-correctness theorem. -/",
           "namespace PA215.Source", "", "def exactSites : Array Site := #["]
    tags = {"EInc": ".inc", "EDecnz": ".dec", "EBreak": ".breakTo",
            "EContinue": ".continueTo", "EHalt": ".halt"}
    paths = []
    for path, (tag, arg) in sites:
        if not path or any(c not in "01" for c in path) or tag not in tags:
            raise ValueError("malformed site")
        if tag in ("EInc", "EDecnz") and not (type(arg) is int and 0 <= arg < 9):
            raise ValueError("bad register")
        if tag in ("EBreak", "EContinue") and not (type(arg) is int and arg > 0):
            raise ValueError("bad jump depth")
        paths.append(path)
        bits = "[" + ",".join("true" if c == "1" else "false" for c in path) + "]"
        op = tags[tag] + (" " + str(arg) if tag != "EHalt" else "")
        out.append(f"  ⟨{bits}, {op}⟩,")
    if paths != sorted(set(paths)):
        raise ValueError("duplicate or unordered source paths")
    out[-1] = out[-1].rstrip(",")
    out += ["]", "", "theorem exactSites_count : exactSites.size = 3947 := by decide",
            "", "end PA215.Source", ""]
    return "\n".join(out).encode()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("source_json", type=Path)
    p.add_argument("--output", type=Path, default=Path(__file__).with_name("ExactSource.lean"))
    p.add_argument("--write", action="store_true", help="write generated Lean; default verifies only")
    a = p.parse_args()
    expected = render(a.source_json.read_bytes())
    if a.write:
        a.output.write_bytes(expected)
    elif a.output.read_bytes() != expected:
        raise SystemExit("Lean literal differs from exact source transcription")
    print("Exact 3947-site transcription matches; no mathematical proof is asserted.")


if __name__ == "__main__":
    main()
