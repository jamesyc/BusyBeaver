"""Confirm that Lean reported only standard axioms for every audit target."""

import re
import sys
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
audit = Path(__file__).resolve().parents[1] / "Audit.lean"
expected = set(re.findall(r"^#print axioms (\S+)$", audit.read_text(), re.MULTILINE))
output = sys.stdin.read()
print(output, end="")
reported = re.findall(
    r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$",
    output,
    re.MULTILINE,
)
for name, listing in reported:
    unexpected = {axiom.strip() for axiom in listing.split(",") if axiom.strip()} - ALLOWED
    if unexpected:
        raise SystemExit(f"Unexpected axioms on {name}: {sorted(unexpected)}")
if {name for name, _ in reported} != expected:
    raise SystemExit("Lean did not report every audited declaration")
