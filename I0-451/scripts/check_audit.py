"""Require an axiom report for every audited declaration and the compared theorem."""
import json
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parents[1]
expected = set(re.findall(r"^#print axioms (\S+)$", (root / "Audit.lean").read_text(), re.M))
config = json.loads((root / "comparator.json").read_text())
assert set(config["theorem_names"] + config.get("definition_names", [])) <= expected
allowed = {"propext", "Quot.sound", "Classical.choice"}
output = sys.stdin.read()
print(output, end="")
for name in sorted(expected):
    match = re.search(rf"^'{re.escape(name)}' (?:depends on axioms: \[([^\]]*)\]|"
                      r"does not depend on any axioms)$", output, re.M)
    assert match, f"Missing axiom report: {name}"
    found = {name.strip() for name in match[1].split(",")} if match[1] else set()
    assert found <= allowed, f"{name} uses {found - allowed}"
