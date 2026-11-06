#!/usr/bin/env python3
"""Check the actual transitive axiom report for every explicitly audited root.

This consumes Lean's #print axioms output, not source-token guesses. It does not
check that the chosen theorem statements express the intended mathematics.
"""
from pathlib import Path
import re
import subprocess
import sys

ALLOWED = frozenset({'propext', 'Classical.choice', 'Quot.sound'})

def validate_report(expected, report):
    found = {}
    for name, deps in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", report):
        if name in found:
            raise ValueError(f'duplicate axiom report: {name}')
        found[name] = frozenset(x.strip() for x in deps.split(',') if x.strip())
    for name in re.findall(r"'([^']+)' does not depend on any axioms", report):
        if name in found:
            raise ValueError(f'duplicate axiom report: {name}')
        found[name] = frozenset()
    missing = set(expected) - found.keys()
    if missing:
        raise ValueError(f'missing reports: {sorted(missing)}')
    unexpected = found.keys() - set(expected)
    if unexpected:
        raise ValueError(f'unexpected reports: {sorted(unexpected)}')
    for name, deps in found.items():
        if deps - ALLOWED:
            raise ValueError(f'unapproved axioms for {name}: {sorted(deps - ALLOWED)}')
    return found

def main():
    root = Path(__file__).resolve().parents[1]
    audit = root / 'Audit.lean'
    expected = re.findall(r'^#print axioms\s+(\S+)\s*$', audit.read_text(), re.M)
    if not expected or len(expected) != len(set(expected)):
        raise SystemExit('Audit.lean must name distinct explicit theorem roots.')
    result = subprocess.run(['lake', 'env', 'lean', str(audit)], cwd=root,
                            capture_output=True, text=True)
    print(result.stdout, end='')
    print(result.stderr, end='', file=sys.stderr)
    if result.returncode:
        raise SystemExit(result.returncode)
    try:
        validate_report(expected, result.stdout)
    except ValueError as error:
        raise SystemExit(str(error))
    print(f'PASS: all {len(expected)} audited roots use only the declared standard axioms.')

if __name__ == '__main__':
    main()
