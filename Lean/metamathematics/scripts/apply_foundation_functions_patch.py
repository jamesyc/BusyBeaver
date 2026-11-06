#!/usr/bin/env python3
"""Apply the exact TermSubst proof-only upstream memory fix. Refuse unfamiliar bytes."""
from pathlib import Path
import hashlib

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / '.lake/packages/Foundation/Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Term/Functions.lean'
ORIGINAL = 'd79a08c80f3c9f86cfcea1f2c60b1d193b0df9a902be8d6a008cfa7d5aac16b7'
PATCHED = '2ce4186eda6c7f44fe283e44723582c19a4f216e7bc78e9333336b23a0aacb9d'
OLD = '  bvar_defined := .mk fun v ↦ by simp [blueprint]'
NEW = '''  bvar_defined := .mk fun v ↦ by
    simp only [blueprint, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    rw [Semiformula.eval_substs]
    simp [nth_defined.df]'''

def main():
    raw = TARGET.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest == PATCHED:
        print('Exact Foundation proof-only patch already present.')
        return
    if digest != ORIGINAL:
        raise SystemExit('Refusing unexpected Foundation source bytes.')
    text = raw.decode()
    if text.count(OLD) != 3:
        raise SystemExit('Refusing unexpected proof replacement count.')
    result = text.replace(OLD, NEW, 1).encode()
    if hashlib.sha256(result).hexdigest() != PATCHED:
        raise SystemExit('Replacement failed the exact output hash check.')
    TARGET.write_bytes(result)
    print('Applied the exact Foundation proof-only memory patch; build still required.')

if __name__ == '__main__':
    main()
