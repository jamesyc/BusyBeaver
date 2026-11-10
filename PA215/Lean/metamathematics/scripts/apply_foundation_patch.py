#!/usr/bin/env python3
"""Apply one exact, proof-only upstream memory fix. Refuse unfamiliar bytes."""
from pathlib import Path
import hashlib

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / '.lake/packages/Foundation/Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Term/Basic.lean'
ORIGINAL = '011d4e6c7d222628926ef327104ee6ef4dd683ed4a8447f8379a6752c61e78ec'
PATCHED = '6b700dc6ea4ea8d60bb17b7d681c46e1ac53ce52a37f5be5b84e4d033c5bb31e'
OLD = '  func_defined := .mk fun v ↦ by simp [blueprint]'
NEW = '''  func_defined := .mk fun v ↦ by
    simp only [blueprint, Bounding.HierarchySymbol.Semiformula.val_mkSigma]
    rw [Semiformula.eval_substs]
    simp [listMax_defined.df]'''

def main():
    raw = TARGET.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest == PATCHED:
        print('Exact Foundation proof-only patch already present.')
        return
    if digest != ORIGINAL:
        raise SystemExit('Refusing unexpected Foundation source bytes.')
    text = raw.decode()
    if text.count(OLD) != 1:
        raise SystemExit('Refusing unexpected proof replacement count.')
    result = text.replace(OLD, NEW).encode()
    if hashlib.sha256(result).hexdigest() != PATCHED:
        raise SystemExit('Replacement failed the exact output hash check.')
    TARGET.write_bytes(result)
    print('Applied the exact Foundation proof-only memory patch; build still required.')

if __name__ == '__main__':
    main()
