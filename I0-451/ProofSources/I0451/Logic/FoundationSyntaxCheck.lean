module
public import I0451.Commands.ExtraMeaning

/-! The literal Foundation formula uses the sentinel code for
falsity and has no other syntactically diagonal membership atom. -/
@[expose] public section
namespace I0451.Logic

open I0451.Runtime

/-- The sentinel atom at label zero represents logical falsity.
An emitted formula with no other diagonal atom admits the same
normalization proof in an arbitrary membership structure. -/
def sentinelOnly : Formula → Bool
  | .truth | .equal _ _ => true
  | .mem a b => decide (a ≠ b ∨ a = 0)
  | .imp p q => sentinelOnly p && sentinelOnly q
  | .all _ p => sentinelOnly p

set_option maxRecDepth 16000 in
theorem literal_foundation_sentinel :
    literalFoundationTerm.toFormula.any sentinelOnly = true := by decide +kernel

end I0451.Logic
