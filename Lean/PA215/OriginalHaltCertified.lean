import PA215.OriginalCensus
import PA215.HaltContracts
set_option maxRecDepth 100000
namespace PA215.Census
attribute [local irreducible] originalAt

/-- The exact terminal obligation is kept separate from nonterminal progress. -/
structure OriginalHaltCertified (i : Fin 5134) where
  target_none : (originalAt i).target = none
  halt_flag : (originalAt i).isHalt = true
  fuel : Nat
  accepted : PA215.HaltContracts.check fuel (originalAt i).branch (originalAt i).initial = true

theorem OriginalHaltCertified.sound (c : OriginalHaltCertified i) (n : Nat) (vs : List Nat)
    (hv : PA215.Runtime.Valid (originalAt i).branch vs) :
    PA215.Zip.Halts PA215.NativeTable.machine (PA215.Runtime.conc n vs (originalAt i).initial) :=
  PA215.HaltContracts.sound c.fuel _ _ c.accepted n vs hv

end PA215.Census
