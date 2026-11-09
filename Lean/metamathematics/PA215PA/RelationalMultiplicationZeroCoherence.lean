module

public import PA215PA.RelationalMultiplicationZeroLaw
public import PA215PA.RelationalOrderIsoZero
public import PA215PA.RelationalZeroIso

@[expose] public section

/-! Zero multiplication outputs are genuinely empty, hence isomorphic without
choosing or identifying a canonical empty object. -/
namespace PA215.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] orderIso mulResult

def multiplicationZeroCoherence {Γ : List Form} (E : FormulaEquality Γ)
    (x y b c r s : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar x)))
    (hxy : ND.Proof Γ (orderIso (.fvar x) (.fvar y)))
    (hr : ND.Proof Γ (mulResult (.fvar x) (.fvar b) (.fvar r)))
    (hs : ND.Proof Γ (mulResult (.fvar y) (.fvar c) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) :=
  zeroOrderIso E r s (mulResultZeroOutput E x b r hz hr)
    (mulResultZeroOutput E y c s (orderIsoZeroForward x y hz hxy) hs)

#print axioms multiplicationZeroCoherence
end PA215.PA.RelationalSource.PairGraph
