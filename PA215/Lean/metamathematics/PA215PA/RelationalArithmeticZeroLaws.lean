import PA215PA.RelationalAdditionZeroLaw
import PA215PA.RelationalMultiplicationZeroLaw
import PA215PA.RelationalOrderIsoTransport
import PA215PA.RelationalZeroIso

/-! The two arithmetic zero equations in the interpreted equality relation.
No arbitrary empty representative is identified by raw equality. -/
namespace PA215.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def additionZeroLawIso {Γ : List Form} (E : FormulaEquality Γ) (x b out : Nat)
    (hidentity : ND.Proof Γ identityStatement)
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hz : ND.Proof Γ (Ordinal.zero (.fvar x)))
    (hp : ND.Proof Γ (addResult (.fvar x) (.fvar b) (.fvar out))) :
    ND.Proof Γ (orderIso (.fvar out) (.fvar b)) :=
  orderIsoLeftTransport E b out b (E.symmetryOf (addResultZeroOutput E x b out hz hp))
    (orderIsoFromExists E b (identityAt b hidentity hb))

def multiplicationZeroLawIso {Γ : List Form} (E : FormulaEquality Γ) (x b out z : Nat)
    (hx : ND.Proof Γ (Ordinal.zero (.fvar x)))
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (mulResult (.fvar x) (.fvar b) (.fvar out))) :
    ND.Proof Γ (orderIso (.fvar out) (.fvar z)) :=
  zeroOrderIso E out z (mulResultZeroOutput E x b out hx hp) hz

#print axioms additionZeroLawIso
#print axioms multiplicationZeroLawIso
end PA215.PA.RelationalSource.PairGraph
