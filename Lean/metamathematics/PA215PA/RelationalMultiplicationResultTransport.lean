import PA215PA.RelationalMultiplicationCompactSyntax
import PA215PA.RelationalMultiplicationTrace
namespace PA215.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
set_option maxHeartbeats 600000
attribute [local irreducible] addResult addPrefix mulPrefix

def mulAddTargetTransport {Γ : List Form} (E : FormulaEquality Γ) (a base b c : Nat)
    (hbc : ND.Proof Γ (eq (.fvar b) (.fvar c)))
    (hs : ND.Proof Γ (addResult (.fvar a) (.fvar base) (.fvar b))) :
    ND.Proof Γ (addResult (.fvar a) (.fvar base) (.fvar c)) := by
  have hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![.fvar b]) (addResult (.fvar a) (.fvar base) (.bvar 0))) := by
    convert hs using 1 ; mulCompactSyntax
  have out := E.substituteOne (addResult (.fvar a) (.fvar base) (.bvar 0)) (.fvar b) (.fvar c) hbc hp
  convert out using 1 ; mulCompactSyntax

#print axioms mulAddTargetTransport

end PA215.PA.RelationalSource.PairGraph
