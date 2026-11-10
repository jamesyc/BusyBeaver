import PA215PA.RelationalMultiplicationInductionStep
namespace PA215.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

/-- Fixed-base induction: additive totality and the distinct multiplicative
Separation instance are both explicit premises. -/
def mulPrefixTotal {Γ : List Form} (S : SetProofs Γ) (base : Nat)
    (hadd : ND.Proof Γ (addOutputConclusion base))
    (hsep : ND.Proof Γ (separationFormula (∼mulPrefixProperty base))) :
    ND.Proof Γ (Ordinal.inductionConclusion (mulPrefixProperty base)) :=
  Ordinal.uniformInduction S.equality.core (mulPrefixProperty base) S.equality.transitive
    S.intersection S.adjunction hsep (mulPrefixInductionBase S base) (mulPrefixInductionStep S base hadd)

#print axioms mulPrefixTotal
end PA215.PA.RelationalSource.PairGraph
