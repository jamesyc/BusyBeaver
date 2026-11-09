module

public import PA215PA.RelationalMultiplicationCoherenceStepFrame

@[expose] public section

/-! The full universally parameterized successor step, without any parameter
freshness assumption or a fixed second input. -/
namespace PA215.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] mulResult orderIso Ordinal.domain
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

def mulCoherenceSuccessor {Γ : List Form} (p x : Nat)
    (I : MultiplicationCoherenceStepFrame Γ p x) :
    ND.Proof Γ (mulCoherence (.fvar x)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  apply allIntro
  apply allIntro
  have out := mulCoherenceSuccessorPoint (p+1+1+1+1+1) (x+1+1+1+1+1) 4 3 2 1 0
    I.shift.shift.shift.shift.shift
  convert out using 1 <;> mulCoherenceSyntax

#print axioms mulCoherenceSuccessor
end PA215.PA.RelationalSource.PairGraph
