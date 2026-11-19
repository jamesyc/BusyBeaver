module
public import ExactZfrAxiomFormula
public import ExactTheoryProofFormula
public import ExactFixedAxiomClosed
public import ZfrCoreEndpoints
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
/-- Actual structural arithmetic syntax for exact ZFR provability, not an RE-code choice. -/
def explicitZfrProvabilityFormula : 𝚺ᴬ₁.Semisentence 1 := theoryProofFormula zfrAxiomFormula
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma explicitZfrProvabilityFormula_defined :
 𝚺ᴬ₁.DefinedPred (modelTheoryProof (modelZfrAxiom (M:=M))) explicitZfrProvabilityFormula :=
 theoryProofFormula_defined zfrAxiomFormula modelZfrAxiom zfrAxiomFormula_defined
lemma explicitZfrProvabilityFormula_nat (f : Nat) :
 explicitZfrProvabilityFormula.val.Evalb ![f] ↔ ZfrProvable f := by
 rw [explicitZfrProvabilityFormula,theoryProofFormula_nat zfrAxiomFormula modelZfrAxiom zfrAxiomFormula_defined]
 simp only [ZfrProvable,sourceTheoryProvable,modelZfrAxiom_nat]
lemma modelZfrAxiom_closed (z : M) (h : modelZfrAxiom z) : modelSourceBound 0 z := by
 rcases h with h|h|h
 · exact modelFixedAxiom_closed z h
 · exact h.1
 · exact h.1
end ZFR.ArithmeticRepresentation
