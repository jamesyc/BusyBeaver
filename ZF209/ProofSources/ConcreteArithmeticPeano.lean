module
public import ConcreteArithmeticPeanoMinus
public import ConcreteArithmeticInduction
public import ConcreteZfrPredicateTranslation
@[expose] public section
namespace ZF209.OmegaInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "A" => arithmeticTranslation.Model V
instance omega_models_peano : A↓[ℒₒᵣ] ⊧* 𝗣𝗔 := by
 apply models_theory_iff.mpr
 intro φ hφ
 rcases hφ with h|h
 · exact models_theory_iff.mp (omega_models_peanoMinus (V := V)) φ h
 · exact models_theory_iff.mp (models_arithmetic_induction (V := V)) φ h
/-- The exact source verifier is now interpreted in a proved PA model.
No proof-code translation or Goedel-II conclusion is assumed here. -/
theorem sourceRefutation_internal_model :
 V↓[ℒₛₑₜ] ⊧ sourceRefutationInZF ↔
 ZFR.ArithmeticRepresentation.modelTheoryProof
   (ZFR.ArithmeticRepresentation.modelZfrAxiom (M := A)) (0 : A) := by
 have h := sourceRefutation_translation_exact (V := V)
 rw [interpreted_structure_eq_standard (V := V)] at h
 refine h.trans ?_
 simp only [models_iff,Semiformula.eval_substs]
 simpa using (ZFR.ArithmeticRepresentation.explicitZfrProvabilityFormula_defined (M := A)).iff (v := ![0])
end ZF209.OmegaInterpretation
