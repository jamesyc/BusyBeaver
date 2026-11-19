module
public import ExactFixedAxiomFormula
public import ExactSourceBoundEquations
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma modelFixedFormula_bound (f : Formula) (n : Nat) (hf : Bound f n) :
 modelSourceBound (n:M) (modelFixedFormula f) := by
 induction f generalizing n with
 | bot => exact modelSourceBound_zero _
 | mem i j =>
  apply (modelSourceBound_atomic _ _ _ _ (Or.inl rfl)).mpr
  exact ⟨model_natCast_lt hf.1,model_natCast_lt hf.2⟩
 | eq i j =>
  apply (modelSourceBound_atomic _ _ _ _ (Or.inr rfl)).mpr
  exact ⟨model_natCast_lt hf.1,model_natCast_lt hf.2⟩
 | and a b ia ib =>
  apply (modelSourceBound_binary _ _ _ _ (Or.inl rfl)).mpr
  exact ⟨ia n hf.1,ib n hf.2⟩
 | or a b ia ib =>
  apply (modelSourceBound_binary _ _ _ _ (Or.inr (Or.inl rfl))).mpr
  exact ⟨ia n hf.1,ib n hf.2⟩
 | imp a b ia ib =>
  apply (modelSourceBound_binary _ _ _ _ (Or.inr (Or.inr rfl))).mpr
  exact ⟨ia n hf.1,ib n hf.2⟩
 | all a ia =>
  apply (modelSourceBound_binder _ _ _ (Or.inl rfl)).mpr
  simpa using ia (n+1) hf
 | ex a ia =>
  apply (modelSourceBound_binder _ _ _ (Or.inr rfl)).mpr
  simpa using ia (n+1) hf
lemma fixedAxiomList_closed (f : Formula) (hf : f∈fixedAxiomList) : Bound f 0 := by
 have hx : sourceZfrFixed (encodeFormula f) := by
  apply (fixedAxiomFormula_nat _).mp
  apply (fixedFormulaListGraph_eval _ _).mpr
  exact ⟨f,hf,(modelFixedFormula_nat f).symm⟩
 exact (sourceBound_encode f 0).mp (sourceZfrFixed_closed hx)
lemma modelFixedAxiom_closed (z : M) (hz : modelFixedAxiom z) : modelSourceBound 0 z := by
 obtain ⟨f,hf,rfl⟩ := hz
 exact modelFixedFormula_bound f 0 (fixedAxiomList_closed f hf)
end ZFR.ArithmeticRepresentation
