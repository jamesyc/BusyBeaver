module
public import ExactTheoryContextFormula
public import ExactFullTraceFormula
public import NumericTheory
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- A genuine arithmetic theory-proof formula, parameterized by actual axiom syntax. -/
def theoryProofFormula (ax : 𝚺ᴬ₁.Semisentence 1) : 𝚺ᴬ₁.Semisentence 1 := .mkSigma
 “f. ∃ g, ∃ p, ∃ r, !(theoryContextFormula ax) g ∧ !sequentGraph r g f ∧
 !fullTraceFormula p ∧ !memberFormula r p”
def modelTheoryProof (A : M → Prop) (f : M) :=
 ∃g p,modelTheoryContext A g ∧ modelTrace modelFullRules p ∧ modelMember (modelSequent g f) p
lemma theoryProofFormula_defined (ax : 𝚺ᴬ₁.Semisentence 1) (A : M → Prop)
 (hA : 𝚺ᴬ₁.DefinedPred A ax) :
 𝚺ᴬ₁.DefinedPred (modelTheoryProof A) (theoryProofFormula ax) := .mk (by
 intro v
 simp [theoryProofFormula,modelTheoryProof,Semiformula.eval_rew,Function.comp_def,
 Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,(theoryContextFormula_defined ax A hA).iff,
 sequentGraph_defined.iff,fullTraceFormula_defined.iff,memberFormula_defined.iff])
lemma theoryProofFormula_nat (ax : 𝚺ᴬ₁.Semisentence 1) (A : Nat → Prop)
 (hA : 𝚺ᴬ₁.DefinedPred A ax) (f : Nat) :
 (theoryProofFormula ax).val.Evalb ![f] ↔ sourceTheoryProvable A f := by
 have he : (theoryProofFormula ax).val.Evalb ![f] ↔ modelTheoryProof A f :=
  (theoryProofFormula_defined ax A hA).iff
 rw [he]
 have hr : (modelFullRules (M:=Nat))=sourceFullRules := by
  funext r xs; exact propext (modelFullRules_nat r xs)
 simp only [modelTheoryProof,modelTheoryContext_nat,modelTrace_nat,hr,modelMember_nat,
 modelSequent_nat,sourceTheoryProvable,sourceFullDerives,numericTraceDerives]
end ZFR.ArithmeticRepresentation
