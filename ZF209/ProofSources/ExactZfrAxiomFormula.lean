module
public import ExactSchemaCodeGraphs
public import ExactFixedAxiomFormula
public import ExactSourceBoundEquations
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def zfrAxiomFormula : 𝚺ᴬ₁.Semisentence 1 := .mkSigma
 “z. !fixedAxiomFormula z ∨
 (!sourceBoundFormula 0 z ∧ ∃ phi, ∃ n, !sourceBoundFormula (n+1) phi ∧ !separationCodeGraph z phi n) ∨
 (!sourceBoundFormula 0 z ∧ ∃ phi, ∃ n, !sourceBoundFormula (n+2) phi ∧ !replacementCodeGraph z phi n)”
def modelZfrAxiom (z : M) := modelFixedAxiom z ∨
 (modelSourceBound 0 z ∧ ∃ phi n, modelSourceBound (n+1) phi ∧ z=modelSeparationCode phi n) ∨
 (modelSourceBound 0 z ∧ ∃ phi n, modelSourceBound (n+2) phi ∧ z=modelReplacementCode phi n)
lemma zfrAxiomFormula_defined : 𝚺ᴬ₁.DefinedPred (modelZfrAxiom (M:=M)) zfrAxiomFormula := .mk (by
 intro v
 simp [zfrAxiomFormula,modelZfrAxiom,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,
 fixedAxiomFormula_defined.iff,sourceBoundFormula_defined.iff,separationCodeGraph_defined.iff,replacementCodeGraph_defined.iff,numeral_eq_natCast]
 have hv (x:M) : (fun _ : Fin 1 => x)=![x] := by
  funext i; have hi:i=0 := Subsingleton.elim _ _; subst i; rfl
 simp only [hv]
 simp)
lemma modelZfrAxiom_nat (z : Nat) : modelZfrAxiom z ↔ sourceZfrAxiom z := by
 have hf (z : Nat) : modelFixedAxiom z ↔ sourceZfrFixed z := (fixedAxiomFormula_defined.iff (v:=![z])).symm.trans (fixedAxiomFormula_nat z)
 simp only [modelZfrAxiom,sourceZfrAxiom,numericClosedSeparation,numericClosedReplacement,hf,
 modelSourceBound_nat,modelSeparationCode_nat,modelReplacementCode_nat]
 rfl
end ZFR.ArithmeticRepresentation
