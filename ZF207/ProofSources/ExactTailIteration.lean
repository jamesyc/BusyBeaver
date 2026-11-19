module
public import ExactUnaryFormula
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma ruleTail_defined : 𝚺ᴬ₁.DefinedFunction₁ (modelListTail (M:=M)) listTailGraph := .mk (by
 intro v
 have hv : v=![v 0,v 1] := by
  funext i; refine Fin.cases rfl (fun j=>?_) i
  exact Fin.cases rfl (fun j=>Fin.elim0 j) j
 rw [hv]; exact listTailGraph_eval _ _)
def tailIterationBlueprint : PR.Blueprint 1 where
 zero := .mkSigma “z n. z=n”
 succ := .mkSigma “u z i n. !listTailGraph u z”
noncomputable def tailIterationConstruction : PR.Construction M tailIterationBlueprint where
 zero := fun v => v 0
 succ := fun _ _ z => modelListTail z
 zero_defined := .mk (by intro v; simp [tailIterationBlueprint])
 succ_defined := .mk (by intro v; simp [tailIterationBlueprint,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,ruleTail_defined.iff])
noncomputable def modelTailIter (k n : M) : M := tailIterationConstruction.result ![n] k
def tailIterationGraph : 𝚺ᴬ₁.Semisentence 3 := tailIterationBlueprint.resultDef
lemma tailIterationGraph_defined : 𝚺ᴬ₁.DefinedFunction₂ (modelTailIter (M:=M)) tailIterationGraph := .mk (by
 intro v
 have hv : v=![v 0,v 1,v 2] := by
  funext i; refine Fin.cases rfl (fun j=>?_) i
  refine Fin.cases rfl (fun j=>?_) j
  exact Fin.cases rfl (fun j=>Fin.elim0 j) j
 rw [hv]
 exact tailIterationConstruction.result_defined_iff _)
lemma modelTailIter_zero (n : M) : modelTailIter 0 n=n := tailIterationConstruction.result_zero ![n]
lemma modelTailIter_succ (k n : M) : modelTailIter (k+1) n=modelListTail (modelTailIter k n) :=
 tailIterationConstruction.result_succ ![n] k
end ZFR.ArithmeticRepresentation
