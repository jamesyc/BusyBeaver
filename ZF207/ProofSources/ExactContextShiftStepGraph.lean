module
public import ExactSourceShiftSentences
public import ExactListDecoderGraphs
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation

def contextShiftBranchGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
 “z h n a b. (n=0 ∧ z=0) ∨ (n≠0 ∧ ∃ x, ∃ y,
 !sourceShiftGraph x 0 a ∧ !znthDef y h b ∧ !listConsGraph z x y)”

def contextShiftStepGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “z h n. ∃ a, ∃ b, !listHeadGraph a n ∧ !listTailGraph b n ∧ !contextShiftBranchGraph z h n a b”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma contextShiftBranchGraph_eval (z h n a b : M) :
 contextShiftBranchGraph.val.Evalb ![z,h,n,a,b] ↔
 (n=0 ∧ z=0) ∨ (n≠0 ∧ z=modelListCons (modelSourceShift 0 a) (znth h b)) := by
 simp [contextShiftBranchGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq,sourceShiftGraph_defined.iff,znth_defined.iff]
 have hv (x : M) : (fun _ : Fin 1 => x)=![x] := by
   funext j; have hj : j=0 := Subsingleton.elim _ _; subst j; rfl
 simp only [hv]
 rw [listConsGraph_eval]

lemma contextShiftBranchGraph_total : GraphTotalIn (M := M) contextShiftBranchGraph := by
 intro v
 have hv : v=![v 0,v 1,v 2,v 3] := by
  funext i; refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  exact Fin.cases rfl (fun x => Fin.elim0 x) i
 rw [hv]
 simp only [contextShiftBranchGraph_eval]
 by_cases h : v 1=0 <;> simp [h]

noncomputable def modelContextShiftStep (h n : M) : M :=
 graphValue contextShiftBranchGraph contextShiftBranchGraph_total ![h,n,modelListHead n,modelListTail n]

lemma contextShiftStepGraph_eval (z h n : M) :
 contextShiftStepGraph.val.Evalb ![z,h,n] ↔ z=modelContextShiftStep h n := by
 simp [contextShiftStepGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq]
 have hv (x : M) : (fun _ : Fin 1 => x)=![x] := by
   funext j; have hj : j=0 := Subsingleton.elim _ _; subst j; rfl
 simp only [hv]
 simp [listHeadGraph_eval,listTailGraph_eval,graphValue_spec contextShiftBranchGraph contextShiftBranchGraph_total,
   modelContextShiftStep]

lemma contextShiftStepGraph_total : GraphTotalIn (M := M) contextShiftStepGraph := by
 intro v
 have hv : v=![v 0,v 1] := by funext i; refine Fin.cases rfl (fun i => ?_) i; exact Fin.cases rfl (fun x => Fin.elim0 x) i
 rw [hv]
 simp only [contextShiftStepGraph_eval]
 exact ⟨_,rfl,fun _ h => h⟩

noncomputable def sourceContextShiftHistory : PR.Construction M (historyBlueprint contextShiftStepGraph) :=
 historyConstruction contextShiftStepGraph contextShiftStepGraph_total

end ZFR.ArithmeticRepresentation
