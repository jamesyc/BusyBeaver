module
public import ExactSourceWfSentences
public import ExactListDecoderGraphs
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation

def contextWfBranchGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
 “z h n a b. ∃ w, !sourceWfCodeGraph w a ∧
 (((n=0 ∨ (w=1 ∧ !znthDef 1 h b)) ∧ z=1) ∨
 (¬(n=0 ∨ (w=1 ∧ !znthDef 1 h b)) ∧ z=0))”

def contextWfStepGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “z h n. ∃ a, ∃ b, !listHeadGraph a n ∧ !listTailGraph b n ∧ !contextWfBranchGraph z h n a b”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma contextWfBranchGraph_eval (z h n a b : M) :
 contextWfBranchGraph.val.Evalb ![z,h,n,a,b] ↔
 (((n=0 ∨ (modelSourceWf a ∧ znth h b=1)) ∧ z=1) ∨
 (¬(n=0 ∨ (modelSourceWf a ∧ znth h b=1)) ∧ z=0)) := by
 simp [contextWfBranchGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq,sourceWfCodeGraph_defined.iff,znth_defined.iff,modelSourceWf,eq_comm]
 by_cases h1 : 1=modelSourceWfCode a <;> simp [h1]

lemma contextWfBranchGraph_total : GraphTotalIn (M := M) contextWfBranchGraph := by
 intro v
 have hv : v=![v 0,v 1,v 2,v 3] := by
  funext i; refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  exact Fin.cases rfl (fun x => Fin.elim0 x) i
 rw [hv]
 simp only [contextWfBranchGraph_eval]
 by_cases h : v 1=0 ∨ (modelSourceWf (v 2) ∧ znth (v 0) (v 3)=1) <;> simp [h]

noncomputable def modelContextWfStep (h n : M) : M :=
 graphValue contextWfBranchGraph contextWfBranchGraph_total ![h,n,modelListHead n,modelListTail n]

lemma contextWfStepGraph_eval (z h n : M) :
 contextWfStepGraph.val.Evalb ![z,h,n] ↔ z=modelContextWfStep h n := by
 simp [contextWfStepGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq]
 have hv (x : M) : (fun _ : Fin 1 => x)=![x] := by
   funext j; have hj : j=0 := Subsingleton.elim _ _; subst j; rfl
 simp only [hv]
 simp [listHeadGraph_eval,listTailGraph_eval,graphValue_spec contextWfBranchGraph contextWfBranchGraph_total,
   modelContextWfStep]

lemma contextWfStepGraph_total : GraphTotalIn (M := M) contextWfStepGraph := by
 intro v
 have hv : v=![v 0,v 1] := by funext i; refine Fin.cases rfl (fun i => ?_) i; exact Fin.cases rfl (fun x => Fin.elim0 x) i
 rw [hv]
 simp only [contextWfStepGraph_eval]
 exact ⟨_,rfl,fun _ h => h⟩

noncomputable def sourceContextWfHistory : PR.Construction M (historyBlueprint contextWfStepGraph) :=
 historyConstruction contextWfStepGraph contextWfStepGraph_total

end ZFR.ArithmeticRepresentation
