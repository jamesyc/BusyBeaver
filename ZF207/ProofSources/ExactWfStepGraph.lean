module
public import ExactWfBranchGraph
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation

def wfStepGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “z h n. ∃ t, ∃ a, ∃ b, !radix8ResidueGraph t n ∧ !sourceLeftGraph a n ∧
 !sourceRightGraph b n ∧ !wfBranchGraph z h n t a b”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelWfStep (h n : M) : M :=
 let t := graphValue radix8ResidueGraph radix8ResidueGraph_total ![n]
 let a := graphValue sourceLeftGraph sourceLeftGraph_total ![n]
 let b := graphValue sourceRightGraph sourceRightGraph_total ![n]
 graphValue wfBranchGraph wfBranchGraph_total ![h,n,t,a,b]

lemma wfStepGraph_eval (z h n : M) : wfStepGraph.val.Evalb ![z,h,n] ↔ z=modelWfStep h n := by
 simp [wfStepGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq,
   graphValue_spec radix8ResidueGraph radix8ResidueGraph_total,
   graphValue_spec sourceLeftGraph sourceLeftGraph_total,
   graphValue_spec sourceRightGraph sourceRightGraph_total,
   graphValue_spec wfBranchGraph wfBranchGraph_total,modelWfStep]
 have hv (x : M) : (fun _ : Fin 1 => x)=![x] := by
   funext j; have hj : j=0 := Subsingleton.elim _ _; subst j; rfl
 simp only [hv]

lemma wfStepGraph_total : GraphTotalIn (M := M) wfStepGraph := by
 intro v
 have hv : v=![v 0,v 1] := by
   funext i; refine Fin.cases rfl (fun j => ?_) i
   exact Fin.cases rfl (fun x => Fin.elim0 x) j
 rw [hv]
 simp only [wfStepGraph_eval]
 exact ⟨_,rfl,fun _ h => h⟩

noncomputable def sourceWfHistory : PR.Construction M (historyBlueprint wfStepGraph) :=
 historyConstruction wfStepGraph wfStepGraph_total

end ZFR.ArithmeticRepresentation
