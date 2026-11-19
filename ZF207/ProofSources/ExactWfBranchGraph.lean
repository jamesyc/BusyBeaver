module
public import ExactSourceDecoderEquations
public import ModelCourseOfValuesSentences
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation

/-- Bounded test of literal source-WF branches against earlier 0/1 values. -/
def wfAllowedGraph : 𝚺ᴬ₀.Semisentence 5 := .mkSigma
 “h n t a b. n=0 ∨ (t=1 ∨ t=2) ∨
 ((t=3 ∨ t=4 ∨ t=5) ∧ !znthDef 1 h a ∧ !znthDef 1 h b) ∨
 ((t=6 ∨ t=7) ∧ b=0 ∧ !znthDef 1 h a)”

def wfBranchGraph : 𝚺ᴬ₁.Semisentence 6 := .mkSigma
 “z h n t a b. (!wfAllowedGraph h n t a b ∧ z=1) ∨ (¬!wfAllowedGraph h n t a b ∧ z=0)”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def modelWfAllowed (h n t a b : M) : Prop :=
 n=0 ∨ (t=1 ∨ t=2) ∨
 ((t=3 ∨ t=4 ∨ t=5) ∧ znth h a=1 ∧ znth h b=1) ∨
 ((t=6 ∨ t=7) ∧ b=0 ∧ znth h a=1)

lemma wfAllowedGraph_eval (h n t a b : M) :
 wfAllowedGraph.val.Evalb ![h,n,t,a,b] ↔ modelWfAllowed h n t a b := by
 simp [wfAllowedGraph,modelWfAllowed,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq,znth_defined.iff,numeral_eq_natCast,eq_comm]

lemma wfAllowedGraph_defined : 𝚺ᴬ₀.Defined
 (fun v : Fin 5 → M => modelWfAllowed (v 0) (v 1) (v 2) (v 3) (v 4)) wfAllowedGraph := .mk (by
 intro v
 have hv : v=![v 0,v 1,v 2,v 3,v 4] := by
   funext i
   refine Fin.cases rfl (fun i => ?_) i
   refine Fin.cases rfl (fun i => ?_) i
   refine Fin.cases rfl (fun i => ?_) i
   refine Fin.cases rfl (fun i => ?_) i
   exact Fin.cases rfl (fun x => Fin.elim0 x) i
 rw [hv]
 exact wfAllowedGraph_eval _ _ _ _ _)

lemma wfBranchGraph_eval (z h n t a b : M) :
 wfBranchGraph.val.Evalb ![z,h,n,t,a,b] ↔
 (modelWfAllowed h n t a b ∧ z=1) ∨ (¬modelWfAllowed h n t a b ∧ z=0) := by
 simp [wfBranchGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq,wfAllowedGraph_defined.iff]

lemma wfBranchGraph_total : GraphTotalIn (M := M) wfBranchGraph := by
 intro v
 have hv : v=![v 0,v 1,v 2,v 3,v 4] := by
   funext i
   refine Fin.cases rfl (fun i => ?_) i
   refine Fin.cases rfl (fun i => ?_) i
   refine Fin.cases rfl (fun i => ?_) i
   refine Fin.cases rfl (fun i => ?_) i
   exact Fin.cases rfl (fun x => Fin.elim0 x) i
 rw [hv]
 simp only [wfBranchGraph_eval]
 by_cases h : modelWfAllowed (v 0) (v 1) (v 2) (v 3) (v 4) <;> simp [h]

end ZFR.ArithmeticRepresentation
