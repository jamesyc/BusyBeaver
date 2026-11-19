module
public import ExactWfStepGraph
public import ExactSourceDescent
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelSourceWfCode (n : M) : M :=
 znth ((sourceWfHistory (M := M)).result ![] (n+1)) n

def modelSourceWf (n : M) : Prop := modelSourceWfCode n=1

lemma modelSourceWfCode_step (n : M) : modelSourceWfCode n =
 modelWfStep ((sourceWfHistory (M := M)).result ![] n) n := by
 unfold modelSourceWfCode
 rw [show sourceWfHistory (M := M)=historyConstruction wfStepGraph wfStepGraph_total from rfl]
 rw [history_last]
 apply (wfStepGraph_eval _ _ _).mp
 exact (graphValue_spec wfStepGraph wfStepGraph_total _ _).mpr rfl

lemma modelSourceWfCode_lookup (n w : M) (hi : n<w) :
 znth ((sourceWfHistory (M := M)).result ![] w) n=modelSourceWfCode n :=
 history_stable wfStepGraph wfStepGraph_total ![] n (n+1) w (lt_add_one _) (succ_le_iff_lt.mpr hi)

def sourceWfCodeGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
 “z n. ∃ s, !(historyBlueprint wfStepGraph).resultDef s (n+1) ∧ !znthDef z s n”

def sourceWfFormula : 𝚺ᴬ₁.Semisentence 1 := .mkSigma “n. !sourceWfCodeGraph 1 n”

lemma sourceWfCodeGraph_eval (z n : M) : sourceWfCodeGraph.val.Evalb ![z,n] ↔ z=modelSourceWfCode n := by
 let c := sourceWfHistory (M := M)
 simp [sourceWfCodeGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq,c.result_defined_iff,znth_defined.iff]
 have hv (x : M) : (fun _ : Fin 1 => x)=![x] := by
   funext j; have hj : j=0 := Subsingleton.elim _ _; subst j; rfl
 simp only [hv]
 simp [modelSourceWfCode]
 rfl

lemma sourceWfFormula_eval (n : M) : sourceWfFormula.val.Evalb ![n] ↔ modelSourceWf n := by
 simp [sourceWfFormula,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq]
 have hv : (fun _ : Fin 1 => n)=![n] := by
   funext j; have hj : j=0 := Subsingleton.elim _ _; subst j; rfl
 simp only [hv]
 change sourceWfCodeGraph.val.Evalb ![1,n] ↔ _
 rw [sourceWfCodeGraph_eval]
 exact eq_comm

end ZFR.ArithmeticRepresentation
