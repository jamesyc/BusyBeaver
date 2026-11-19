module
public import ExactContextWfStepGraph
public import ExactSourceDescent
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelSourceContextWfCode (n : M) : M :=
 znth ((sourceContextWfHistory (M := M)).result ![] (n+1)) n

def modelSourceContextWf (n : M) : Prop := modelSourceContextWfCode n=1

lemma modelSourceContextWfCode_step (n : M) : modelSourceContextWfCode n =
 modelContextWfStep ((sourceContextWfHistory (M := M)).result ![] n) n := by
 unfold modelSourceContextWfCode
 rw [show sourceContextWfHistory (M := M)=historyConstruction contextWfStepGraph contextWfStepGraph_total from rfl]
 rw [history_last]
 apply (contextWfStepGraph_eval _ _ _).mp
 exact (graphValue_spec contextWfStepGraph contextWfStepGraph_total _ _).mpr rfl

lemma modelSourceContextWfCode_lookup (n w : M) (hi : n<w) :
 znth ((sourceContextWfHistory (M := M)).result ![] w) n=modelSourceContextWfCode n :=
 history_stable contextWfStepGraph contextWfStepGraph_total ![] n (n+1) w (lt_add_one _) (succ_le_iff_lt.mpr hi)

def sourceContextWfCodeGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
 “z n. ∃ s, !(historyBlueprint contextWfStepGraph).resultDef s (n+1) ∧ !znthDef z s n”

def sourceContextWfFormula : 𝚺ᴬ₁.Semisentence 1 := .mkSigma “n. !sourceContextWfCodeGraph 1 n”

lemma sourceContextWfCodeGraph_eval (z n : M) : sourceContextWfCodeGraph.val.Evalb ![z,n] ↔ z=modelSourceContextWfCode n := by
 let c := sourceContextWfHistory (M := M)
 simp [sourceContextWfCodeGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq,c.result_defined_iff,znth_defined.iff]
 have hv (x : M) : (fun _ : Fin 1 => x)=![x] := by
   funext j; have hj : j=0 := Subsingleton.elim _ _; subst j; rfl
 simp only [hv]
 simp [modelSourceContextWfCode]
 rfl

lemma sourceContextWfFormula_eval (n : M) : sourceContextWfFormula.val.Evalb ![n] ↔ modelSourceContextWf n := by
 simp [sourceContextWfFormula,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq]
 have hv : (fun _ : Fin 1 => n)=![n] := by
   funext j; have hj : j=0 := Subsingleton.elim _ _; subst j; rfl
 simp only [hv]
 change sourceContextWfCodeGraph.val.Evalb ![1,n] ↔ _
 rw [sourceContextWfCodeGraph_eval]
 exact eq_comm

end ZFR.ArithmeticRepresentation
