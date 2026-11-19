module
public import ExactContextShiftStepGraph
public import ExactSourceDescent
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelSourceContextShift (n : M) : M :=
 znth ((sourceContextShiftHistory (M := M)).result ![] (n+1)) n

lemma modelSourceContextShift_step (n : M) : modelSourceContextShift n =
 modelContextShiftStep ((sourceContextShiftHistory (M := M)).result ![] n) n := by
 unfold modelSourceContextShift
 rw [show sourceContextShiftHistory (M := M)=historyConstruction contextShiftStepGraph contextShiftStepGraph_total from rfl]
 rw [history_last]
 apply (contextShiftStepGraph_eval _ _ _).mp
 exact (graphValue_spec contextShiftStepGraph contextShiftStepGraph_total _ _).mpr rfl

lemma modelSourceContextShift_lookup (n w : M) (hi : n<w) :
 znth ((sourceContextShiftHistory (M := M)).result ![] w) n=modelSourceContextShift n :=
 history_stable contextShiftStepGraph contextShiftStepGraph_total ![] n (n+1) w (lt_add_one _) (succ_le_iff_lt.mpr hi)

def sourceContextShiftGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
 “z n. ∃ s, !(historyBlueprint contextShiftStepGraph).resultDef s (n+1) ∧ !znthDef z s n”

lemma sourceContextShiftGraph_eval (z n : M) : sourceContextShiftGraph.val.Evalb ![z,n] ↔ z=modelSourceContextShift n := by
 let c := sourceContextShiftHistory (M := M)
 simp [sourceContextShiftGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq,c.result_defined_iff,znth_defined.iff]
 have hv (x : M) : (fun _ : Fin 1 => x)=![x] := by
   funext j; have hj : j=0 := Subsingleton.elim _ _; subst j; rfl
 simp only [hv]
 simp [modelSourceContextShift]
 rfl

end ZFR.ArithmeticRepresentation
