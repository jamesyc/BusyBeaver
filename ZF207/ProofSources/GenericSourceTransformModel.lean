module
public import ExactSourceShiftModel
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation.GenericTransform
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (idx : 𝚺ᴬ₁.Semisentence 3) (hi : GraphTotalIn (M:=M) idx)
noncomputable def transformHistory : PR.Construction M (historyBlueprint (transformStepGraph idx)) :=
 historyConstruction (transformStepGraph idx) (transformStepGraph_total idx hi)
noncomputable def modelTransform (d n : M) : M :=
 znth ((transformHistory idx hi).result ![] (modelCantor d n+1)) (modelCantor d n)
lemma modelTransform_step (d n : M) : modelTransform idx hi d n =
 modelTransformStep idx hi ((transformHistory idx hi).result ![] (modelCantor d n)) (modelCantor d n) := by
 unfold modelTransform transformHistory
 rw [history_last]
 apply (transformStepGraph_eval idx hi _ _ _).mp
 exact (graphValue_spec (transformStepGraph idx) (transformStepGraph_total idx hi) _ _).mpr rfl
lemma modelTransform_lookup (d n w : M) (h:modelCantor d n<w) :
 znth ((transformHistory idx hi).result ![] w) (modelCantor d n)=modelTransform idx hi d n :=
 history_stable (transformStepGraph idx) (transformStepGraph_total idx hi) ![]
 (modelCantor d n) (modelCantor d n+1) w (lt_add_one _) (succ_le_iff_lt.mpr h)
def transformGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “z d n. ∃ i, ∃ s, !exactCantorGraph i d n ∧
 !(historyBlueprint (transformStepGraph idx)).resultDef s (i+1) ∧ !znthDef z s i”
lemma transformGraph_eval (z d n : M) : (transformGraph idx).val.Evalb ![z,d,n] ↔ z=modelTransform idx hi d n := by
 let c := transformHistory idx hi
 simp [transformGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,
 modelCantor_defined.iff,c.result_defined_iff,znth_defined.iff]
 have hv (x:M) : (fun _ : Fin 1 => x)=![x] := by
  funext j; have hj:j=0 := Subsingleton.elim _ _; subst j; rfl
 simp only [hv]
 rfl
end ZFR.ArithmeticRepresentation.GenericTransform
