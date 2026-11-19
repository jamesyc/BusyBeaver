module
public import ExactSubstStepGraph
public import ExactSourceDecoderEquations
public import ExactBinderDescent
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelSourceSubst (d r n : M) : M :=
 let i := modelCantor d n
 znth ((sourceSubstHistory (M := M)).result ![r] (i+1)) i

lemma modelSourceSubst_step (d r n : M) : modelSourceSubst d r n =
 modelSubstTransformStep substIndexGraph substIndexGraph_total
   ((sourceSubstHistory (M := M)).result ![r] (modelCantor d n)) (modelCantor d n) r := by
 unfold modelSourceSubst
 rw [show sourceSubstHistory (M := M)=historyConstruction (substTransformStepGraph substIndexGraph)
   (substTransformStepGraph_total substIndexGraph substIndexGraph_total) from rfl]
 rw [history_last]
 apply (substTransformStepGraph_eval substIndexGraph substIndexGraph_total _ _ _ _).mp
 exact (graphValue_spec (substTransformStepGraph substIndexGraph)
   (substTransformStepGraph_total substIndexGraph substIndexGraph_total) _ _).mpr rfl

lemma modelSourceSubst_lookup (d r n w : M) (hi : modelCantor d n<w) :
 znth ((sourceSubstHistory (M := M)).result ![r] w) (modelCantor d n)=modelSourceSubst d r n := by
 exact history_stable (substTransformStepGraph substIndexGraph)
   (substTransformStepGraph_total substIndexGraph substIndexGraph_total) ![r]
   (modelCantor d n) (modelCantor d n+1) w (lt_add_one _) (succ_le_iff_lt.mpr hi)

def sourceSubstGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
 “z d r n. ∃ i, ∃ s, !exactCantorGraph i d n ∧
   !(historyBlueprint (substTransformStepGraph substIndexGraph)).resultDef s (i+1) r ∧ !znthDef z s i”

lemma sourceSubstGraph_eval (z d r n : M) : sourceSubstGraph.val.Evalb ![z,d,r,n] ↔ z=modelSourceSubst d r n := by
 let c := sourceSubstHistory (M := M)
 simp [sourceSubstGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq,modelCantor_defined.iff,c.result_defined_iff,znth_defined.iff]
 have hv (x : M) : (fun _ : Fin 1 => x)=![x] := by
   funext j; have hj : j=0 := Subsingleton.elim _ _; subst j; rfl
 simp only [hv]
 simp [modelSourceSubst]
 rfl

end ZFR.ArithmeticRepresentation
