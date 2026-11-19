module
public import ExactTransformStepGraph
public import ExactSourceDecoderEquations
public import ExactBinderDescent
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelSourceShift (d n : M) : M :=
 let i := modelCantor d n
 znth ((sourceShiftHistory (M := M)).result ![] (i+1)) i

lemma modelSourceShift_step (d n : M) : modelSourceShift d n =
 modelTransformStep shiftIndexGraph shiftIndexGraph_total
   ((sourceShiftHistory (M := M)).result ![] (modelCantor d n)) (modelCantor d n) := by
 unfold modelSourceShift
 rw [show sourceShiftHistory (M := M)=historyConstruction (transformStepGraph shiftIndexGraph)
   (transformStepGraph_total shiftIndexGraph shiftIndexGraph_total) from rfl]
 rw [history_last]
 apply (transformStepGraph_eval shiftIndexGraph shiftIndexGraph_total _ _ _).mp
 exact (graphValue_spec (transformStepGraph shiftIndexGraph)
   (transformStepGraph_total shiftIndexGraph shiftIndexGraph_total) _ _).mpr rfl

lemma modelSourceShift_lookup (d n w : M) (hi : modelCantor d n<w) :
 znth ((sourceShiftHistory (M := M)).result ![] w) (modelCantor d n)=modelSourceShift d n := by
 exact history_stable (transformStepGraph shiftIndexGraph)
   (transformStepGraph_total shiftIndexGraph shiftIndexGraph_total) ![]
   (modelCantor d n) (modelCantor d n+1) w (lt_add_one _) (succ_le_iff_lt.mpr hi)

def sourceShiftGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “z d n. ∃ i, ∃ s, !exactCantorGraph i d n ∧
   !(historyBlueprint (transformStepGraph shiftIndexGraph)).resultDef s (i+1) ∧ !znthDef z s i”

lemma sourceShiftGraph_eval (z d n : M) : sourceShiftGraph.val.Evalb ![z,d,n] ↔ z=modelSourceShift d n := by
 let c := sourceShiftHistory (M := M)
 simp [sourceShiftGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq,modelCantor_defined.iff,c.result_defined_iff,znth_defined.iff]
 have hv (x : M) : (fun _ : Fin 1 => x)=![x] := by
   funext j; have hj : j=0 := Subsingleton.elim _ _; subst j; rfl
 simp only [hv]
 simp [modelSourceShift]
 rfl

end ZFR.ArithmeticRepresentation
