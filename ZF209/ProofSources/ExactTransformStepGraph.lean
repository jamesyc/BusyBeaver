module
public import ExactTransformBranchGraph
public import ExactSourceDecoderGraphs
public import ExactIndexEquations
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation

def transformStepGraph (idx : 𝚺ᴬ₁.Semisentence 3) : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “z h i. ∃ d, ∃ n, ∃ t, ∃ a, ∃ b,
 !unpairLeftGraph d i ∧ !unpairRightGraph n i ∧ !radix8ResidueGraph t n ∧
 !sourceLeftGraph a n ∧ !sourceRightGraph b n ∧ !(transformBranchGraph idx) z h d n t a b”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelTransformStep (idx : 𝚺ᴬ₁.Semisentence 3)
 (hi : GraphTotalIn (M := M) idx) (h i : M) : M :=
 let d := graphValue unpairLeftGraph unpairLeftGraph_total ![i]
 let n := graphValue unpairRightGraph unpairRightGraph_total ![i]
 let t := graphValue radix8ResidueGraph radix8ResidueGraph_total ![n]
 let a := graphValue sourceLeftGraph sourceLeftGraph_total ![n]
 let b := graphValue sourceRightGraph sourceRightGraph_total ![n]
 graphValue (transformBranchGraph idx) (transformBranchGraph_total idx hi) ![h,d,n,t,a,b]

lemma transformStepGraph_eval (idx : 𝚺ᴬ₁.Semisentence 3)
 (hi : GraphTotalIn (M := M) idx) (z h i : M) :
 (transformStepGraph idx).val.Evalb ![z,h,i] ↔ z=modelTransformStep idx hi h i := by
 simp [transformStepGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq,
   graphValue_spec unpairLeftGraph unpairLeftGraph_total,
   graphValue_spec unpairRightGraph unpairRightGraph_total,
   graphValue_spec radix8ResidueGraph radix8ResidueGraph_total,
   graphValue_spec sourceLeftGraph sourceLeftGraph_total,
   graphValue_spec sourceRightGraph sourceRightGraph_total,
   graphValue_spec (transformBranchGraph idx) (transformBranchGraph_total idx hi),modelTransformStep]
 have hv (x : M) : (fun _ : Fin 1 => x)=![x] := by
   funext j; have hj : j=0 := Subsingleton.elim _ _; subst j; rfl
 simp only [hv]

lemma transformStepGraph_total (idx : 𝚺ᴬ₁.Semisentence 3)
 (hi : GraphTotalIn (M := M) idx) : GraphTotalIn (M := M) (transformStepGraph idx) := by
 intro v
 have hv : v=![v 0,v 1] := by funext i; refine Fin.cases rfl (fun j => ?_) i; exact Fin.cases rfl (fun x => Fin.elim0 x) j
 rw [hv]
 simp only [transformStepGraph_eval idx hi]
 exact ⟨_,rfl,fun _ h => h⟩

/-- This explicit graph, unlike a choice of PR representation, has the literal
source branch equations. Correctness of history lookup is established separately. -/
noncomputable def sourceShiftHistory : PR.Construction M (historyBlueprint (transformStepGraph shiftIndexGraph)) :=
 historyConstruction (transformStepGraph shiftIndexGraph) (transformStepGraph_total shiftIndexGraph shiftIndexGraph_total)

end ZFR.ArithmeticRepresentation
