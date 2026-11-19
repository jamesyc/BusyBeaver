module
public import ExactSubstBranchGraph
public import ExactSourceDecoderGraphs
public import ExactIndexEquations
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation

def substTransformStepGraph (idx : 𝚺ᴬ₁.Semisentence 4) : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
 “z h i r. ∃ d, ∃ n, ∃ t, ∃ a, ∃ b,
 !unpairLeftGraph d i ∧ !unpairRightGraph n i ∧ !radix8ResidueGraph t n ∧
 !sourceLeftGraph a n ∧ !sourceRightGraph b n ∧ !(substTransformBranchGraph idx) z h d n t a b r”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelSubstTransformStep (idx : 𝚺ᴬ₁.Semisentence 4)
 (hi : GraphTotalIn (M := M) idx) (h i r : M) : M :=
 let d := graphValue unpairLeftGraph unpairLeftGraph_total ![i]
 let n := graphValue unpairRightGraph unpairRightGraph_total ![i]
 let t := graphValue radix8ResidueGraph radix8ResidueGraph_total ![n]
 let a := graphValue sourceLeftGraph sourceLeftGraph_total ![n]
 let b := graphValue sourceRightGraph sourceRightGraph_total ![n]
 graphValue (substTransformBranchGraph idx) (substTransformBranchGraph_total idx hi) ![h,d,n,t,a,b,r]

lemma substTransformStepGraph_eval (idx : 𝚺ᴬ₁.Semisentence 4)
 (hi : GraphTotalIn (M := M) idx) (z h i r : M) :
 (substTransformStepGraph idx).val.Evalb ![z,h,i,r] ↔ z=modelSubstTransformStep idx hi h i r := by
 simp [substTransformStepGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq,
   graphValue_spec unpairLeftGraph unpairLeftGraph_total,
   graphValue_spec unpairRightGraph unpairRightGraph_total,
   graphValue_spec radix8ResidueGraph radix8ResidueGraph_total,
   graphValue_spec sourceLeftGraph sourceLeftGraph_total,
   graphValue_spec sourceRightGraph sourceRightGraph_total,
   graphValue_spec (substTransformBranchGraph idx) (substTransformBranchGraph_total idx hi),modelSubstTransformStep]
 have hv (x : M) : (fun _ : Fin 1 => x)=![x] := by
   funext j; have hj : j=0 := Subsingleton.elim _ _; subst j; rfl
 simp only [hv]

lemma substTransformStepGraph_total (idx : 𝚺ᴬ₁.Semisentence 4)
 (hi : GraphTotalIn (M := M) idx) : GraphTotalIn (M := M) (substTransformStepGraph idx) := by
 intro v
 have hv : v=![v 0,v 1,v 2] := by funext i; refine Fin.cases rfl (fun j => ?_) i; refine Fin.cases rfl (fun j => ?_) j; exact Fin.cases rfl (fun x => Fin.elim0 x) j
 rw [hv]
 simp only [substTransformStepGraph_eval idx hi]
 exact ⟨_,rfl,fun _ h => h⟩

/-- This explicit graph, unlike a choice of PR representation, has the literal
source branch equations. Correctness of history lookup is established separately. -/
noncomputable def sourceSubstHistory : PR.Construction M (historyBlueprint (substTransformStepGraph substIndexGraph)) :=
 historyConstruction (substTransformStepGraph substIndexGraph) (substTransformStepGraph_total substIndexGraph substIndexGraph_total)

end ZFR.ArithmeticRepresentation
