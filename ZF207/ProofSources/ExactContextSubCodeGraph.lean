module
public import ExactContextSubStepGraph
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def contextSubCodeGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “z n x. ∃ s, !(historyBlueprint contextSubStepGraph).resultDef s (n+1) x ∧ !znthDef z s n”

lemma contextSubCodeGraph_eval (z n x : M) : contextSubCodeGraph.val.Evalb ![z,n,x] ↔ z=modelContextSubCode n x := by
 let c := contextSubHistory (M := M)
 simp [contextSubCodeGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq,c.result_defined_iff,znth_defined.iff]
 have hv (x : M) : (fun _ : Fin 1 => x)=![x] := by
   funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
 simp only [hv]
 change z=znth (c.result ![x] (n+1)) n ↔ z=modelContextSubCode n x
 rfl

end ZFR.ArithmeticRepresentation
