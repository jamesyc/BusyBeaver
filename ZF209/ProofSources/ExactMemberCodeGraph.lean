module
public import ExactMemberStepGraph
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma modelMemberCode_boolean (x n : M) : modelMemberCode x n=0 ∨ modelMemberCode x n=1 := by
 have h := (memberStepGraph_eval _ _ _ _).mp (modelMember_step x n)
 rcases h with ⟨_,h⟩|⟨_,⟨_,h⟩|⟨_,h⟩⟩
 · exact Or.inl h
 · exact Or.inr h
 · exact Or.inl h

def memberCodeGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “z x n. ∃ s, !(historyBlueprint memberStepGraph).resultDef s (n+1) x ∧ !znthDef z s n”

lemma memberCodeGraph_eval (z x n : M) : memberCodeGraph.val.Evalb ![z,x,n] ↔ z=modelMemberCode x n := by
 let c := memberHistory (M := M)
 simp [memberCodeGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq,c.result_defined_iff,znth_defined.iff]
 have hv (x : M) : (fun _ : Fin 1 => x)=![x] := by
   funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
 simp only [hv]
 change z=znth (c.result ![x] (n+1)) n ↔ z=modelMemberCode x n
 rfl

end ZFR.ArithmeticRepresentation
