module
public import ExactMemberCodeGraph
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation

/-- Prove substitution semantics before instantiating the large concrete graph. -/
def memberOutputOne (φ : 𝚺ᴬ₁.Semisentence 3) : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
 “x n. !φ 1 x n”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma memberOutputOne_eval (φ : 𝚺ᴬ₁.Semisentence 3) (x n : M) :
 (memberOutputOne φ).val.Evalb ![x,n] ↔ φ.val.Evalb ![1,x,n] := by
 simp [memberOutputOne,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq]
 have hv : (fun _ : Fin 1 => n)=![n] := by
   funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
 rw [hv]

def memberFormula : 𝚺ᴬ₁.Semisentence 2 := memberOutputOne memberCodeGraph

lemma memberFormula_eval (x n : M) : memberFormula.val.Evalb ![x,n] ↔ modelMember x n := by
 change (memberOutputOne memberCodeGraph).val.Evalb ![x,n] ↔ modelMemberCode x n=1
 rw [memberOutputOne_eval,memberCodeGraph_eval]
 exact eq_comm

end ZFR.ArithmeticRepresentation
