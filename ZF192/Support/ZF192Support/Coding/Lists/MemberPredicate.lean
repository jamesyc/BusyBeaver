module
public import ZF192Support.Coding.Lists.MemberCodeGraph
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
 rw [Matrix.constant_eq_singleton]

def memberFormula : 𝚺ᴬ₁.Semisentence 2 := memberOutputOne memberCodeGraph

lemma memberFormula_eval (x n : M) : memberFormula.val.Evalb ![x,n] ↔ modelMember x n := by
 change (memberOutputOne memberCodeGraph).val.Evalb ![x,n] ↔ modelMemberCode x n=1
 rw [memberOutputOne_eval,memberCodeGraph_eval]
 exact eq_comm

end ZFR.ArithmeticRepresentation
