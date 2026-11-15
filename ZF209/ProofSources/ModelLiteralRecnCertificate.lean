module
public import ModelLiteralRecnStepCertificate
public import ModelLiteralRecursionBinaryCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def literalRecnFormula (rr : ArithmeticSemiformula Nat 3) : ArithmeticSemiformula Nat 2 :=
 “y n. ∃i, ∃r, !literalPairGraph i 0 &0 ∧ !rr r n i ∧ !unpairRightGraph y r”
noncomputable def literalRecn_certificate {e : Nat → M} {A : M → Prop}
 (a : FormulaCertificate e 1 (fun v=>A (v 0))) :
 FunctionGraphCertificate e 1 (fun v=>t112 (e 0) A (v 0)) := by
 let step := literalRecnStep_certificate a
 let rr := literalRecursionBinary_certificate step
 refine ⟨literalRecnFormula rr.formula,?_⟩
 intro v y
 have hr (z n i:M) : rr.formula.Eval ![z,n,i] e ↔ z=t110 i (t82 (fun x=>t63 (t29 (t64 x)) (t84 A x))) n := rr.correct ![n,i] z
 have hs (z r:M) : unpairRightGraph.val.Evalb ![z,r] ↔ z=t65 r := by
  rw [literalSnd_modelUnpairRight]; exact graphValue_spec unpairRightGraph unpairRightGraph_total z ![r]
 simp [literalRecnFormula,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons']
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv,literalPairGraph_eval,hr,hs,exists_eq_left]
 simp [t112,t111,t28,numeral_eq_natCast,Matrix.empty_eq]
end ZF209.MM0ModelReplay
