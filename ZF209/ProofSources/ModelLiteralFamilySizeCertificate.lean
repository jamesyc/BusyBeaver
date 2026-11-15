module
public import ModelBoundPredicateCertificate
public import ModelLiteralCourseRecCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def literalFamilyLeastPredicate (φ : ArithmeticSemiformula Nat 2) : ArithmeticSemiformula Nat 2 :=
 “z x. !φ z x ∧ ∀k, !φ k x → z≤k”
def literalFamilyLeast_certificate {e : Nat → M} {P : M → M → Prop}
 (p : FormulaCertificate e 2 (fun v=>P (v 0) (v 1))) :
 FunctionGraphCertificate e 1 (fun v=>t90 (fun k=>P k (v 0))) := by
 let q : FormulaCertificate e 2 (fun v=>t2 (P (v 0) (v 1)) (t8 (fun k=>t0 (P k (v 1)) (t47 (v 0) k)))) := {
  formula := literalFamilyLeastPredicate p.formula
  correct := by
   intro v
   have hp (k x:M) : p.formula.Eval ![k,x] e ↔ P k x := (p.correct ![k,x]).symm
   simp [literalFamilyLeastPredicate,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons']
   have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
    funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
   simp only [hv,hp]
   simp [t2,t1,t0,t8,literalLe_order] }
 exact FunctionGraphCertificate.ofDescription q

def literalFamilyBoundPredicate (φ : ArithmeticSemiformula Nat 2) : ArithmeticSemiformula Nat 2 :=
 “n x. ∀k, !φ k x → k<n”
def literalFamilySize_certificate {e : Nat → M} {P : M → M → Prop}
 (p : FormulaCertificate e 2 (fun v=>P (v 0) (v 1))) :
 FunctionGraphCertificate e 1 (fun v=>t125 (fun k=>P k (v 0))) := by
 let q : FormulaCertificate e 2 (fun v=>t18 (fun k=>P k (v 1)) (t120 (t124 (v 0)))) := {
  formula := literalFamilyBoundPredicate p.formula
  correct := by
   intro v
   have hp (k x:M) : p.formula.Eval ![k,x] e ↔ P k x := (p.correct ![k,x]).symm
   simp [literalFamilyBoundPredicate,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons']
   have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
    funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
   simp only [hv,hp]
   simp [t18,t8,t0,t16,literalUpto_member] }
 exact literalFamilyLeast_certificate (P:=fun n x=>t18 (fun k=>P k x) (t120 (t124 n))) q
end ZF209.MM0ModelReplay
