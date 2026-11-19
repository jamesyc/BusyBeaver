module
public import ModelLiteralHistoryCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def literalCourseRecFormula (hist : ArithmeticSemiformula Nat 2) : ArithmeticSemiformula Nat 2 :=
 “y n. ∃s, !hist s (n+1) ∧ !(descriptionGraph literalBitApplicationPredicate) y n s”
noncomputable def literalCourseRec_certificate {e : Nat → M} {A : M → Prop}
 (a : FormulaCertificate e 1 (fun v=>A (v 0))) :
 FunctionGraphCertificate e 1 (fun v=>t138 A (v 0)) := by
 let h := literalHistory_certificate a
 refine ⟨literalCourseRecFormula h.formula,?_⟩
 intro v y
 have hh (s n:M) : h.formula.Eval ![s,n] e ↔ s=t137 A n := h.correct ![n] s
 have hb (y n s:M) : (descriptionGraph literalBitApplicationPredicate).Eval ![y,n,s] e ↔ y=t84 (t120 s) n :=
  (literalBitApplication_certificate e).correct ![n,s] y
 simp [literalCourseRecFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons']
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv,hh,hb]
 simp [t138,t29,Matrix.empty_eq]
end ZF207.MM0ModelReplay
