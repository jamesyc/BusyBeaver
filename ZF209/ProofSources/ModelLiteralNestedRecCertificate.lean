module
public import ModelLiteralDomainSizeCertificate
public import ModelLiteralSetCodeCertificate
public import LiteralPredecessorModelAlignment
public import ModelLiteralSubstitutionCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def literalNestedStepFormula (dom app : ArithmeticSemiformula Nat 2) : ArithmeticSemiformula Nat 2 :=
 “y s. ∃n, !dom n s ∧ ((n=0 ∧ y=&0) ∨ (n≠0 ∧ ∃m, ∃l, ∃r, ∃z, ∃q, ∃p,
 !predecessorGraph m n ∧ !unpairLeftGraph l m ∧ !unpairRightGraph r m ∧
 !(descriptionGraph literalBitApplicationPredicate) z r s ∧ !literalPairGraph q r z ∧ !literalPairGraph p l q ∧ !app y p))”
noncomputable def literalNestedStep_certificate {e : Nat → M} {A : M → Prop}
 (a : FormulaCertificate e 1 (fun v=>A (v 0))) :
 FunctionGraphCertificate e 1 (fun v=>t43 (t125 (t76 (t120 (v 0)))) (fun n=>t50 (t10 n t28) (e 0)
  (t84 A (t63 (t64 (t46 n t30)) (t63 (t65 (t46 n t30)) (t84 (t120 (v 0)) (t65 (t46 n t30)))))))) := by
 let dom := literalBitDomainSize_certificate e
 let app := literalApply_certificate a
 refine ⟨literalNestedStepFormula dom.formula app.formula,?_⟩
 intro v y
 have hd (n s:M) : dom.formula.Eval ![n,s] e ↔ n=t125 (t76 (t120 s)) := dom.correct ![s] n
 have ha (y p:M) : app.formula.Eval ![y,p] e ↔ y=t84 A p := app.correct ![p] y
 have hp (m n:M) : predecessorGraph.val.Evalb ![m,n] ↔ m=t46 n 1 := by
  rw [literalSubOne_modelPredecessor]; exact predecessorGraph_value m n
 have hl (x k:M) : unpairLeftGraph.val.Evalb ![x,k] ↔ x=t64 k := by
  rw [literalFst_modelUnpairLeft]; exact graphValue_spec unpairLeftGraph unpairLeftGraph_total x ![k]
 have hr (x k:M) : unpairRightGraph.val.Evalb ![x,k] ↔ x=t65 k := by
  rw [literalSnd_modelUnpairRight]; exact graphValue_spec unpairRightGraph unpairRightGraph_total x ![k]
 have hb (y n s:M) : (descriptionGraph literalBitApplicationPredicate).Eval ![y,n,s] e ↔ y=t84 (t120 s) n :=
  (literalBitApplication_certificate e).correct ![n,s] y
 simp [literalNestedStepFormula,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq]
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv,hd,ha,hp,hl,hr,hb,literalPairGraph_eval,exists_eq_left]
 classical
 simp [literalSubstitute_value,t10,t28,t30,t29,literalConditional_value]
 split_ifs <;> simp_all
noncomputable def literalNestedRec_certificate {e : Nat → M} {A : M → Prop}
 (a : FormulaCertificate e 1 (fun v=>A (v 0))) :
 FunctionGraphCertificate e 1 (fun v=>t142 (e 0) A (v 0)) :=
 literalCourseRec_certificate (literalGraph_certificate (literalNestedStep_certificate a))
end ZF209.MM0ModelReplay
