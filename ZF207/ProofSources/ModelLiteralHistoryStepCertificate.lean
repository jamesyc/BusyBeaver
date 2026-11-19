module
public import ModelLiteralFunctionUpdateCertificate
public import ModelLiteralRecnCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZF207.MM0ModelPeano ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma literalGraph_pair_member (F : M → M) (x y : M) :
 t82 F (t63 x y) ↔ y=F x := by
 change (¬∀a,¬(t63 x y=t63 a (F a))) ↔ _
 rw [not_forall]
 simp only [not_not]
 constructor
 · rintro ⟨a,h⟩
   have hx := congrArg (t64 (M:=M)) h
   have hy := congrArg (t65 (M:=M)) h
   change t64 (t63 x y)=t64 (t63 a (F a)) at hx
   rw [p1277,p1277] at hx
   rw [p1278,p1278] at hy
   simpa [←hx] using hy
 · intro h; exact ⟨x,by rw [h]⟩
lemma literalHistoryStep_member (A : M → Prop) (k : M) :
 t89 (fun a=>t82 (fun s=>t121 (t136 (t120 s) a (t84 A s)))) k ↔
 t65 k=t121 (t136 (t120 (t65 (t64 k))) (t64 (t64 k)) (t84 A (t65 (t64 k)))) := by
 simp [t89,t73,t15,t16,t25,t14,t8,t0,t10,literalGraph_pair_member]
def literalHistoryStepFormula (app : ArithmeticSemiformula Nat 2) : ArithmeticSemiformula Nat 1 :=
 “k. ∃p, ∃y, ∃a, ∃s, ∃v,
 !unpairLeftGraph p k ∧ !unpairRightGraph y k ∧ !unpairLeftGraph a p ∧ !unpairRightGraph s p ∧
 !app v s ∧ !(descriptionGraph literalFunctionUpdateCodePredicate) y s a v”
noncomputable def literalHistoryStep_certificate {e : Nat → M} {A : M → Prop}
 (a : FormulaCertificate e 1 (fun v=>A (v 0))) :
 FormulaCertificate e 1 (fun v=>t89 (fun key=>t82 (fun s=>t121 (t136 (t120 s) key (t84 A s)))) (v 0)) := by
 let app := literalApply_certificate a
 refine ⟨literalHistoryStepFormula app.formula,?_⟩
 intro v
 rw [literalHistoryStep_member]
 have hl (x k:M) : unpairLeftGraph.val.Evalb ![x,k] ↔ x=t64 k := by
  rw [literalFst_modelUnpairLeft]; exact graphValue_spec unpairLeftGraph unpairLeftGraph_total x ![k]
 have hr (x k:M) : unpairRightGraph.val.Evalb ![x,k] ↔ x=t65 k := by
  rw [literalSnd_modelUnpairRight]; exact graphValue_spec unpairRightGraph unpairRightGraph_total x ![k]
 have ha (y s:M) : app.formula.Eval ![y,s] e ↔ y=t84 A s := app.correct ![s] y
 have hu (y s key z:M) : (descriptionGraph literalFunctionUpdateCodePredicate).Eval ![y,s,key,z] e ↔ y=t121 (t136 (t120 s) key z) :=
  (literalFunctionUpdateCode_certificate e).correct ![s,key,z] y
 simp [literalHistoryStepFormula,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons']
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv,hl,hr,ha,hu,exists_eq_left]
end ZF207.MM0ModelReplay
