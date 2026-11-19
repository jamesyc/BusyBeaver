module
public import ModelLiteralNestedRecCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZF207.MM0ModelPeano ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma literalContextBuildStep_member (k : M) :
 t89 (fun a=>t89 (fun _=>t82 (fun c=>t123 a c))) k ↔
 t65 k=t123 (t64 (t64 k)) (t65 (t65 (t64 k))) := by
 simp [t89,t73,t15,t16,t25,t14,t8,t0,t10,literalGraph_pair_member,p1277,p1278]
 rw [p1277,p1278]
def literalContextBuildStepFormula : ArithmeticSemiformula Nat 1 :=
 “k. ∃u, ∃y, ∃a, ∃bc, ∃c,
 !unpairLeftGraph u k ∧ !unpairRightGraph y k ∧ !unpairLeftGraph a u ∧ !unpairRightGraph bc u ∧ !unpairRightGraph c bc ∧
 !(descriptionGraph literalInsertCodePredicate) y a c”
def literalContextBuildStep_certificate (e : Nat → M) :
 FormulaCertificate e 1 (fun v=>t89 (fun a=>t89 (fun _=>t82 (fun c=>t123 a c))) (v 0)) where
 formula := literalContextBuildStepFormula
 correct := by
  intro v
  rw [literalContextBuildStep_member]
  have hl (x k:M) : unpairLeftGraph.val.Evalb ![x,k] ↔ x=t64 k := by
   rw [literalFst_modelUnpairLeft]; exact graphValue_spec unpairLeftGraph unpairLeftGraph_total x ![k]
  have hr (x k:M) : unpairRightGraph.val.Evalb ![x,k] ↔ x=t65 k := by
   rw [literalSnd_modelUnpairRight]; exact graphValue_spec unpairRightGraph unpairRightGraph_total x ![k]
  have hi (y a c:M) : (descriptionGraph literalInsertCodePredicate).Eval ![y,a,c] e ↔ y=t123 a c :=
   (literalInsertCode_certificate e).correct ![a,c] y
  simp [literalContextBuildStepFormula,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons']
  have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
   funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
  simp only [hv,hl,hr,hi,exists_eq_left]
noncomputable def literalContextCode_certificate (e : Nat → M) :
 FunctionGraphCertificate e 1 (fun v=>t143 (v 0)) := by
 let ee : Nat → M := fun i=>Nat.casesOn i 0 e
 let g := literalNestedRec_certificate (literalContextBuildStep_certificate ee)
 refine ⟨substituteZeroParameter g.formula,?_⟩
 intro v y
 rw [substituteZeroParameter_eval]
 exact g.correct v y
def literalContextMembershipFormula (code : ArithmeticSemiformula Nat 2) : ArithmeticSemiformula Nat 2 :=
 “a g. ∃s, !code s g ∧ !literalBitMembershipFormula a s”
noncomputable def literalContextMembership_certificate (e : Nat → M) :
 FormulaCertificate e 2 (fun v=>t144 (v 0) (v 1)) := by
 let c := literalContextCode_certificate e
 refine ⟨literalContextMembershipFormula c.formula,?_⟩
 intro v
 have hc (s g:M) : c.formula.Eval ![s,g] e ↔ s=t143 g := c.correct ![g] s
 simp [literalContextMembershipFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons']
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp only [hv,hc,literalBitMembershipFormula_eval,exists_eq_left]
 rfl
end ZF207.MM0ModelReplay
