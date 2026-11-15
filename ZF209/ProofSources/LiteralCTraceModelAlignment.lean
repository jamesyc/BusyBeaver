module
public import LiteralCRuleModelAlignment
public import ModelTraceFormulaCertificate
public import ModelLiteralC209RulesCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
attribute [local irreducible] t335 t337 modelTrace modelCRule modelMember
noncomputable def modelCRule_certificate (e : Nat → M) :
 FormulaCertificate e 2 (fun v=>modelCRule (v 0) (v 1)) := by
 let r := literalC209Rules_certificate e
 refine ⟨“a b. ∃k, !literalPairGraph k a b ∧ !r.formula k”,?_⟩
 intro v
 have hp (k a b:M) := literalPairGraph_eval e k a b
 have hr (k:M) : r.formula.Eval ![k] e ↔ t335 k := (r.correct ![k]).symm
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',hv,hp,hr,
 literalPair_modelCantor,literalCRule_pair]
lemma literalCTrace_zero : t172 (t335 (M:=M)) 0 := by
 simpa only [t28] using p2753 (fun _ : Nat=> (0:M)) t335 (literalC209Rules_certificate _)
lemma literalCTrace_cons (a b:M) : t172 t335 (modelListCons a b) ↔ t172 t335 b ∧ modelCRule a b := by
 have h:=p2754 (fun _ : Nat=>(0:M)) t335 a b (literalC209Rules_certificate _)
 simpa [t3,t2,t0,t1,t16,literalCons_modelListCons,literalPair_modelCantor,literalCRule_pair,iff_iff_implies_and_implies] using h
lemma literalCTrace_modelTrace (n:M) : t172 t335 n ↔ modelTrace modelCRule n :=
 tracePredicate_unique_certificate modelCRule (t172 t335) (fun _=>0)
 (modelCRule_certificate _) (literalTraceValid_certificate (literalC209Rules_certificate _))
 ⟨literalCTrace_zero,literalCTrace_cons⟩ n
lemma literalCDerives_model (p r:M) : t336 p r ↔ modelTrace modelCRule p ∧ modelMember r p := by
 simp only [t336,t173,literalAnd_iff,literalCTrace_modelTrace,literalMember_modelMember]
lemma literalCProvable_model (r:M) : t337 r ↔ ∃p,modelTrace modelCRule p ∧ modelMember r p := by
 simp only [t337,t15,literalExists_iff,literalCDerives_model]
lemma literalCRefutation_model : t338 (M:=M) ↔ ∃p : M,modelTrace modelCRule p ∧ modelMember 1 p := by
 simpa only [t338,t303,t30,t29,t28,zero_add] using literalCProvable_model (M:=M) t303
end ZF209.MM0ModelReplay
