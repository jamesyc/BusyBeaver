module
public import ModelTraceDefinitions
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def literalTraceStepValue_certificate {e : Nat → M} {A : M → Prop}
 (a : FormulaCertificate e 1 (fun v=>A (v 0))) :
 FunctionGraphCertificate e 1 (fun v=>t53 (t2 (t51 (t69 (v 0))) (t16 (t63 (t64 (v 0)) (t68 (v 0))) A))) := by
 let fst := literalFst_certificate e
 let snd := literalSnd_certificate e
 refine ⟨“y x. ∃u, ∃bc, ∃b, ∃c, ∃p,
 !fst.formula u x ∧ !snd.formula bc x ∧ !fst.formula b bc ∧ !snd.formula c bc ∧ !literalPairGraph p u b ∧
 (((c≠0 ∧ !a.formula p) ∧ y=1) ∨ (¬(c≠0 ∧ !a.formula p) ∧ y=0))”,?_⟩
 intro v y
 have hl (u k:M) := fst.correct ![k] u
 have hr (u k:M) := snd.correct ![k] u
 have ha (p:M) : a.formula.Eval ![p] e ↔ A p := (a.correct ![p]).symm
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,hv,hl,hr,ha,literalPairGraph_eval]
 classical
 simp only [t53,literalConditional_value,t2,t1,t0,t51,t13,t10,t28,t30,t29,t68,t69,t16]
 by_cases hc : t65 (t65 (v 0))=0 <;> by_cases hp : A (t63 (t64 (v 0)) (t64 (t65 (v 0)))) <;> simp_all
noncomputable def literalTraceStep_certificate {e : Nat → M} {A : M → Prop}
 (a : FormulaCertificate e 1 (fun v=>A (v 0))) :
 FormulaCertificate e 1 (fun v=>t170 A (v 0)) :=
 literalGraph_certificate (F := fun x=>t53 (t2 (t51 (t69 x)) (t16 (t63 (t64 x) (t68 x)) A))) (literalTraceStepValue_certificate a)
end ZF207.MM0ModelReplay
