module
public import ModelSourcePredicateUniqueness
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
open ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def modelTrace_certificate {e : Nat → M} {R : M → M → Prop}
 (rel : FormulaCertificate e 2 (fun v=>R (v 0) (v 1))) :
 FormulaCertificate e 1 (fun v=>modelTrace R (v 0)) := by
 refine ⟨“n. !tailIterationGraph 0 n n ∧ ∀ k<n, ∃ g, !tailIterationGraph g k n ∧
 (g=0 ∨ ∃ a, ∃ b, !listHeadGraph a g ∧ !listTailGraph b g ∧ !rel.formula a b)”,?_⟩
 intro v
 have hr (a b:M) : rel.formula.Eval ![a,b] e ↔ R a b := (rel.correct ![a,b]).symm
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [hv,modelTrace,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,
 tailIterationGraph_defined.iff,ruleHead_defined.iff,ruleTail_defined.iff,hr,eq_comm]
theorem tracePredicate_unique_certificate (R : M → M → Prop) (P : M → Prop) (e : Nat → M)
 (rel : FormulaCertificate e 2 (fun v=>R (v 0) (v 1)))
 (cert : FormulaCertificate e 1 (fun v=>P (v 0))) (hr : TracePredicateRecurrences R P) :
 ∀n,P n ↔ modelTrace R n := by
 apply (cert.iffCert (modelTrace_certificate rel)).orderInduction
 intro n ih
 change P n ↔ modelTrace R n
 by_cases hz:n=0
 · subst n; exact iff_of_true hr.zero (modelTrace_zero R)
 · have hp:0<n := pos_iff_ne_zero.mpr hz
   have he:n=modelListCons (modelListHead n) (modelListTail n) := (modelList_reconstruct n hp).symm
   have ht := modelListTail_lt n hp
   rw [he,hr.cons,modelTrace_cons]
   exact and_congr (ih (modelListTail n) ht) Iff.rfl
end ZFR.ArithmeticRepresentation
