module
public import ModelPredicateOrderInduction
public import ExactSourceWfSentences
public import ExactContextWfSentences
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
open ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Explicit model recurrences, to be discharged by the actual MM0 interpretation. -/
structure SourceWfPredicateRecurrences (P : M → Prop) : Prop where
 zero : P 0
 node : ∀t a b,t<8 → 0<modelSourceNode t a b →
  (P (modelSourceNode t a b) ↔ (t=1 ∨ t=2) ∨
   ((t=3 ∨ t=4 ∨ t=5) ∧ P a ∧ P b) ∨ ((t=6 ∨ t=7) ∧ b=0 ∧ P a))
def certificateOfDefinedPred (e : Nat → M) (φ : 𝚺ᴬ₁.Semisentence 1) (Q : M → Prop)
 (hQ : 𝚺ᴬ₁.DefinedPred Q φ) : FormulaCertificate e 1 (fun v=>Q (v 0)) := {
 formula := (FormulaCertificate.fromSemisentence e φ.val).formula
 correct := fun v => hQ.iff.symm.trans ((FormulaCertificate.fromSemisentence e φ.val).correct v) }
/-- Genuine PA order induction on explicit syntax; not external well-foundedness. -/
theorem sourceWfPredicate_unique (P : M → Prop) (e : Nat → M)
 (cert : FormulaCertificate e 1 (fun v=>P (v 0)))
 (hr : SourceWfPredicateRecurrences P) : ∀n,P n ↔ modelSourceWf n := by
 let q := certificateOfDefinedPred e sourceWfFormula modelSourceWf sourceWfFormula_defined
 have c := cert.iffCert q
 apply c.orderInduction
 intro n ih
 change P n ↔ modelSourceWf n
 change ∀y<n,P y ↔ modelSourceWf y at ih
 by_cases hz:n=0
 · subst n; exact iff_of_true hr.zero modelSourceWf_zero
 · obtain ⟨t,a,b,ht,he⟩ := modelSourceNode_surjective n
   have hp : 0<modelSourceNode t a b := he ▸ pos_iff_ne_zero.mpr hz
   have ha : a<n := he ▸ modelSourceNode_left_lt t a b hp
   have hb : b<n := he ▸ modelSourceNode_right_lt t a b hp
   rw [he,hr.node t a b ht hp,modelSourceWf_node t a b ht hp,ih a ha,ih b hb]
structure ContextWfPredicateRecurrences (P : M → Prop) : Prop where
 zero : P 0
 cons : ∀a b,P (modelListCons a b) ↔ modelSourceWf a ∧ P b
structure TracePredicateRecurrences (R : M → M → Prop) (P : M → Prop) : Prop where
 zero : P 0
 cons : ∀a b,P (modelListCons a b) ↔ P b ∧ R a b
theorem tracePredicate_unique (R : M → M → Prop) (rel : 𝚺ᴬ₁.Semisentence 2)
 (hR : 𝚺ᴬ₁.DefinedRel R rel) (P : M → Prop) (e : Nat → M)
 (cert : FormulaCertificate e 1 (fun v=>P (v 0))) (hr : TracePredicateRecurrences R P) :
 ∀n,P n ↔ modelTrace R n := by
 let q := certificateOfDefinedPred e (traceFormula rel) (modelTrace R) (traceFormula_defined rel R hR)
 apply (cert.iffCert q).orderInduction
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
