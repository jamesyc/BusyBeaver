module
public import ModelFormulaCertificates
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelPeano

/-- The first bound variable is the proposed unique witness; remaining bound
variables and all free parameters are preserved. -/
def descriptionUnique {n} (φ : ArithmeticSemiformula Nat (n+1)) :
 ArithmeticSemiformula Nat (n+1) :=
 φ ⋏ (∀¹ ((Rew.bind (L := ℒₒᵣ)
   (Semiterm.bvar 0 :> fun i => Semiterm.bvar i.succ.succ) Semiterm.fvar ▹ φ) 🡒 “#0 = #1”))

def descriptionExistsLift {n} (φ : ArithmeticSemiformula Nat (n+1)) :
 ArithmeticSemiformula Nat (n+1) :=
 Rew.bind (L := ℒₒᵣ) (fun i => Semiterm.bvar i.succ) Semiterm.fvar ▹
   (∃¹ descriptionUnique φ)

/-- Explicit arithmetic graph of MM0's unique-or-zero description operator.
Failure of uniqueness includes both empty and multiple-witness predicates. -/
def descriptionGraph {n} (φ : ArithmeticSemiformula Nat (n+1)) :
 ArithmeticSemiformula Nat (n+1) :=
 descriptionUnique φ ⋎ (“#0 = 0” ⋏ ∼descriptionExistsLift φ)

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma descriptionUnique_eval {n} (φ : ArithmeticSemiformula Nat (n+1))
 (e : Nat → M) (y : M) (v : Fin n → M) :
 (descriptionUnique φ).Eval (y :> v) e ↔
 φ.Eval (y :> v) e ∧ ∀x,φ.Eval (x :> v) e → x=y := by
 simp [descriptionUnique,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons']

lemma descriptionExistsLift_eval {n} (φ : ArithmeticSemiformula Nat (n+1))
 (e : Nat → M) (y : M) (v : Fin n → M) :
 (descriptionExistsLift φ).Eval (y :> v) e ↔
 ∃x,φ.Eval (x :> v) e ∧ ∀z,φ.Eval (z :> v) e → z=x := by
 rw [descriptionExistsLift,Semiformula.eval_rew]
 simp [descriptionUnique_eval,Function.comp_def,Matrix.comp_vecCons']

lemma descriptionGraph_eval {n} (φ : ArithmeticSemiformula Nat (n+1))
 (e : Nat → M) (y : M) (v : Fin n → M) :
 (descriptionGraph φ).Eval (y :> v) e ↔
 (φ.Eval (y :> v) e ∧ ∀x,φ.Eval (x :> v) e → x=y) ∨
 (y=0 ∧ ¬∃x,φ.Eval (x :> v) e ∧ ∀z,φ.Eval (z :> v) e → z=x) := by
 simp [descriptionGraph,descriptionUnique_eval,descriptionExistsLift_eval]

lemma the_graph (P : M → Prop) (y : M) :
 ((P y ∧ ∀x,P x → x=y) ∨ (y=0 ∧ ¬∃a,P a ∧ ∀x,P x → x=a)) ↔ y=the P := by
 classical
 by_cases h : ∃a,∀x,P x ↔ x=a
 · obtain ⟨a,ha⟩ := h
   have ht : the P=a := theid P a ((eqs_iff _ _).mpr ha)
   rw [ht]
   constructor
   · rintro (⟨hy,_⟩ | ⟨_,hn⟩)
     · exact (ha y).mp hy
     · exact False.elim (hn ⟨a,(ha a).mpr rfl,fun x hx => (ha x).mp hx⟩)
   · intro hy
     subst y
     exact Or.inl ⟨(ha a).mpr rfl,fun x hx => (ha x).mp hx⟩
 · have hn : ¬∃a,P a ∧ ∀x,P x → x=a := by
     rintro ⟨a,ha,hu⟩
     apply h
     refine ⟨a,fun x => ⟨hu x,?_⟩⟩
     intro hx
     simpa only [hx] using ha
   have ht : the P=0 := by simp only [the,dite_eq_right h]
   rw [ht]
   constructor
   · rintro (⟨hy,hu⟩ | ⟨hy,_⟩)
     · exact False.elim (hn ⟨y,hy,hu⟩)
     · exact hy
   · intro hy
     exact Or.inr ⟨hy,hn⟩

namespace FormulaCertificate
end FormulaCertificate
end ZF207.MM0ModelPeano
