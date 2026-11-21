module
public import I0451.Standalone.ArithmeticSyntax
public import Foundation.FirstOrder.SetTheory.FunctionSet
@[expose] public section
namespace I0451.Standalone
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭]
local notation "E" => (fun x y : V => x ∈ y)
lemma empty_iff (a : V) : Empty E a ↔ a = ∅ := by
 constructor
 · intro h; ext x; simpa using h x
 · rintro rfl; simp [Empty]
lemma succ_iff (a b : V) : Succ E a b ↔ b = SetTheory.succ a := by
 constructor
 · intro h; ext x; simpa only [mem_succ_iff, or_comm] using h x
 · rintro rfl; intro x; simp only [mem_succ_iff, or_comm]
lemma pair_iff (a b p : V) : Pair E a b p ↔ p = {a,b} := by
 constructor
 · intro h; ext x; simpa using h x
 · rintro rfl; intro x; simp
lemma orderedPair_iff (a b p : V) : OrderedPair E a b p ↔ p = ⟨a,b⟩ₖ := by
 simp only [OrderedPair,pair_iff]
 constructor
 · rintro ⟨aa,ab,rfl,rfl,h⟩; simpa [kpair] using h
 · intro h; exact ⟨{a,a},{a,b},rfl,rfl,by simpa [kpair] using h⟩
lemma at_iff (f x y : V) : At E f x y ↔ ⟨x,y⟩ₖ ∈ f := by
 simp only [At,orderedPair_iff]
 constructor
 · rintro ⟨p,h,rfl⟩; exact h
 · intro h; exact ⟨_,h,rfl⟩
lemma functionOn_iff (f d : V) : FunctionOn E f d ↔ IsFunction f ∧ domain f = d := by
 simp only [FunctionOn,at_iff,orderedPair_iff]
 constructor
 · rintro ⟨ht,hp⟩
   have hf : f ∈ range f ^ d := by
    apply mem_function.intro
    · intro p h
      obtain ⟨x,y,hx,rfl⟩ := hp p h
      exact (mem_prod_iff).mpr ⟨x,hx,y,mem_range_of_kpair_mem h,rfl⟩
    · intro x hx; exact ht x hx
   exact ⟨IsFunction.of_mem hf,domain_eq_of_mem_function hf⟩
 · rintro ⟨hf,hd⟩
   letI := hf
   constructor
   · intro x hx
     exact exists_unique_of_mem_function (IsFunction.mem_function f) x (hd.symm ▸ hx)
   · intro p hp
     obtain ⟨x,y,rfl⟩ := IsFunction.mem_eq_kpair hp
     exact ⟨x,y,hd ▸ mem_domain_of_kpair_mem hp,rfl⟩
lemma inductive_iff (a : V) : Inductive E a ↔ IsInductive a := by
 simp only [Inductive,empty_iff,succ_iff]
 constructor
 · rintro ⟨⟨z,rfl,hz⟩,hs⟩
   exact ⟨hz,fun x hx => by obtain ⟨y,rfl,hy⟩ := hs x hx; exact hy⟩
 · intro h
   exact ⟨⟨∅,rfl,h.1⟩,fun x hx => ⟨_,rfl,h.2 x hx⟩⟩
lemma omega_iff (w : V) : Omega E w ↔ w = ω := by
 simp only [Omega,inductive_iff]
 constructor
 · rintro ⟨hi,hm⟩
   ext x
   exact ⟨fun hx => hm ω ω_isInductive x hx,fun hx => hi.ω_subset x hx⟩
 · rintro rfl
   exact ⟨ω_isInductive,fun a ha x hx => ha.ω_subset x hx⟩
lemma natObject_iff (x : V) : NatObject E x ↔ x ∈ (ω : V) := by
 simp only [NatObject,omega_iff]
 constructor
 · rintro ⟨w,rfl,h⟩; exact h
 · intro h; exact ⟨ω,rfl,h⟩
lemma numeral_iff (n : Nat) (x : V) : Numeral E n x ↔ x = (n : V) := by
 induction n generalizing x with
 | zero =>
   change Empty E x ↔ x = ((0 : Nat) : V)
   simpa only [cast_zero_def,zero_def] using empty_iff x
 | succ n ih =>
   change (∃ y, Numeral E n y ∧ Succ E y x) ↔ x = ((n+1 : Nat) : V)
   simp only [ih,succ_iff,num_succ_def]
   constructor
   · rintro ⟨y,rfl,h⟩; exact h
   · intro h; exact ⟨_,rfl,h⟩
end I0451.Standalone
