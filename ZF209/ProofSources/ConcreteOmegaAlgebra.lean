module
public import ConcreteOmegaMultiplication
@[expose] public section
namespace ZF209.OmegaInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
attribute [local irreducible] add

theorem zero_add (n : V) (hn : n ∈ (ω : V)) : add 0 n = n := by
 apply naturalNumber_induction (fun n => add 0 n = n) ?_ ?_ ?_ n hn
 · definability
 · simp
 · intro k hk ih
   rw [add_succ _ _ hk, ih]

theorem succ_add (a n : V) (hn : n ∈ (ω : V)) :
 add (succ a) n = succ (add a n) := by
 apply naturalNumber_induction (fun n => add (succ a) n = succ (add a n)) ?_ ?_ ?_ n hn
 · definability
 · simp
 · intro k hk ih
   rw [add_succ _ _ hk, add_succ _ _ hk, ih]

theorem add_assoc (a b n : V) (hb : b ∈ (ω : V)) (hn : n ∈ (ω : V)) :
 add (add a b) n = add a (add b n) := by
 apply naturalNumber_induction (fun n => add (add a b) n = add a (add b n)) ?_ ?_ ?_ n hn
 · definability
 · simp
 · intro k hk ih
   rw [add_succ _ _ hk, add_succ b k hk, add_succ a _ (add_mem_omega b k hb hk), ih]

theorem add_comm (a n : V) (ha : a ∈ (ω : V)) (hn : n ∈ (ω : V)) :
 add a n = add n a := by
 apply naturalNumber_induction (fun n => add a n = add n a) ?_ ?_ ?_ n hn
 · definability
 · simp [zero_add a ha]
 · intro k hk ih
   rw [add_succ _ _ hk, succ_add k a ha, ih]
end ZF209.OmegaInterpretation
