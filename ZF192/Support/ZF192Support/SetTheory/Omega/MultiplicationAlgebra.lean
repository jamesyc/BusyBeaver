module
public import ZF192Support.SetTheory.Omega.Algebra
@[expose] public section
namespace ZF192Support.OmegaInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
attribute [local irreducible] add mul

theorem zero_mul (n : V) (hn : n ∈ (ω : V)) : mul 0 n = 0 := by
 apply naturalNumber_induction (fun n => mul 0 n = 0) ?_ ?_ ?_ n hn
 · definability
 · simp [← zero_def]
 · intro k hk ih
   rw [mul_succ _ _ hk, add_zero, ih]

theorem mul_one (a : V) (ha : a ∈ (ω : V)) : mul a (succ 0) = a := by
 rw [mul_succ _ _ zero_mem_ω, mul_zero]
 exact zero_add a ha

theorem one_mul (n : V) (hn : n ∈ (ω : V)) : mul (succ 0) n = n := by
 apply naturalNumber_induction (fun n => mul (succ 0) n = n) ?_ ?_ ?_ n hn
 · definability
 · simp [← zero_def]
 · intro k hk ih
   rw [mul_succ _ _ hk, add_succ _ _ zero_mem_ω, add_zero, ih]

theorem mul_add (a b n : V) (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) (hn : n ∈ (ω : V)) :
 mul a (add b n) = add (mul a b) (mul a n) := by
 apply naturalNumber_induction (fun n => mul a (add b n) = add (mul a b) (mul a n)) ?_ ?_ ?_ n hn
 · definability
 · simp [← zero_def]
 · intro k hk ih
   rw [add_succ _ _ hk, mul_succ _ _ (add_mem_omega b k hb hk), mul_succ _ _ hk,
     ih, add_assoc _ _ _ (mul_mem_omega a k ha hk) ha]

theorem succ_mul (a n : V) (ha : a ∈ (ω : V)) (hn : n ∈ (ω : V)) :
 mul (succ a) n = add (mul a n) n := by
 apply naturalNumber_induction (fun n => mul (succ a) n = add (mul a n) n) ?_ ?_ ?_ n hn
 · definability
 · simp [← zero_def]
 · intro k hk ih
   rw [mul_succ _ _ hk, ih, mul_succ _ _ hk, add_succ _ _ ha, add_succ _ _ hk]
   congr 1
   rw [add_assoc _ _ _ hk ha, add_comm k a hk ha, ← add_assoc _ _ _ ha hk]

theorem mul_comm (a n : V) (ha : a ∈ (ω : V)) (hn : n ∈ (ω : V)) : mul a n = mul n a := by
 apply naturalNumber_induction (fun n => mul a n = mul n a) ?_ ?_ ?_ n hn
 · definability
 · simpa [← zero_def] using (zero_mul a ha).symm
 · intro k hk ih
   rw [mul_succ _ _ hk, succ_mul k a hk ha, ih]

theorem add_mul (a b n : V) (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) (hn : n ∈ (ω : V)) :
 mul (add a b) n = add (mul a n) (mul b n) := by
 rw [mul_comm _ _ (add_mem_omega a b ha hb) hn, mul_add n a b hn ha hb,
   mul_comm n a hn ha, mul_comm n b hn hb]

theorem mul_assoc (a b n : V) (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) (hn : n ∈ (ω : V)) :
 mul (mul a b) n = mul a (mul b n) := by
 apply naturalNumber_induction (fun n => mul (mul a b) n = mul a (mul b n)) ?_ ?_ ?_ n hn
 · definability
 · simp [← zero_def]
 · intro k hk ih
   rw [mul_succ _ _ hk, mul_succ _ _ hk, mul_add _ _ _ ha (mul_mem_omega b k hb hk) hb, ih]
end ZF192Support.OmegaInterpretation
