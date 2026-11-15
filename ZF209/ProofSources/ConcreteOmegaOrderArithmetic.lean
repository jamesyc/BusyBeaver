module
public import ConcreteOmegaOrder
public import ConcreteOmegaMulAlgebra
@[expose] public section
namespace ZF209.OmegaInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
attribute [local irreducible] add mul

theorem omega_succ_lt_succ (a b : V) (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V))
 (h : a ∈ b) : succ a ∈ succ b := by
 letI : IsOrdinal a := IsOrdinal.nat ha
 letI : IsOrdinal b := IsOrdinal.nat hb
 exact mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (Ordinal.subset_succ_iff.mpr h))

theorem add_lt_add_right (a b n : V) (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V))
 (hn : n ∈ (ω : V)) (hab : a ∈ b) : add a n ∈ add b n := by
 apply naturalNumber_induction (fun n => add a n ∈ add b n) ?_ ?_ ?_ n hn
 · definability
 · simpa using hab
 · intro k hk ih
   rw [add_succ _ _ hk, add_succ _ _ hk]
   exact omega_succ_lt_succ _ _ (add_mem_omega a k ha hk) (add_mem_omega b k hb hk) ih

theorem add_lt_add_left (a b n : V) (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V))
 (hn : n ∈ (ω : V)) (hab : a ∈ b) : add n a ∈ add n b := by
 rw [add_comm n a hn ha, add_comm n b hn hb]
 exact add_lt_add_right a b n ha hb hn hab

theorem omega_add_difference (a b : V) (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V))
 (hab : a ∈ b) : ∃ d : V, d ∈ (ω : V) ∧ b = add a (succ d) := by
 have H : ∀ b : V, b ∈ (ω : V) → ∀ a : V, a ∈ (ω : V) → a ∈ b →
     ∃ d : V, d ∈ (ω : V) ∧ b = add a (succ d) := by
  apply naturalNumber_induction
    (fun b => ∀ a : V, a ∈ (ω : V) → a ∈ b → ∃ d : V, d ∈ (ω : V) ∧ b = add a (succ d))
  · definability
  · intro a _ h
    simpa [zero_def] using h
  · intro k hk ih a ha hak
    rcases mem_succ_iff.mp hak with rfl | hak
    · exact ⟨0, zero_mem_ω, by rw [add_succ _ _ zero_mem_ω, add_zero]⟩
    · obtain ⟨d,hd,he⟩ := ih a ha hak
      exact ⟨succ d, ω_succ_closed hd, by rw [add_succ _ _ (ω_succ_closed hd), ← he]⟩
 exact H b hb a ha hab
theorem mul_lt_mul_right (a b n : V) (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V))
 (hn : n ∈ (ω : V)) (hab : a ∈ b) (hn0 : n ≠ 0) : mul a n ∈ mul b n := by
 have H : ∀ n : V, n ∈ (ω : V) → n = 0 ∨ mul a n ∈ mul b n := by
  apply naturalNumber_induction (fun n => n = 0 ∨ mul a n ∈ mul b n)
  · definability
  · exact Or.inl rfl
  · intro k hk ih
    apply Or.inr
    rcases ih with rfl | ih
    · simpa [mul_one a ha, mul_one b hb] using hab
    · rw [mul_succ _ _ hk, mul_succ _ _ hk]
      have h1 := add_lt_add_right _ _ a (mul_mem_omega a k ha hk) (mul_mem_omega b k hb hk) ha ih
      have h2 := add_lt_add_left a b (mul b k) ha hb (mul_mem_omega b k hb hk) hab
      exact omega_lt_trans _ _ _ (add_mem_omega _ _ (mul_mem_omega b k hb hk) hb) h1 h2
 exact (H n hn).resolve_left hn0

end ZF209.OmegaInterpretation
