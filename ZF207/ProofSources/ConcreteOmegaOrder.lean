module
public import ConcreteOmegaAlgebra
@[expose] public section
namespace ZF207.OmegaInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
theorem omega_lt_irrefl (a : V) : ¬ a ∈ a := mem_irrefl a
theorem omega_lt_trans (a b c : V) (hc : c ∈ (ω : V))
 (hab : a ∈ b) (hbc : b ∈ c) : a ∈ c :=
 (IsTransitive.nat hc).mem_trans hab hbc
theorem omega_lt_trichotomy (a b : V) (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) :
 a ∈ b ∨ a=b ∨ b ∈ a := by
 letI : IsOrdinal a := IsOrdinal.nat ha
 letI : IsOrdinal b := IsOrdinal.nat hb
 exact IsOrdinal.mem_trichotomy (α := a) (β := b)
theorem omega_zero_le (a : V) (ha : a ∈ (ω : V)) : ¬ a ∈ (0 : V) := by
 simp [zero_def]
theorem omega_zero_lt_one : (0 : V) ∈ (1 : V) := zero_mem_one
end ZF207.OmegaInterpretation
