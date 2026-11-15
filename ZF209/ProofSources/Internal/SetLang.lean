module
public import Foundation.FirstOrder.SetTheory.Basic.Misc
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Coding
@[expose] public section
/-! # Internal syntax of the language of set theory

Foundation's internal syntax needs a Σ1 description of the symbols of a
language. `ℒₛₑₜ` has no function symbols and two binary relations, equality
(code 0) and membership (code 1). Every internal term is a variable. -/
namespace ZF209.Internal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

lemma set_relation_range {k r : ℕ} :
    r ∈ Set.range (Encodable.encode : (ℒₛₑₜ).Rel k → ℕ) ↔ k = 2 ∧ (r = 0 ∨ r = 1) := by
  constructor
  · rintro ⟨r, rfl⟩
    match k, r with
    | 2, Language.Set.Rel.eq => exact ⟨rfl, Or.inl rfl⟩
    | 2, Language.Set.Rel.mem => exact ⟨rfl, Or.inr rfl⟩
  · rintro ⟨rfl, rfl | rfl⟩
    · exact ⟨Language.Set.Rel.eq, rfl⟩
    · exact ⟨Language.Set.Rel.mem, rfl⟩

instance set_definable : (ℒₛₑₜ).LORDefinable where
  func := .mkSigma “k f. ⊥”
  rel := .mkSigma “k r. k = 2 ∧ (r = 0 ∨ r = 1)”
  func_iff {k c} := by
    simp only [Set.mem_range]
    constructor
    · rintro ⟨f, _⟩
      exact nomatch f
    · simp
  rel_iff {k c} := by simpa using! (set_relation_range (k := k) (r := c))

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] lemma set_no_func (k f : V) : ¬(ℒₛₑₜ).IsFunc k f := by
  change ¬(V ⊧/![k, f] (⊥ : ArithmeticSemisentence 2))
  simp

@[simp] lemma set_isRel (k r : V) : (ℒₛₑₜ).IsRel k r ↔ k = 2 ∧ (r = 0 ∨ r = 1) := by
  change (V ⊧/![k, r] “k r. k = 2 ∧ (r = 0 ∨ r = 1)”) ↔ _
  simp

/-- Every internal semiterm of `ℒₛₑₜ` is a variable. -/
lemma set_term_cases {n t : V} :
    IsSemiterm ℒₛₑₜ n t ↔ (∃ i < n, t = ^#i) ∨ ∃ i, t = ^&i := by
  rw [IsSemiterm.case_iff]
  simp

end ZF209.Internal
