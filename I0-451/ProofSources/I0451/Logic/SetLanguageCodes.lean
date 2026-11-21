module
public import Foundation.FirstOrder.SetTheory.Basic.Misc
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Coding
public import Foundation.FirstOrder.Syntax.Classical.PrimrecCoding

/-! The membership language has no function symbols and two binary
relation symbols. The same encodings work in the arithmetic syntax
library and in its standard computability model. -/
@[expose] public section
namespace I0451.Logic

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

theorem setLanguage_relationCode {arity code : Nat} :
    code ∈ Set.range (Encodable.encode : (ℒₛₑₜ).Rel arity → Nat) ↔
      arity = 2 ∧ (code = 0 ∨ code = 1) := by
  constructor
  · rintro ⟨r, rfl⟩
    cases r
    · exact ⟨rfl, Or.inl rfl⟩
    · exact ⟨rfl, Or.inr rfl⟩
  · rintro ⟨rfl, rfl | rfl⟩
    · exact ⟨Language.Set.Rel.eq, rfl⟩
    · exact ⟨Language.Set.Rel.mem, rfl⟩

instance : (ℒₛₑₜ).LORDefinable where
  func := .mkSigma “arity code. ⊥”
  rel := .mkSigma “arity code. arity = 2 ∧ (code = 0 ∨ code = 1)”
  func_iff := by simp
  rel_iff {k c} := by simpa [models_iff] using! (setLanguage_relationCode (arity := k) (code := c))

instance : (ℒₛₑₜ).Primcodable where
  func := by
    have constant : Primrec fun _ : Nat × Nat => (0 : Nat) := Primrec.const _
    refine constant.of_eq ?_
    rintro ⟨arity, code⟩
    simp [Encodable.decode]
  rel := by
    have decodeCode : Primrec fun p : Nat × Nat =>
      if p.1 = 2 ∧ p.2 < 2 then p.2 + 1 else 0 := by primrec
    refine decodeCode.of_eq ?_
    rintro ⟨arity, code⟩
    match arity, code with
    | 0, _ => simp [Encodable.decode]
    | 1, _ => simp [Encodable.decode]
    | 2, 0 => rfl
    | 2, 1 => rfl
    | 2, _ + 2 => simp [Encodable.decode]
    | _ + 3, _ => simp [Encodable.decode]

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

end I0451.Logic
