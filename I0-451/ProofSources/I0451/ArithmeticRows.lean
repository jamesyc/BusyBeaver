module
public import I0451.Arithmetization

/-! The finite transition lookup at any standard control state has the
literal row value on all arithmetic tapes, including nonstandard ones. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem modelDigit_standard_bit (table q : Nat) (read : Bool) :
    modelDigit table (q : V) (read.toNat : V) = (I0451.row table q read : V) := by
  let d := I0451.row table q read
  have old : (rowDef table).val.Evalb (![d, q, read.toNat] : Fin 3 → Nat) := by
    apply (rowDef_eval table d q read.toNat).mpr
    rw [modelDigit_nat]
    cases read <;> rfl
  have lifted := bold_sigma_one_completeness' (M := V) (rowDef table).sigma_prop old
  have exactValues : (rowDef table).val.Evalb (![↑d, ↑q, ↑read.toNat] : Fin 3 → V) := by
    simpa [numeral_eq_natCast, Function.comp_def, Matrix.comp_vecCons', Matrix.vec_single_eq_const] using lifted
  exact ((rowDef_eval table (d : V) (q : V) (read.toNat : V)).mp exactValues).symm

theorem modelDigit_literal_row (table q : Nat) (tape : V) (read : Bool)
    (h : modelRem tape 2 = (read.toNat : V)) :
    modelDigit table (q : V) tape = (I0451.row table q read : V) := by
  have small : modelRem (read.toNat : V) 2 = (read.toNat : V) := by
    cases read <;> simp [modelRem]
  have same : modelDigit table (q : V) tape = modelDigit table (q : V) (read.toNat : V) := by
    unfold modelDigit
    rw [h, small]
  exact same.trans (modelDigit_standard_bit table q read)

theorem modelDigit_has_literal_read (table q : Nat) (tape : V) :
    ∃ read : Bool, modelRem tape 2 = (read.toNat : V) ∧
      modelDigit table (q : V) tape = (I0451.row table q read : V) := by
  rcases mod_two tape with low | high
  · have bit : modelRem tape 2 = ((false.toNat : Nat) : V) := by simpa [modelRem] using low
    exact ⟨false, bit, modelDigit_literal_row table q tape false bit⟩
  · have bit : modelRem tape 2 = ((true.toNat : Nat) : V) := by simpa [modelRem] using high
    exact ⟨true, bit, modelDigit_literal_row table q tape true bit⟩

end I0451.Arithmetization
