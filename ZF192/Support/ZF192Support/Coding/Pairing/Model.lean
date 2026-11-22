module
public import Foundation.FirstOrder.Arithmetic.IOpen.Basic
public import ZF192Support.Coding.Pairing.Standard
@[expose] public section

/-! # Cantor pairing in models of arithmetic -/

namespace ZF192Support.Internal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def cantorDef : 𝚺ᴬ₀.Semisentence 3 := .mkSigma “z a b. 2 * z = (a + b) * (a + b + 1) + 2 * b”

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma succ_product_even (s : V) : ∃ h : V, 2 * h = s * (s + 1) := by
  have h : Even (s * (s + 1)) := by
    obtain ⟨x, hx | hx⟩ := even_or_odd s
    · exact (even_iff_two_dvd.mpr ⟨x, hx⟩).mul_right _
    · exact (show Odd s from ⟨x, hx⟩).add_one.mul_left _
  obtain ⟨x, hx⟩ := even_iff_two_dvd.mp h
  exact ⟨x, hx.symm⟩

lemma cantor_existsUnique (a b : V) : ∃! z : V, 2 * z = (a + b) * (a + b + 1) + 2 * b := by
  obtain ⟨h, hh⟩ := succ_product_even (a + b)
  refine ⟨h + b, ?_, fun y hy => ?_⟩
  · show 2 * (h + b) = _
    rw [mul_add, hh]
  · show y = h + b
    apply mul_left_cancel₀ (by simp : (2 : V) ≠ 0)
    rw [show 2 * y = _ from hy, mul_add (2 : V) h b, hh]

/-- Cantor pairing in a model. -/
noncomputable def cantor (a b : V) : V := Classical.choose! (cantor_existsUnique a b)

lemma two_mul_cantor (a b : V) : 2 * cantor a b = (a + b) * (a + b + 1) + 2 * b :=
  Classical.choose!_spec (cantor_existsUnique a b)

lemma cantor_eq_iff {a b z : V} : z = cantor a b ↔ 2 * z = (a + b) * (a + b + 1) + 2 * b :=
  ⟨fun h => h ▸ two_mul_cantor a b,
    fun h => (cantor_existsUnique a b).unique h (two_mul_cantor a b)⟩

instance cantor_defined : 𝚺ᴬ₀-Function₂ (cantor : V → V → V) via cantorDef :=
  .mk fun v => by simp [cantorDef, cantor_eq_iff]

end

lemma cantor_nat (a b : ℕ) : cantor a b = CCodeSoundness.cantor a b := by
  exact (cantor_eq_iff.mpr (CCodeSoundness.cantor_double a b)).symm

end ZF192Support.Internal
