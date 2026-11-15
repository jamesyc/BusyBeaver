module
public import Foundation.FirstOrder.Arithmetic.IOpen.Basic
public import CKernel.Nat
public import NumericCoding
public import Mathlib.Tactic.Ring
@[expose] public section
/-! # The machine's code constructors in models of arithmetic

The machine codes formulas with the Cantor pairing: implication `4⟨a,b⟩`,
membership `4⟨a,b⟩+1`, quantification `4⟨a,x⟩+2` and equality `4⟨a,b⟩+3`.
This file defines the same constructors in every model of `𝗜𝚺₁`, with Σ0
definitions, and shows that in `ℕ` they are the machine's own. -/
namespace ZF209.Internal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def cantorDef : 𝚺ᴬ₀.Semisentence 3 := .mkSigma “z a b. 2 * z = (a + b) * (a + b + 1) + 2 * b”

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma succ_product_even (s : V) : ∃ h : V, 2 * h = s * (s + 1) := by
  rcases even_or_odd s with ⟨x, rfl | rfl⟩
  · exact ⟨x * (2 * x + 1), by ring⟩
  · exact ⟨(2 * x + 1) * (x + 1), by ring⟩

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

/-- The machine's code constructors in `V`. -/
noncomputable def imp (a b : V) : V := 4 * cantor a b
noncomputable def mem (a b : V) : V := 4 * cantor a b + 1
noncomputable def all (x a : V) : V := 4 * cantor a x + 2
noncomputable def eqc (a b : V) : V := 4 * cantor a b + 3

end

def impDef : 𝚺ᴬ₀.Semisentence 3 := .mkSigma “y a b. ∃ c <⁺ y, !cantorDef c a b ∧ y = 4 * c”
def memDef : 𝚺ᴬ₀.Semisentence 3 := .mkSigma “y a b. ∃ c <⁺ y, !cantorDef c a b ∧ y = 4 * c + 1”
def allDef : 𝚺ᴬ₀.Semisentence 3 := .mkSigma “y x a. ∃ c <⁺ y, !cantorDef c a x ∧ y = 4 * c + 2”
def eqcDef : 𝚺ᴬ₀.Semisentence 3 := .mkSigma “y a b. ∃ c <⁺ y, !cantorDef c a b ∧ y = 4 * c + 3”

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma le_four_mul (c : V) : c ≤ 4 * c := le_mul_of_one_le_left (by simp) (by simp)

instance imp_defined : 𝚺ᴬ₀-Function₂ (imp : V → V → V) via impDef := .mk fun v => by
  simp [impDef, imp]; intro h; rw [h]; exact le_four_mul _

instance mem_defined : 𝚺ᴬ₀-Function₂ (mem : V → V → V) via memDef := .mk fun v => by
  simp [memDef, mem]; intro h; rw [h]; exact le_trans (le_four_mul _) (by simp)

instance all_defined : 𝚺ᴬ₀-Function₂ (all : V → V → V) via allDef := .mk fun v => by
  simp [allDef, all]; intro h; rw [h]; exact le_trans (le_four_mul _) (by simp)

instance eqc_defined : 𝚺ᴬ₀-Function₂ (eqc : V → V → V) via eqcDef := .mk fun v => by
  simp [eqcDef, eqc]; intro h; rw [h]; exact le_trans (le_four_mul _) (by simp)

/-- The generic code algebra on `V`; falsity is the code `1`. -/
noncomputable def codes : CKernel.Generic.Codes V where
  imp := imp
  mem := mem
  eq := eqc
  all := all
  bot := 1

end

/-! ## Agreement with the machine's codes in `ℕ` -/

lemma cantor_nat (a b : ℕ) : cantor a b = C209Soundness.cantor a b := by
  symm
  apply cantor_eq_iff.mpr
  show 2 * ((a + b) * (a + b + 1) / 2 + b) = (a + b) * (a + b + 1) + 2 * b
  have hm : (a + b) * (a + b + 1) % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one (a + b) with h | h <;> simp [Nat.mul_mod, Nat.add_mod, h]
  have := Nat.mod_add_div ((a + b) * (a + b + 1)) 2
  omega

lemma codes_nat : (codes : CKernel.Generic.Codes ℕ) = CKernel.natCodes := by
  have h1 : (imp : ℕ → ℕ → ℕ) = C209Soundness.impCode := by
    funext a b; simp [imp, C209Soundness.impCode, cantor_nat]
  have h2 : (mem : ℕ → ℕ → ℕ) = C209Soundness.memCode := by
    funext a b; simp [mem, C209Soundness.memCode, cantor_nat]
  have h3 : (eqc : ℕ → ℕ → ℕ) = C209Soundness.eqCode := by
    funext a b; simp [eqc, C209Soundness.eqCode, cantor_nat]
  have h4 : (all : ℕ → ℕ → ℕ) = C209Soundness.allCode := by
    funext a b; simp [all, C209Soundness.allCode, cantor_nat]
  simp only [codes, CKernel.natCodes, h1, h2, h3, h4]

end ZF209.Internal
