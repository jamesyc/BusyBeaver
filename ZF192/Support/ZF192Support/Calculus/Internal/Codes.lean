module
public import ZF192Support.Coding.Pairing.Model
public import ZF192Support.Calculus.Standard.Kernel
public import ZF192Support.Calculus.Codes.Encoding
public import Mathlib.Tactic.Ring
@[expose] public section
/-! # The machine's code constructors in models of arithmetic

The machine codes formulas with the Cantor pairing: implication `4⟨a,b⟩`,
membership `4⟨a,b⟩+1`, quantification `4⟨a,x⟩+2` and equality `4⟨a,b⟩+3`.
This file defines the same constructors in every model of `𝗜𝚺₁`, with Σ0
definitions, and shows that in `ℕ` they are the machine's own. -/
namespace ZF192Support.Internal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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

lemma codes_nat : (codes : CKernel.Generic.Codes ℕ) = CKernel.natCodes := by
  have h1 : (imp : ℕ → ℕ → ℕ) = CCodeSoundness.impCode := by
    funext a b; simp [imp, CCodeSoundness.impCode, cantor_nat]
  have h2 : (mem : ℕ → ℕ → ℕ) = CCodeSoundness.memCode := by
    funext a b; simp [mem, CCodeSoundness.memCode, cantor_nat]
  have h3 : (eqc : ℕ → ℕ → ℕ) = CCodeSoundness.eqCode := by
    funext a b; simp [eqc, CCodeSoundness.eqCode, cantor_nat]
  have h4 : (all : ℕ → ℕ → ℕ) = CCodeSoundness.allCode := by
    funext a b; simp [all, CCodeSoundness.allCode, cantor_nat]
  simp only [codes, CKernel.natCodes, h1, h2, h3, h4]

end ZF192Support.Internal
