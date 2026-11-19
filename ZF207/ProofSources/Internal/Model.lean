module
public import Internal.Connectives
public import Foundation.FirstOrder.Arithmetic.Definability.Absoluteness
@[expose] public section
/-! # The machine's calculus in a model of arithmetic

`ProvRules D V` says that the Σ1 formula `D` defines, in `V`, a predicate on codes
closed under the machine's rules. Such a predicate is a `Sys V` whose codes are
`Internal.codes`, so the generic kernel applies to it. When `D` defines the
machine's provability in `ℕ`, every standard theorem of the machine is a
`D`-theorem of `V` (Σ1 upward absoluteness), and code constructors commute with
the embedding of `ℕ`. -/
namespace ZF207.Internal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open CKernel.Generic

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma le_cantor_left (a b : V) : a ≤ cantor a b := by
  have h := two_mul_cantor a b
  have h2 : 2 * a ≤ 2 * cantor a b := by
    rw [h]
    calc 2 * a ≤ 2 * (a + b) := by simp
      _ = (a + b) + (a + b) := two_mul _
      _ ≤ (a + b) * (a + b) + (a + b) := by simp
      _ = (a + b) * (a + b + 1) := by rw [mul_add (a + b) (a + b) 1, mul_one]
      _ ≤ (a + b) * (a + b + 1) + 2 * b := by simp
  exact le_of_mul_le_mul_left h2 (by simp)

lemma le_cantor_right (a b : V) : b ≤ cantor a b := by
  have h := two_mul_cantor a b
  have h2 : 2 * b ≤ 2 * cantor a b := by rw [h]; simp
  exact le_of_mul_le_mul_left h2 (by simp)

lemma left_le_imp (a b : V) : a ≤ imp a b := le_trans (le_cantor_left a b) (le_four_mul _)
lemma right_le_imp (a b : V) : b ≤ imp a b := le_trans (le_cantor_right a b) (le_four_mul _)

end

/-! ## Casting standard codes -/

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] lemma cast_imp (a b : ℕ) : ((imp a b : ℕ) : V) = imp (a : V) (b : V) := by
  simpa [Function.comp_def] using
    DefinedFunction.sigmaZero_absolute_func (V := V) (imp_defined (V := ℕ)) imp_defined ![a, b]

@[simp] lemma cast_mem (a b : ℕ) : ((mem a b : ℕ) : V) = mem (a : V) (b : V) := by
  simpa [Function.comp_def] using
    DefinedFunction.sigmaZero_absolute_func (V := V) (mem_defined (V := ℕ)) mem_defined ![a, b]

@[simp] lemma cast_all (a b : ℕ) : ((all a b : ℕ) : V) = all (a : V) (b : V) := by
  simpa [Function.comp_def] using
    DefinedFunction.sigmaZero_absolute_func (V := V) (all_defined (V := ℕ)) all_defined ![a, b]

@[simp] lemma cast_eqc (a b : ℕ) : ((eqc a b : ℕ) : V) = eqc (a : V) (b : V) := by
  simpa [Function.comp_def] using
    DefinedFunction.sigmaZero_absolute_func (V := V) (eqc_defined (V := ℕ)) eqc_defined ![a, b]

@[simp] lemma cast_cneg (a : ℕ) : ((cneg a : ℕ) : V) = cneg (a : V) := by simp [cneg]
@[simp] lemma cast_cand (a b : ℕ) : ((cand a b : ℕ) : V) = cand (a : V) (b : V) := by simp [cand]
@[simp] lemma cast_cor (a b : ℕ) : ((cor a b : ℕ) : V) = cor (a : V) (b : V) := by simp [cor]
@[simp] lemma cast_cex (a b : ℕ) : ((cex a b : ℕ) : V) = cex (a : V) (b : V) := by simp [cex]
@[simp] lemma cast_ciff (a b : ℕ) : ((ciff a b : ℕ) : V) = ciff (a : V) (b : V) := by simp [ciff]

end

/-! ## Provability predicates closed under the rules -/

/-- `D` defines in `V` a predicate closed under the machine's rules. -/
structure ProvRules (D : 𝚺ᴬ₁.Semisentence 1) (V : Type*) [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : Prop where
  mp {a b : V} : D.val.Evalb ![a] → D.val.Evalb ![imp a b] → D.val.Evalb ![b]
  gen (x : V) {a : V} : D.val.Evalb ![a] → D.val.Evalb ![all x a]
  h1 (d h : V) : D.val.Evalb ![(codes : Codes V).head1 d h]
  h2 (d a h : V) : D.val.Evalb ![(codes : Codes V).head2 d a h]
  h3 (h d a : V) : D.val.Evalb ![(codes : Codes V).head3 h d a]
  h4 (h d a : V) : D.val.Evalb ![(codes : Codes V).head4 h d a]
  h5 (d h : V) : D.val.Evalb ![(codes : Codes V).head5 d h]
  h6 (d a h : V) : D.val.Evalb ![(codes : Codes V).head6 d a h]
  r8 (a b c u : V) : u ≤ a → D.val.Evalb ![(codes : Codes V).rho8 a b c u]
  gate (a b c : V) : c ≠ a → c ≠ b → D.val.Evalb ![(codes : Codes V).bundle a b c]

variable {D : 𝚺ᴬ₁.Semisentence 1} {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The generic calculus read in `V`. -/
noncomputable def ProvRules.sys (h : ProvRules D V) : Sys V where
  toCodes := codes
  Prov x := D.val.Evalb ![x]
  le := (· ≤ ·)
  mp := h.mp
  gen := h.gen
  h1 := h.h1
  h2 := h.h2
  h3 := h.h3
  h4 := h.h4
  h5 := h.h5
  h6 := h.h6
  r8 := h.r8
  gate := h.gate
  refl := le_refl
  boundLeft := fun b hu => le_trans hu (left_le_imp _ b)
  boundRight := fun a hu => le_trans hu (right_le_imp a _)

/-- A standard code that `D` accepts in `ℕ` is accepted in `V`. -/
lemma prov_of_nat (n : ℕ) (hn : D.val.Evalb ![n]) : D.val.Evalb (M := V) ![(n : V)] := by
  simpa [Function.comp_def, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
    sigmaOne_upward_absolute (V := V) D ![n] hn

end ZF207.Internal
