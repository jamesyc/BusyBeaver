module
public import Halting.Craig
public import Internal.Arith.AxStep
@[expose] public section
/-! # The theories `T` and `U`

* `T ι` (arithmetic): axioms `σ ⋏ ⊤ⁿ` where `n` is a C-trace of `chiS 0 (kax σ)`, i.e. of the
  translation of `∀e (Mark e → Ĵσ)`.
* `U ι` (set language): axioms `θ ⋏ ⊤ⁿ` where `n` is a C-trace of `chiS 0 θ` (everything C
  proves, Craig-padded).

Both are Δ1 by `craigTheory_delta1`. -/
namespace ZF207.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ZF207.Internal.Arith

/-- The identity code function. -/
def idFn : CodeFn where
  graph := .mkSigma “y x. y = x”
  f _ _ _ := id
  defined _ _ _ := .mk fun v => by simp

noncomputable def kaxDef (ι : Interp) : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “y σ. ∃ b, !qqBvarDef b 0 ∧ ∃ m, !(markAtDef ι) m b ∧ ∃ j, !(JDef ι) j b 1 σ ∧
    ∃ i, !(impGraph ℒₛₑₜ) i m j ∧ !qqAllDef y i”

/-- The code function `σ ↦ ⌜∀e (Mark e → Ĵσ)⌝`. -/
noncomputable def kaxFn (ι : Interp) : CodeFn where
  graph := kaxDef ι
  f _ _ _ := kax ι
  defined _ _ _ := .mk fun v => by
    simp [kaxDef, kax, jhat, (markAt_defined ι).iff, (J_defined ι).iff, imp.defined.iff]

variable (ι : Interp)

/-- The arithmetic theory: Craig-padded sentences whose marker translation C proves. -/
noncomputable def theoryT : ArithmeticTheory := craigTheory ℒₒᵣ (kaxFn ι)

noncomputable instance theoryT_delta1 : (theoryT ι).Δ₁ := craigTheory_delta1 ℒₒᵣ (kaxFn ι)

/-- The marker axiom `∃e Mark e`. -/
def markAx : Sentence ℒₛₑₜ := ∃¹ ι.mark

/-- The set-language theory: Craig-padded C-theorems. -/
noncomputable def theoryU : Theory ℒₛₑₜ := craigTheory ℒₛₑₜ idFn

noncomputable instance theoryU_delta1 : theoryU.Δ₁ := craigTheory_delta1 ℒₛₑₜ idFn

end ZF207.Halting
