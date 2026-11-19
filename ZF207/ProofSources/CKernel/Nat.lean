module
public import CKernel.ImplicationBasis
public import CKernel.Generic
@[expose] public section
/-! # The machine's calculus on standard codes

`natSys` reads the generic calculus on `ℕ` with the machine's own provability
predicate `ExactProvable`. -/
namespace ZF207.CKernel
open C207Soundness

/-- The code constructors on standard codes. -/
def natCodes : Generic.Codes Nat where
  imp := impCode
  mem := memCode
  eq := eqCode
  all := allCode
  bot := 1

/-- The machine's calculus on standard codes. -/
def natSys : Generic.Sys Nat where
  toCodes := natCodes
  Prov := ExactProvable
  le := (· ≤ ·)
  mp := fun ha hab => provable_mp ha hab
  gen := fun x {_} h => provable_gen x h
  h1 := fun d h => (Derivation.h1 d h).provable
  h2 := fun d a h => (Derivation.h2 d a h).provable
  h3 := fun h d a => (Derivation.h3 h d a).provable
  h4 := fun h d a => (Derivation.h4 h d a).provable
  h5 := fun d h => (Derivation.h5 d h).provable
  h6 := fun d a h => (Derivation.h6 d a h).provable
  r8 := fun a b c u hu => (Derivation.r8 a b c u hu).provable
  gate := fun a b c hca hcb => (Derivation.gate a b c hca hcb).provable
  refl := Nat.le_refl
  boundLeft := fun b h => Dominated.le_l b h
  boundRight := fun a h => Dominated.le_r a h

end ZF207.CKernel
