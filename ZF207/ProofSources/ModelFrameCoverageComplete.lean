module
public import ModelFrameCoverageFramework
public import M207.CheckedCoverage.Complete

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace ZF207.BinaryTape.FrameCoverage

open M207.Source M207.Source.CheckedCoverage M6.Runtime

theorem coverage_of_check {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (pc fuel : Nat) (checked : siteCheck pc fuel = true) :
    BinaryTape.FrameCoverage.CoverageAt (M := M) pc := by
  cases h : program pc with
  | none => simp [siteCheck, h] at checked
  | some code =>
    obtain ⟨bounded, start, verified⟩ := siteCheck_sound h checked
    refine ⟨code, h, ?_⟩
    cases code with
    | inc r k =>
      simp only [instructionCheck, Bool.and_eq_true, decide_eq_true_eq] at verified
      exact model_contract_inc pc r k fuel start verified.1 bounded.1 verified.2
    | dec r z p =>
      simp only [instructionCheck, Bool.and_eq_true, decide_eq_true_eq] at verified
      exact model_contract_dec pc r z p fuel fuel start verified.1 verified.2.1
        bounded.1 verified.2.2.1 verified.2.2.2
    | jump k =>
      simp only [instructionCheck, Bool.and_eq_true, decide_eq_true_eq] at verified
      exact model_contract_jump pc k fuel start verified.1 verified.2
    | halt => exact model_contract_halt pc fuel start verified

theorem complete {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (i : Nat) (hi : i < 4341) : CoverageAt (M := M) i := by
  simpa only [Nat.zero_add] using
    of_blockCheck (coverage_of_check (M := M)) fuelLimit 0 4341 allChecked i hi

end ZF207.BinaryTape.FrameCoverage
