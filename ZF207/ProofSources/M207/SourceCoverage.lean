module
public import M207.SourceCoverageFramework
public import M207.CheckedCoverage.Complete

@[expose] public section

namespace M207.Source.Coverage

open M6.Runtime CheckedCoverage

theorem coverage_of_check (pc fuel : Nat) (checked : siteCheck pc fuel = true) :
    M207.Source.CoverageAt program paths 4341 pc := by
  cases h : program pc with
  | none => simp [siteCheck, h] at checked
  | some code =>
    obtain ⟨bounded, _, verified⟩ := siteCheck_sound h checked
    refine ⟨code, h, bounded, ?_⟩
    cases code with
    | inc r k =>
      simp only [instructionCheck, Bool.and_eq_true, decide_eq_true_eq] at verified
      exact contract_inc paths (paths pc) r k fuel verified.1 verified.2
    | dec r z p =>
      simp only [instructionCheck, Bool.and_eq_true, decide_eq_true_eq] at verified
      exact contract_dec paths (paths pc) r z p fuel fuel verified.2.1 verified.2.2.1 verified.2.2.2
    | jump k =>
      simp only [instructionCheck, Bool.and_eq_true, decide_eq_true_eq] at verified
      exact contract_jump paths (paths pc) k fuel verified.2
    | halt => exact contract_halt paths (paths pc) fuel verified

theorem complete (i : Nat) (hi : i < 4341) : CoverageAt program paths 4341 i := by
  simpa only [Nat.zero_add] using of_blockCheck coverage_of_check fuelLimit 0 4341 allChecked i hi

theorem implementation : SourceSimulation.Implements literal (next program) (Valid 4341) (frame paths) := coverage_implements complete
theorem source_halts_iff (s : State) (hs : Valid 4341 s) : M6.Zip.Halts literal (frame paths s) ↔ SourceSimulation.Terminates (next program) s := SourceSimulation.halts_iff_source implementation hs
end M207.Source.Coverage
