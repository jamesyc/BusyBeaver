module

public import User211SourceCalibration
public import PA211.UserCandidate.KernelEndpoint

@[expose] public section
namespace PA211.UserCandidate.PA
/-- Ordinary PA consistency, not consistency of Lean, supplies exact blank nonhalting. -/
theorem consistent_machine_nonhalting (hcons : PA215.PA.Consistent) :
    ¬ PA215.Zip.Halts CandidateTable.machine PA213.Startup.blank :=
  NonhaltingFromSource.blank_nonhalting (Source.consistent_baseline_startup_nonhalting hcons)
/-- The same statement for the literal user control labels and blank start0. -/
theorem consistent_literal_nonhalting (hcons : PA215.PA.Consistent) :
    ¬ PA215.Zip.Halts Dense.machine (PA215.Zip.zc 0 [] []) :=
  NonhaltingFromSource.literal_blank_nonhalting (Source.consistent_baseline_startup_nonhalting hcons)
#print axioms consistent_machine_nonhalting
#print axioms consistent_literal_nonhalting
end PA211.UserCandidate.PA
