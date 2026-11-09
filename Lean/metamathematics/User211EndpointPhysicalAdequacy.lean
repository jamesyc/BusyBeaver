module

/- Exact211: fresh physical interpretation of the unchanged original coded source. -/
public import User211EndpointPaddedNatTape
public import PA213.StartupData

@[expose] public section
namespace PA211.UserCandidate.PA.PhysicalAdequacy
open PA215.Zip
/-- Auxiliary arithmetic tags do not enlarge the physical control set. The
exact 211-control partial table and the dense-stack interpreter have identical
blank-halting behavior; the four unused tags are excluded by the proved invariant. -/
theorem blank_halts_iff :
    PA215.Zip.Halts PA211.UserCandidate.CandidateTable.machine PA213.Startup.blank ↔ NatTape.Halts NatTape.blank := by
  have hl : PaddedBridge.Live PA213.Startup.blank.q :=
    Or.inr PA211.UserCandidate.StateBound.start_working
  have hp := PaddedBridge.halts_iff PA213.Startup.blank hl
  have hn := PaddedNatTape.halts_iff PA213.Startup.blank
  change PA215.Zip.Halts PaddedBridge.machine PA213.Startup.blank ↔ NatTape.Halts NatTape.blank at hn
  exact hp.symm.trans hn
#print axioms blank_halts_iff
end PA211.UserCandidate.PA.PhysicalAdequacy
