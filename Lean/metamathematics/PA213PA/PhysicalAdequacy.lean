import PA213PA.PaddedNatTape
import PA213.StartupData
namespace PA213.PA.PhysicalAdequacy
open PA215.Zip
/-- Auxiliary arithmetic tags do not enlarge the physical control set. The
exact 213-control partial table and the dense-stack interpreter have identical
blank-halting behavior; the two unused tags are excluded by the proved invariant. -/
theorem blank_halts_iff :
    PA215.Zip.Halts PA213.CandidateTable.machine PA213.Startup.blank ↔ NatTape.Halts NatTape.blank := by
  have hl : PaddedBridge.Live PA213.Startup.blank.q :=
    Or.inr PA213.StateBound.start_working
  have hp := PaddedBridge.halts_iff PA213.Startup.blank hl
  have hn := PaddedNatTape.halts_iff PA213.Startup.blank
  change PA215.Zip.Halts PaddedBridge.machine PA213.Startup.blank ↔ NatTape.Halts NatTape.blank at hn
  exact hp.symm.trans hn
#print axioms blank_halts_iff
end PA213.PA.PhysicalAdequacy
