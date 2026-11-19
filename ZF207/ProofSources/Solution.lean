module
public import Halting.Final
@[expose] public section
/- The compared theorem, from the calibrated arithmetic theory of `Halting.Final`.
This module intentionally does not import Challenge. -/
namespace PalomarZF207

theorem exact207Claim : Exact207Claim := ZF207.Halting.exact207Claim

end PalomarZF207
