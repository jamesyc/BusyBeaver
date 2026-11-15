module
public import Halting.Final
@[expose] public section
/- The compared theorem, from the calibrated arithmetic theory of `Halting.Final`.
This module intentionally does not import Challenge. -/
namespace PalomarZF209

theorem exact209Claim : Exact209Claim := ZF209.Halting.exact209Claim

end PalomarZF209
