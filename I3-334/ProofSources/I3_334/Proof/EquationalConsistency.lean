module
public import I3_334.Proof.ForwardModel
public import I3_334.Proof.Recovery
@[expose] public section

namespace PalomarI3334

/-- The ten guarded equations have exactly the consistency strength of
ZFC + I3 for their distinguished ground equation. -/
theorem guarded_underivability_iff_consistency :
    (¬ Derives (.app 1 []) (.app 0 [])) ↔ PalomarI3380.Logic.ZFCI3Consistent :=
  ⟨consistency_of_guarded_underivability, guarded_underivability_of_consistency⟩

end PalomarI3334
