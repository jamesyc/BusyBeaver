module
public import I3_334.Search.SearchCompleteness
public import I3_334.Proof.Calibration
@[expose] public section

namespace PalomarI3334

open PalomarI3380.Logic

theorem exactClaim : ExactClaim :=
  ⟨haltingSentence, haltingSentence_represents,
    fun consistent => ⟨literal_nonhalting_of_consistency consistent, literal_nonhalting_unprovable consistent⟩,
    fun sound => ⟨literal_halting_unprovable sound, literal_nonhalting_unprovable sound.consistent⟩⟩

end PalomarI3334
