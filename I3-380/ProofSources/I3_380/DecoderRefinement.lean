module
public import I3_380.DecoderComparison
public import I3_380.Startup
public import I3_380.DecoderData
@[expose] public section

namespace PalomarI3380

def referenceMachine : Machine := ⟨394, DecoderData.referenceRows⟩

def decoderComparison : DecoderComparison :=
  ⟨referenceMachine, machine, DecoderData.stateMap, DecoderData.entryMasks⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem decoder_comparison_checked : decoderComparison.check = true := by
  decide +kernel

/-- All finite and infinite blank-tape runs have the same termination
behavior before and after the decoder-state merger. -/
theorem literal_halts_iff_reference :
    HaltsFrom machine blank ↔ HaltsFrom referenceMachine blank := by
  have h : decoderComparison.Related blank (decoderComparison.translate blank) := by
    unfold DecoderComparison.Related
    decide +kernel
  have hStart : decoderComparison.translate blank = blank := by decide +kernel
  have result := decoderComparison.halts_iff decoder_comparison_checked blank h
  rw [hStart] at result
  exact result

private theorem reference_loader_rows : ∀ (q : Fin 7) (b : Fin 2),
    referenceMachine.row q.val b.val = bootMachine.row q.val b.val := by
  decide +kernel

theorem reference_startup : run referenceMachine 39753 blank = some loaderExit :=
  run_extend (small := bootMachine) (large := referenceMachine) (n := 39753) (c := blank)
    (d := loaderExit) (by decide) (fun q hq b hb => reference_loader_rows ⟨q, hq⟩ ⟨b, hb⟩) boot_startup

end PalomarI3380
