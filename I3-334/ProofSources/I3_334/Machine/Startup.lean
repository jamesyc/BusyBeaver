module
public import I3_334.Machine.Bindings
public import I3_334.Machine.ReferenceData
public import I3_334Support.Machine.Loader
@[expose] public section

namespace PalomarI3334

open PalomarI3380

/-- The five shared growth controls, ending as soon as state 5 is reached. -/
def growthMachine : Machine := ⟨5, 0x20020280400880e00a02404007⟩

private theorem growth_rows : ∀ (q : Fin 5) (b : Fin 2),
    growthMachine.row q.val b.val = machine.row q.val b.val := by decide +kernel

private def after10000 : Configuration :=
  ⟨4, 0x24444464444445222222222222291111111111, 0x5555555555555555554⟩

private def after20000 : Configuration :=
  ⟨1, 0x91111191111c8889911111111111111111111111111111111111, 0xaaaaaaaaaaaaaaaaaaab⟩

private def after30000 : Configuration :=
  ⟨1, 0x91111323222222222222222222222222, 0x1555555555555555555555555555555555555555555555555555⟩

private def afterGrowth : Configuration :=
  ⟨5, 0x24444, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaad555555555555555555555555555555555555555555555555555555555555555554⟩

section GrowthReplay

set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

private theorem growth_first : run growthMachine 10000 blank = some after10000 := by decide +kernel
private theorem growth_second : run growthMachine 10000 after10000 = some after20000 := by decide +kernel
private theorem growth_third : run growthMachine 10000 after20000 = some after30000 := by decide +kernel
private theorem growth_last : run growthMachine 9734 after30000 = some afterGrowth := by decide +kernel

private theorem growth_replay : run growthMachine 39734 blank = some afterGrowth := by
  have replay := join_run (join_run (join_run growth_first growth_second) growth_third) growth_last
  rw [show 10000 + 10000 + 10000 + 9734 = 39734 by decide] at replay
  exact replay

/-- The first decoder input. Its tape is the same initialized tape as in
I3-380; the literal decoder entry has a different label. -/
def decoderEntry : Configuration := { PalomarI3380.loaderExit with state := 16 }

private theorem finish_startup : run machine 31 afterGrowth = some decoderEntry := by decide +kernel

theorem literal_startup : run machine 39765 blank = some decoderEntry := by
  have growth := run_extend (small := growthMachine) (large := machine) (by decide)
    (fun q hq b hb => (growth_rows ⟨q, hq⟩ ⟨b, hb⟩).symm) growth_replay
  have replay := join_run growth finish_startup
  rw [show 39734 + 31 = 39765 by decide] at replay
  exact replay

end GrowthReplay

end PalomarI3334
