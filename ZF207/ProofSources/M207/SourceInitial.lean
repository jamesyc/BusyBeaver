module
public import M207.SourceData
public import M207.StartupEndpoint
@[expose] public section
namespace M207.Source
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000

def initialState : State := ⟨25,0,Startup.initialFile⟩

theorem initial_valid : Valid 4341 initialState := by
  constructor <;> decide +kernel

theorem initial_frame : frame paths initialState =
    mapConf forward (M6.Runtime.conc 0 Startup.initialFile start35) := by decide +kernel

theorem blank_to_cfg : Reach literal (zc 0 [] []) (frame paths initialState) := by
  refine ⟨58616,?_⟩
  rw [initial_frame]
  exact Startup.blank_to_initial_frame
end M207.Source
