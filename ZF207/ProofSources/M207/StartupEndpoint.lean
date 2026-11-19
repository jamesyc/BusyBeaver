module
public import M207.Startup
public import M207.StartupFrame
@[expose] public section
namespace M207.Startup
open M6.Zip M6.Runtime

theorem blank_to_initial_frame :
    run literal 58616 (zc 0 [] []) = some (mapConf forward (conc 0 initialFile start35)) := by
  rw [← blank_exact, ← clean_exact]
  exact startup_exact
end M207.Startup
