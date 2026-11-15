module
public import M209.Startup
public import M209.StartupFrame
@[expose] public section
namespace M209.Startup
open M6.Zip M6.Runtime

theorem blank_to_initial_frame :
    run literal 58154 (zc 0 [] []) = some (mapConf forward (conc 0 initialFile start35)) := by
  rw [← blank_exact, ← clean_exact]
  exact startup_exact
end M209.Startup
