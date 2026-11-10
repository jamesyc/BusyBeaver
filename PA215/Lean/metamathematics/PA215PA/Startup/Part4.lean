import PA215PA.Startup.Part3

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace PA215.PA.Startup
open NatTape
theorem chunk032 : NatTape.run 1000 c032 = some c033 := by decide
theorem chunk033 : NatTape.run 1000 c033 = some c034 := by decide
theorem chunk034 : NatTape.run 1000 c034 = some c035 := by decide
theorem chunk035 : NatTape.run 1000 c035 = some c036 := by decide
theorem chunk036 : NatTape.run 1000 c036 = some c037 := by decide
theorem chunk037 : NatTape.run 1000 c037 = some c038 := by decide
theorem chunk038 : NatTape.run 1000 c038 = some c039 := by decide
theorem chunk039 : NatTape.run 1000 c039 = some c040 := by decide

theorem part4 : NatTape.run 8000 c032 = some c040 := by
  exact (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans chunk032 chunk033) chunk034) chunk035) chunk036) chunk037) chunk038) chunk039)
end PA215.PA.Startup
