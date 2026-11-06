import PA215PA.Startup.Part5

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace PA215.PA.Startup
open NatTape
theorem chunk048 : NatTape.run 1000 c048 = some c049 := by decide
theorem chunk049 : NatTape.run 1000 c049 = some c050 := by decide
theorem chunk050 : NatTape.run 1000 c050 = some c051 := by decide
theorem chunk051 : NatTape.run 1000 c051 = some c052 := by decide
theorem chunk052 : NatTape.run 1000 c052 = some c053 := by decide
theorem chunk053 : NatTape.run 1000 c053 = some c054 := by decide
theorem chunk054 : NatTape.run 1000 c054 = some c055 := by decide
theorem chunk055 : NatTape.run 1000 c055 = some c056 := by decide

theorem part6 : NatTape.run 8000 c048 = some c056 := by
  exact (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans chunk048 chunk049) chunk050) chunk051) chunk052) chunk053) chunk054) chunk055)
end PA215.PA.Startup
