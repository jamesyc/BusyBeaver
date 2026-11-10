import PA215PA.Startup.Data

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace PA215.PA.Startup
open NatTape
theorem chunk000 : NatTape.run 1000 c000 = some c001 := by decide
theorem chunk001 : NatTape.run 1000 c001 = some c002 := by decide
theorem chunk002 : NatTape.run 1000 c002 = some c003 := by decide
theorem chunk003 : NatTape.run 1000 c003 = some c004 := by decide
theorem chunk004 : NatTape.run 1000 c004 = some c005 := by decide
theorem chunk005 : NatTape.run 1000 c005 = some c006 := by decide
theorem chunk006 : NatTape.run 1000 c006 = some c007 := by decide
theorem chunk007 : NatTape.run 1000 c007 = some c008 := by decide

theorem part0 : NatTape.run 8000 c000 = some c008 := by
  exact (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans chunk000 chunk001) chunk002) chunk003) chunk004) chunk005) chunk006) chunk007)
end PA215.PA.Startup
