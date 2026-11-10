import PA215PA.Startup.Part6

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace PA215.PA.Startup
open NatTape
theorem chunk056 : NatTape.run 1000 c056 = some c057 := by decide
theorem chunk057 : NatTape.run 1000 c057 = some c058 := by decide
theorem chunk058 : NatTape.run 1000 c058 = some c059 := by decide
theorem chunk059 : NatTape.run 1000 c059 = some c060 := by decide
theorem chunk060 : NatTape.run 1000 c060 = some c061 := by decide
theorem chunk061 : NatTape.run 1000 c061 = some c062 := by decide
theorem chunk062 : NatTape.run 1000 c062 = some c063 := by decide
theorem chunk063 : NatTape.run 228 c063 = some c064 := by decide

theorem part7 : NatTape.run 7228 c056 = some c064 := by
  exact (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans chunk056 chunk057) chunk058) chunk059) chunk060) chunk061) chunk062) chunk063)
end PA215.PA.Startup
