import PA215PA.Startup.Part0

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace PA215.PA.Startup
open NatTape
theorem chunk008 : NatTape.run 1000 c008 = some c009 := by decide
theorem chunk009 : NatTape.run 1000 c009 = some c010 := by decide
theorem chunk010 : NatTape.run 1000 c010 = some c011 := by decide
theorem chunk011 : NatTape.run 1000 c011 = some c012 := by decide
theorem chunk012 : NatTape.run 1000 c012 = some c013 := by decide
theorem chunk013 : NatTape.run 1000 c013 = some c014 := by decide
theorem chunk014 : NatTape.run 1000 c014 = some c015 := by decide
theorem chunk015 : NatTape.run 1000 c015 = some c016 := by decide

theorem part1 : NatTape.run 8000 c008 = some c016 := by
  exact (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans chunk008 chunk009) chunk010) chunk011) chunk012) chunk013) chunk014) chunk015)
end PA215.PA.Startup
