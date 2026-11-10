import PA215PA.Startup.Part4

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace PA215.PA.Startup
open NatTape
theorem chunk040 : NatTape.run 1000 c040 = some c041 := by decide
theorem chunk041 : NatTape.run 1000 c041 = some c042 := by decide
theorem chunk042 : NatTape.run 1000 c042 = some c043 := by decide
theorem chunk043 : NatTape.run 1000 c043 = some c044 := by decide
theorem chunk044 : NatTape.run 1000 c044 = some c045 := by decide
theorem chunk045 : NatTape.run 1000 c045 = some c046 := by decide
theorem chunk046 : NatTape.run 1000 c046 = some c047 := by decide
theorem chunk047 : NatTape.run 1000 c047 = some c048 := by decide

theorem part5 : NatTape.run 8000 c040 = some c048 := by
  exact (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans chunk040 chunk041) chunk042) chunk043) chunk044) chunk045) chunk046) chunk047)
end PA215.PA.Startup
