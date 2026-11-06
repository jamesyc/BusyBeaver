import PA215PA.Startup.Part2

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace PA215.PA.Startup
open NatTape
theorem chunk024 : NatTape.run 1000 c024 = some c025 := by decide
theorem chunk025 : NatTape.run 1000 c025 = some c026 := by decide
theorem chunk026 : NatTape.run 1000 c026 = some c027 := by decide
theorem chunk027 : NatTape.run 1000 c027 = some c028 := by decide
theorem chunk028 : NatTape.run 1000 c028 = some c029 := by decide
theorem chunk029 : NatTape.run 1000 c029 = some c030 := by decide
theorem chunk030 : NatTape.run 1000 c030 = some c031 := by decide
theorem chunk031 : NatTape.run 1000 c031 = some c032 := by decide

theorem part3 : NatTape.run 8000 c024 = some c032 := by
  exact (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans chunk024 chunk025) chunk026) chunk027) chunk028) chunk029) chunk030) chunk031)
end PA215.PA.Startup
