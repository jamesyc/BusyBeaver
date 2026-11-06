import PA215PA.Startup.Part1

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace PA215.PA.Startup
open NatTape
theorem chunk016 : NatTape.run 1000 c016 = some c017 := by decide
theorem chunk017 : NatTape.run 1000 c017 = some c018 := by decide
theorem chunk018 : NatTape.run 1000 c018 = some c019 := by decide
theorem chunk019 : NatTape.run 1000 c019 = some c020 := by decide
theorem chunk020 : NatTape.run 1000 c020 = some c021 := by decide
theorem chunk021 : NatTape.run 1000 c021 = some c022 := by decide
theorem chunk022 : NatTape.run 1000 c022 = some c023 := by decide
theorem chunk023 : NatTape.run 1000 c023 = some c024 := by decide

theorem part2 : NatTape.run 8000 c016 = some c024 := by
  exact (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans (NatTape.run_trans chunk016 chunk017) chunk018) chunk019) chunk020) chunk021) chunk022) chunk023)
end PA215.PA.Startup
