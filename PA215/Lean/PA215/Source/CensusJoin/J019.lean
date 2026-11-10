import PA215.Source.ContractJoinPilot
import PA215.Census.C019
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PA215.Source.CensusJoin.J019
theorem checked : PA215.Census.C019.records.toList.all recordAgrees = true := by decide
#print axioms checked
end PA215.Source.CensusJoin.J019
