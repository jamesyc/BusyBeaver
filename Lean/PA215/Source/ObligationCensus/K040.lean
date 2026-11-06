import PA215.Source.CensusKeys
import PA215.Census.C040
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace PA215.Source.ObligationCensus.K040
def keys : List Nat := [7872,7874,7875,7876,7878,7880,7882,7883,7884,7886,7888,7889,7890,7892]
theorem checked : PA215.Census.C040.records.toList.map ObligationKeys.rawKey = keys := by rfl
#print axioms checked
end PA215.Source.ObligationCensus.K040
