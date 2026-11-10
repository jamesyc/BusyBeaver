import PA215.Source.CensusKeys
import PA215.Census.C000
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace PA215.Source.ObligationCensus.K000
def keys : List Nat := [0,1,2,4,5,6,8,10,12,14,15,16,18,19,20,22,23,24,26,27,28,30,32,34,35,36,38,40,41,42,44,46,47,48,49,50,51,52,54,56,57,58,60,62,63,64,66,68,70,71,72,74,75,76,78,80,82,83,84,86,88,89,90,92,94,96,97,98,100,102,103,104,106,108,109,110,112,114,115,116,118,120,122,123,124,126,127,128,130,132,134,135,136,138,140,141,142,144,146,148,149,150,152,154,155,156,158,159,160,162,163,164,166,168,170,171,172,174,176,177,178,180,182,184,185,186,188,189]
theorem checked : PA215.Census.C000.records.toList.map ObligationKeys.rawKey = keys := by rfl
#print axioms checked
end PA215.Source.ObligationCensus.K000
