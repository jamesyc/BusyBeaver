import PA215.OriginalCensus
import PA215.Source.CensusJoin.J001
import PA215.Source.CensusJoin.J002
import PA215.Source.CensusJoin.J003
import PA215.Source.CensusJoin.J004
import PA215.Source.CensusJoin.J005
import PA215.Source.CensusJoin.J006
import PA215.Source.CensusJoin.J007
import PA215.Source.CensusJoin.J008
import PA215.Source.CensusJoin.J009
import PA215.Source.CensusJoin.J010
import PA215.Source.CensusJoin.J011
import PA215.Source.CensusJoin.J012
import PA215.Source.CensusJoin.J013
import PA215.Source.CensusJoin.J014
import PA215.Source.CensusJoin.J015
import PA215.Source.CensusJoin.J016
import PA215.Source.CensusJoin.J017
import PA215.Source.CensusJoin.J018
import PA215.Source.CensusJoin.J019
import PA215.Source.CensusJoin.J020
import PA215.Source.CensusJoin.J021
import PA215.Source.CensusJoin.J022
import PA215.Source.CensusJoin.J023
import PA215.Source.CensusJoin.J024
import PA215.Source.CensusJoin.J025
import PA215.Source.CensusJoinCachedV2.J026
import PA215.Source.CensusJoinCachedV2.J027
import PA215.Source.CensusJoinCachedV2.J028
import PA215.Source.CensusJoinCachedV2.J029
import PA215.Source.CensusJoinCachedV2.J030
import PA215.Source.CensusJoinCachedV2.J031
import PA215.Source.CensusJoin.J032
import PA215.Source.CensusJoin.J033
import PA215.Source.CensusJoin.J034
import PA215.Source.CensusJoin.J035
import PA215.Source.CensusJoin.J036
import PA215.Source.CensusJoin.J037
import PA215.Source.CensusJoin.J038
import PA215.Source.CensusJoin.J039
import PA215.Source.CensusJoin.J040

namespace PA215.Source.CachedV2

/-- All 5134 original obligations match the exact source-generated operation,
branch and complete frames. This is not a theorem that all machine checks pass. -/
theorem original_all_frames_agree :
    PA215.Census.all.toList.all recordAgrees = true := by
  simp only [PA215.Census.all, Array.toList_append, List.all_append,
    original_first128_agree,
    CensusJoin.J001.checked,
    CensusJoin.J002.checked,
    CensusJoin.J003.checked,
    CensusJoin.J004.checked,
    CensusJoin.J005.checked,
    CensusJoin.J006.checked,
    CensusJoin.J007.checked,
    CensusJoin.J008.checked,
    CensusJoin.J009.checked,
    CensusJoin.J010.checked,
    CensusJoin.J011.checked,
    CensusJoin.J012.checked,
    CensusJoin.J013.checked,
    CensusJoin.J014.checked,
    CensusJoin.J015.checked,
    CensusJoin.J016.checked,
    CensusJoin.J017.checked,
    CensusJoin.J018.checked,
    CensusJoin.J019.checked,
    CensusJoin.J020.checked,
    CensusJoin.J021.checked,
    CensusJoin.J022.checked,
    CensusJoin.J023.checked,
    CensusJoin.J024.checked,
    CensusJoin.J025.checked,
    CensusJoinCachedV2.J026.checked,
    CensusJoinCachedV2.J027.checked,
    CensusJoinCachedV2.J028.checked,
    CensusJoinCachedV2.J029.checked,
    CensusJoinCachedV2.J030.checked,
    CensusJoinCachedV2.J031.checked,
    CensusJoin.J032.checked,
    CensusJoin.J033.checked,
    CensusJoin.J034.checked,
    CensusJoin.J035.checked,
    CensusJoin.J036.checked,
    CensusJoin.J037.checked,
    CensusJoin.J038.checked,
    CensusJoin.J039.checked,
    CensusJoin.J040.checked,
    Bool.and_self]

#print axioms original_all_frames_agree
end PA215.Source.CachedV2
