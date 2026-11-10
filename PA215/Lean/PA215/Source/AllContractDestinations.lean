import PA215.OriginalCensus
import PA215.Source.DestinationJoin.D001
import PA215.Source.DestinationJoin.D002
import PA215.Source.DestinationJoin.D003
import PA215.Source.DestinationJoin.D004
import PA215.Source.DestinationJoin.D005
import PA215.Source.DestinationJoin.D006
import PA215.Source.DestinationJoin.D007
import PA215.Source.DestinationJoin.D008
import PA215.Source.DestinationJoin.D009
import PA215.Source.DestinationJoin.D010
import PA215.Source.DestinationJoin.D011
import PA215.Source.DestinationJoin.D012
import PA215.Source.DestinationJoin.D013
import PA215.Source.DestinationJoin.D014
import PA215.Source.DestinationJoin.D015
import PA215.Source.DestinationJoin.D016
import PA215.Source.DestinationJoin.D017
import PA215.Source.DestinationJoin.D018
import PA215.Source.DestinationJoin.D019
import PA215.Source.DestinationJoin.D020
import PA215.Source.DestinationJoin.D021
import PA215.Source.DestinationJoin.D022
import PA215.Source.DestinationJoin.D023
import PA215.Source.DestinationJoin.D024
import PA215.Source.DestinationJoin.D025
import PA215.Source.DestinationJoin.D026
import PA215.Source.DestinationJoin.D027
import PA215.Source.DestinationJoin.D028
import PA215.Source.DestinationJoin.D029
import PA215.Source.DestinationJoin.D030
import PA215.Source.DestinationJoin.D031
import PA215.Source.DestinationJoin.D032
import PA215.Source.DestinationJoin.D033
import PA215.Source.DestinationJoin.D034
import PA215.Source.DestinationJoin.D035
import PA215.Source.DestinationJoin.D036
import PA215.Source.DestinationJoin.D037
import PA215.Source.DestinationJoin.D038
import PA215.Source.DestinationJoin.D039
import PA215.Source.DestinationJoin.D040

namespace PA215.Source

/-- All 5134 original obligations have the exact source control destination,
including zero-extension, branches, cyclic root return, and terminal halt.
This finite comparison is not runtime coverage. -/
theorem original_all_destinations_agree :
    PA215.Census.all.toList.all destinationAgrees = true := by
  simp only [PA215.Census.all, Array.toList_append, List.all_append,
    original_first128_destinations,
    DestinationJoin.D001.checked,
    DestinationJoin.D002.checked,
    DestinationJoin.D003.checked,
    DestinationJoin.D004.checked,
    DestinationJoin.D005.checked,
    DestinationJoin.D006.checked,
    DestinationJoin.D007.checked,
    DestinationJoin.D008.checked,
    DestinationJoin.D009.checked,
    DestinationJoin.D010.checked,
    DestinationJoin.D011.checked,
    DestinationJoin.D012.checked,
    DestinationJoin.D013.checked,
    DestinationJoin.D014.checked,
    DestinationJoin.D015.checked,
    DestinationJoin.D016.checked,
    DestinationJoin.D017.checked,
    DestinationJoin.D018.checked,
    DestinationJoin.D019.checked,
    DestinationJoin.D020.checked,
    DestinationJoin.D021.checked,
    DestinationJoin.D022.checked,
    DestinationJoin.D023.checked,
    DestinationJoin.D024.checked,
    DestinationJoin.D025.checked,
    DestinationJoin.D026.checked,
    DestinationJoin.D027.checked,
    DestinationJoin.D028.checked,
    DestinationJoin.D029.checked,
    DestinationJoin.D030.checked,
    DestinationJoin.D031.checked,
    DestinationJoin.D032.checked,
    DestinationJoin.D033.checked,
    DestinationJoin.D034.checked,
    DestinationJoin.D035.checked,
    DestinationJoin.D036.checked,
    DestinationJoin.D037.checked,
    DestinationJoin.D038.checked,
    DestinationJoin.D039.checked,
    DestinationJoin.D040.checked,
    Bool.and_self]

#print axioms original_all_destinations_agree
end PA215.Source
