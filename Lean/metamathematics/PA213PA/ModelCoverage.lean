import PA213.ListBlocks
import PA213PA.ModelCoverageShards.S000
import PA213PA.ModelCoverageShards.S001
import PA213PA.ModelCoverageShards.S002
import PA213PA.ModelCoverageShards.S003
import PA213PA.ModelCoverageShards.S004
import PA213PA.ModelCoverageShards.S005
import PA213PA.ModelCoverageShards.S006
import PA213PA.ModelCoverageShards.S007
import PA213PA.ModelCoverageShards.S008
import PA213PA.ModelCoverageShards.S009
import PA213PA.ModelCoverageShards.S010
import PA213PA.ModelCoverageShards.S011
import PA213PA.ModelCoverageShards.S012
import PA213PA.ModelCoverageShards.S013
import PA213PA.ModelCoverageShards.S014
import PA213PA.ModelCoverageShards.S015
import PA213PA.ModelCoverageShards.S016
import PA213PA.ModelCoverageShards.S017
import PA213PA.ModelCoverageShards.S018
import PA213PA.ModelCoverageShards.S019
import PA213PA.ModelCoverageShards.S020
import PA213PA.ModelCoverageShards.S021
import PA213PA.ModelCoverageShards.S022
import PA213PA.ModelCoverageShards.S023
import PA213PA.ModelCoverageShards.S024
import PA213PA.ModelCoverageShards.S025
import PA213PA.ModelCoverageShards.S026
import PA213PA.ModelCoverageShards.S027
import PA213PA.ModelCoverageShards.S028
import PA213PA.ModelCoverageShards.S029
import PA213PA.ModelCoverageShards.S030
import PA213PA.ModelCoverageShards.S031
import PA213PA.ModelCoverageShards.S032
import PA213PA.ModelCoverageShards.S033
import PA213PA.ModelCoverageShards.S034
import PA213PA.ModelCoverageShards.S035
import PA213PA.ModelCoverageShards.S036
import PA213PA.ModelCoverageShards.S037
import PA213PA.ModelCoverageShards.S038
import PA213PA.ModelCoverageShards.S039
import PA213PA.ModelCoverageShards.S040
import PA213PA.ModelCoverageShards.S041
import PA213PA.ModelCoverageShards.S042
import PA213PA.ModelCoverageShards.S043
import PA213PA.ModelCoverageShards.S044
import PA213PA.ModelCoverageShards.S045
import PA213PA.ModelCoverageShards.S046
import PA213PA.ModelCoverageShards.S047
import PA213PA.ModelCoverageShards.S048
import PA213PA.ModelCoverageShards.S049
import PA213PA.ModelCoverageShards.S050
import PA213PA.ModelCoverageShards.S051
import PA213PA.ModelCoverageShards.S052
import PA213PA.ModelCoverageShards.S053
import PA213PA.ModelCoverageShards.S054
import PA213PA.ModelCoverageShards.S055
import PA213PA.ModelCoverageShards.S056
import PA213PA.ModelCoverageShards.S057
import PA213PA.ModelCoverageShards.S058
import PA213PA.ModelCoverageShards.S059
import PA213PA.ModelCoverageShards.S060
import PA213PA.ModelCoverageShards.S061
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000
namespace PA213.PA.ModelCoverage
open PA215.Source PA213.SourceProgram PA213.PA.ModelPrimitive
def entries : Array (Entry PA213.FastPaths.path 3947) :=
  PA213.PA.ModelCoverageShards.S000.entries ++
  PA213.PA.ModelCoverageShards.S001.entries ++
  PA213.PA.ModelCoverageShards.S002.entries ++
  PA213.PA.ModelCoverageShards.S003.entries ++
  PA213.PA.ModelCoverageShards.S004.entries ++
  PA213.PA.ModelCoverageShards.S005.entries ++
  PA213.PA.ModelCoverageShards.S006.entries ++
  PA213.PA.ModelCoverageShards.S007.entries ++
  PA213.PA.ModelCoverageShards.S008.entries ++
  PA213.PA.ModelCoverageShards.S009.entries ++
  PA213.PA.ModelCoverageShards.S010.entries ++
  PA213.PA.ModelCoverageShards.S011.entries ++
  PA213.PA.ModelCoverageShards.S012.entries ++
  PA213.PA.ModelCoverageShards.S013.entries ++
  PA213.PA.ModelCoverageShards.S014.entries ++
  PA213.PA.ModelCoverageShards.S015.entries ++
  PA213.PA.ModelCoverageShards.S016.entries ++
  PA213.PA.ModelCoverageShards.S017.entries ++
  PA213.PA.ModelCoverageShards.S018.entries ++
  PA213.PA.ModelCoverageShards.S019.entries ++
  PA213.PA.ModelCoverageShards.S020.entries ++
  PA213.PA.ModelCoverageShards.S021.entries ++
  PA213.PA.ModelCoverageShards.S022.entries ++
  PA213.PA.ModelCoverageShards.S023.entries ++
  PA213.PA.ModelCoverageShards.S024.entries ++
  PA213.PA.ModelCoverageShards.S025.entries ++
  PA213.PA.ModelCoverageShards.S026.entries ++
  PA213.PA.ModelCoverageShards.S027.entries ++
  PA213.PA.ModelCoverageShards.S028.entries ++
  PA213.PA.ModelCoverageShards.S029.entries ++
  PA213.PA.ModelCoverageShards.S030.entries ++
  PA213.PA.ModelCoverageShards.S031.entries ++
  PA213.PA.ModelCoverageShards.S032.entries ++
  PA213.PA.ModelCoverageShards.S033.entries ++
  PA213.PA.ModelCoverageShards.S034.entries ++
  PA213.PA.ModelCoverageShards.S035.entries ++
  PA213.PA.ModelCoverageShards.S036.entries ++
  PA213.PA.ModelCoverageShards.S037.entries ++
  PA213.PA.ModelCoverageShards.S038.entries ++
  PA213.PA.ModelCoverageShards.S039.entries ++
  PA213.PA.ModelCoverageShards.S040.entries ++
  PA213.PA.ModelCoverageShards.S041.entries ++
  PA213.PA.ModelCoverageShards.S042.entries ++
  PA213.PA.ModelCoverageShards.S043.entries ++
  PA213.PA.ModelCoverageShards.S044.entries ++
  PA213.PA.ModelCoverageShards.S045.entries ++
  PA213.PA.ModelCoverageShards.S046.entries ++
  PA213.PA.ModelCoverageShards.S047.entries ++
  PA213.PA.ModelCoverageShards.S048.entries ++
  PA213.PA.ModelCoverageShards.S049.entries ++
  PA213.PA.ModelCoverageShards.S050.entries ++
  PA213.PA.ModelCoverageShards.S051.entries ++
  PA213.PA.ModelCoverageShards.S052.entries ++
  PA213.PA.ModelCoverageShards.S053.entries ++
  PA213.PA.ModelCoverageShards.S054.entries ++
  PA213.PA.ModelCoverageShards.S055.entries ++
  PA213.PA.ModelCoverageShards.S056.entries ++
  PA213.PA.ModelCoverageShards.S057.entries ++
  PA213.PA.ModelCoverageShards.S058.entries ++
  PA213.PA.ModelCoverageShards.S059.entries ++
  PA213.PA.ModelCoverageShards.S060.entries ++
  PA213.PA.ModelCoverageShards.S061.entries
private theorem sites_blocks : entries.toList.map (·.site) =
    PA213.ListBlocks.blocks sites.toList 62 := by
  simp only [entries, Array.toList_append, List.map_append,
    PA213.PA.ModelCoverageShards.S000.sites_block,
    PA213.PA.ModelCoverageShards.S001.sites_block,
    PA213.PA.ModelCoverageShards.S002.sites_block,
    PA213.PA.ModelCoverageShards.S003.sites_block,
    PA213.PA.ModelCoverageShards.S004.sites_block,
    PA213.PA.ModelCoverageShards.S005.sites_block,
    PA213.PA.ModelCoverageShards.S006.sites_block,
    PA213.PA.ModelCoverageShards.S007.sites_block,
    PA213.PA.ModelCoverageShards.S008.sites_block,
    PA213.PA.ModelCoverageShards.S009.sites_block,
    PA213.PA.ModelCoverageShards.S010.sites_block,
    PA213.PA.ModelCoverageShards.S011.sites_block,
    PA213.PA.ModelCoverageShards.S012.sites_block,
    PA213.PA.ModelCoverageShards.S013.sites_block,
    PA213.PA.ModelCoverageShards.S014.sites_block,
    PA213.PA.ModelCoverageShards.S015.sites_block,
    PA213.PA.ModelCoverageShards.S016.sites_block,
    PA213.PA.ModelCoverageShards.S017.sites_block,
    PA213.PA.ModelCoverageShards.S018.sites_block,
    PA213.PA.ModelCoverageShards.S019.sites_block,
    PA213.PA.ModelCoverageShards.S020.sites_block,
    PA213.PA.ModelCoverageShards.S021.sites_block,
    PA213.PA.ModelCoverageShards.S022.sites_block,
    PA213.PA.ModelCoverageShards.S023.sites_block,
    PA213.PA.ModelCoverageShards.S024.sites_block,
    PA213.PA.ModelCoverageShards.S025.sites_block,
    PA213.PA.ModelCoverageShards.S026.sites_block,
    PA213.PA.ModelCoverageShards.S027.sites_block,
    PA213.PA.ModelCoverageShards.S028.sites_block,
    PA213.PA.ModelCoverageShards.S029.sites_block,
    PA213.PA.ModelCoverageShards.S030.sites_block,
    PA213.PA.ModelCoverageShards.S031.sites_block,
    PA213.PA.ModelCoverageShards.S032.sites_block,
    PA213.PA.ModelCoverageShards.S033.sites_block,
    PA213.PA.ModelCoverageShards.S034.sites_block,
    PA213.PA.ModelCoverageShards.S035.sites_block,
    PA213.PA.ModelCoverageShards.S036.sites_block,
    PA213.PA.ModelCoverageShards.S037.sites_block,
    PA213.PA.ModelCoverageShards.S038.sites_block,
    PA213.PA.ModelCoverageShards.S039.sites_block,
    PA213.PA.ModelCoverageShards.S040.sites_block,
    PA213.PA.ModelCoverageShards.S041.sites_block,
    PA213.PA.ModelCoverageShards.S042.sites_block,
    PA213.PA.ModelCoverageShards.S043.sites_block,
    PA213.PA.ModelCoverageShards.S044.sites_block,
    PA213.PA.ModelCoverageShards.S045.sites_block,
    PA213.PA.ModelCoverageShards.S046.sites_block,
    PA213.PA.ModelCoverageShards.S047.sites_block,
    PA213.PA.ModelCoverageShards.S048.sites_block,
    PA213.PA.ModelCoverageShards.S049.sites_block,
    PA213.PA.ModelCoverageShards.S050.sites_block,
    PA213.PA.ModelCoverageShards.S051.sites_block,
    PA213.PA.ModelCoverageShards.S052.sites_block,
    PA213.PA.ModelCoverageShards.S053.sites_block,
    PA213.PA.ModelCoverageShards.S054.sites_block,
    PA213.PA.ModelCoverageShards.S055.sites_block,
    PA213.PA.ModelCoverageShards.S056.sites_block,
    PA213.PA.ModelCoverageShards.S057.sites_block,
    PA213.PA.ModelCoverageShards.S058.sites_block,
    PA213.PA.ModelCoverageShards.S059.sites_block,
    PA213.PA.ModelCoverageShards.S060.sites_block,
    PA213.PA.ModelCoverageShards.S061.sites_block]
  rfl
private theorem codes_blocks : entries.toList.map (·.code) =
    PA213.ListBlocks.blocks codes.toList 62 := by
  simp only [entries, Array.toList_append, List.map_append,
    PA213.PA.ModelCoverageShards.S000.codes_block,
    PA213.PA.ModelCoverageShards.S001.codes_block,
    PA213.PA.ModelCoverageShards.S002.codes_block,
    PA213.PA.ModelCoverageShards.S003.codes_block,
    PA213.PA.ModelCoverageShards.S004.codes_block,
    PA213.PA.ModelCoverageShards.S005.codes_block,
    PA213.PA.ModelCoverageShards.S006.codes_block,
    PA213.PA.ModelCoverageShards.S007.codes_block,
    PA213.PA.ModelCoverageShards.S008.codes_block,
    PA213.PA.ModelCoverageShards.S009.codes_block,
    PA213.PA.ModelCoverageShards.S010.codes_block,
    PA213.PA.ModelCoverageShards.S011.codes_block,
    PA213.PA.ModelCoverageShards.S012.codes_block,
    PA213.PA.ModelCoverageShards.S013.codes_block,
    PA213.PA.ModelCoverageShards.S014.codes_block,
    PA213.PA.ModelCoverageShards.S015.codes_block,
    PA213.PA.ModelCoverageShards.S016.codes_block,
    PA213.PA.ModelCoverageShards.S017.codes_block,
    PA213.PA.ModelCoverageShards.S018.codes_block,
    PA213.PA.ModelCoverageShards.S019.codes_block,
    PA213.PA.ModelCoverageShards.S020.codes_block,
    PA213.PA.ModelCoverageShards.S021.codes_block,
    PA213.PA.ModelCoverageShards.S022.codes_block,
    PA213.PA.ModelCoverageShards.S023.codes_block,
    PA213.PA.ModelCoverageShards.S024.codes_block,
    PA213.PA.ModelCoverageShards.S025.codes_block,
    PA213.PA.ModelCoverageShards.S026.codes_block,
    PA213.PA.ModelCoverageShards.S027.codes_block,
    PA213.PA.ModelCoverageShards.S028.codes_block,
    PA213.PA.ModelCoverageShards.S029.codes_block,
    PA213.PA.ModelCoverageShards.S030.codes_block,
    PA213.PA.ModelCoverageShards.S031.codes_block,
    PA213.PA.ModelCoverageShards.S032.codes_block,
    PA213.PA.ModelCoverageShards.S033.codes_block,
    PA213.PA.ModelCoverageShards.S034.codes_block,
    PA213.PA.ModelCoverageShards.S035.codes_block,
    PA213.PA.ModelCoverageShards.S036.codes_block,
    PA213.PA.ModelCoverageShards.S037.codes_block,
    PA213.PA.ModelCoverageShards.S038.codes_block,
    PA213.PA.ModelCoverageShards.S039.codes_block,
    PA213.PA.ModelCoverageShards.S040.codes_block,
    PA213.PA.ModelCoverageShards.S041.codes_block,
    PA213.PA.ModelCoverageShards.S042.codes_block,
    PA213.PA.ModelCoverageShards.S043.codes_block,
    PA213.PA.ModelCoverageShards.S044.codes_block,
    PA213.PA.ModelCoverageShards.S045.codes_block,
    PA213.PA.ModelCoverageShards.S046.codes_block,
    PA213.PA.ModelCoverageShards.S047.codes_block,
    PA213.PA.ModelCoverageShards.S048.codes_block,
    PA213.PA.ModelCoverageShards.S049.codes_block,
    PA213.PA.ModelCoverageShards.S050.codes_block,
    PA213.PA.ModelCoverageShards.S051.codes_block,
    PA213.PA.ModelCoverageShards.S052.codes_block,
    PA213.PA.ModelCoverageShards.S053.codes_block,
    PA213.PA.ModelCoverageShards.S054.codes_block,
    PA213.PA.ModelCoverageShards.S055.codes_block,
    PA213.PA.ModelCoverageShards.S056.codes_block,
    PA213.PA.ModelCoverageShards.S057.codes_block,
    PA213.PA.ModelCoverageShards.S058.codes_block,
    PA213.PA.ModelCoverageShards.S059.codes_block,
    PA213.PA.ModelCoverageShards.S060.codes_block,
    PA213.PA.ModelCoverageShards.S061.codes_block]
  rfl
theorem sites_list_eq : entries.toList.map (·.site) = sites.toList := by
  rw [sites_blocks, PA213.ListBlocks.blocks_eq_take, List.take_of_length_le]
  decide
theorem sites_eq : entries.map (·.site) = sites := by
  apply Array.toList_inj.mp
  simpa using sites_list_eq
theorem codes_list_eq : entries.toList.map (·.code) = codes.toList := by
  rw [codes_blocks, PA213.ListBlocks.blocks_eq_take, List.take_of_length_le]
  decide
theorem codes_eq : entries.map (·.code) = codes := by
  apply Array.toList_inj.mp
  simpa using codes_list_eq
theorem count_eq : entries.size = 3947 := by
  have h := congrArg Array.size sites_eq
  simpa only [Array.size_map, sites_count] using h
end PA213.PA.ModelCoverage
