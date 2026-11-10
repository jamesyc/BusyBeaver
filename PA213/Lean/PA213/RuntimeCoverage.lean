import PA213.ListBlocks
import PA213.CoverageShards.S000
import PA213.CoverageShards.S001
import PA213.CoverageShards.S002
import PA213.CoverageShards.S003
import PA213.CoverageShards.S004
import PA213.CoverageShards.S005
import PA213.CoverageShards.S006
import PA213.CoverageShards.S007
import PA213.CoverageShards.S008
import PA213.CoverageShards.S009
import PA213.CoverageShards.S010
import PA213.CoverageShards.S011
import PA213.CoverageShards.S012
import PA213.CoverageShards.S013
import PA213.CoverageShards.S014
import PA213.CoverageShards.S015
import PA213.CoverageShards.S016
import PA213.CoverageShards.S017
import PA213.CoverageShards.S018
import PA213.CoverageShards.S019
import PA213.CoverageShards.S020
import PA213.CoverageShards.S021
import PA213.CoverageShards.S022
import PA213.CoverageShards.S023
import PA213.CoverageShards.S024
import PA213.CoverageShards.S025
import PA213.CoverageShards.S026
import PA213.CoverageShards.S027
import PA213.CoverageShards.S028
import PA213.CoverageShards.S029
import PA213.CoverageShards.S030
import PA213.CoverageShards.S031
import PA213.CoverageShards.S032
import PA213.CoverageShards.S033
import PA213.CoverageShards.S034
import PA213.CoverageShards.S035
import PA213.CoverageShards.S036
import PA213.CoverageShards.S037
import PA213.CoverageShards.S038
import PA213.CoverageShards.S039
import PA213.CoverageShards.S040
import PA213.CoverageShards.S041
import PA213.CoverageShards.S042
import PA213.CoverageShards.S043
import PA213.CoverageShards.S044
import PA213.CoverageShards.S045
import PA213.CoverageShards.S046
import PA213.CoverageShards.S047
import PA213.CoverageShards.S048
import PA213.CoverageShards.S049
import PA213.CoverageShards.S050
import PA213.CoverageShards.S051
import PA213.CoverageShards.S052
import PA213.CoverageShards.S053
import PA213.CoverageShards.S054
import PA213.CoverageShards.S055
import PA213.CoverageShards.S056
import PA213.CoverageShards.S057
import PA213.CoverageShards.S058
import PA213.CoverageShards.S059
import PA213.CoverageShards.S060
import PA213.CoverageShards.S061
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000
namespace PA213.RuntimeCoverage
open PA215.Source PA213.SourceProgram PA213.PrimitiveSimulation
def entries : Array (Entry PA213.FastPaths.path 3947) :=
  PA213.CoverageShards.S000.entries ++
  PA213.CoverageShards.S001.entries ++
  PA213.CoverageShards.S002.entries ++
  PA213.CoverageShards.S003.entries ++
  PA213.CoverageShards.S004.entries ++
  PA213.CoverageShards.S005.entries ++
  PA213.CoverageShards.S006.entries ++
  PA213.CoverageShards.S007.entries ++
  PA213.CoverageShards.S008.entries ++
  PA213.CoverageShards.S009.entries ++
  PA213.CoverageShards.S010.entries ++
  PA213.CoverageShards.S011.entries ++
  PA213.CoverageShards.S012.entries ++
  PA213.CoverageShards.S013.entries ++
  PA213.CoverageShards.S014.entries ++
  PA213.CoverageShards.S015.entries ++
  PA213.CoverageShards.S016.entries ++
  PA213.CoverageShards.S017.entries ++
  PA213.CoverageShards.S018.entries ++
  PA213.CoverageShards.S019.entries ++
  PA213.CoverageShards.S020.entries ++
  PA213.CoverageShards.S021.entries ++
  PA213.CoverageShards.S022.entries ++
  PA213.CoverageShards.S023.entries ++
  PA213.CoverageShards.S024.entries ++
  PA213.CoverageShards.S025.entries ++
  PA213.CoverageShards.S026.entries ++
  PA213.CoverageShards.S027.entries ++
  PA213.CoverageShards.S028.entries ++
  PA213.CoverageShards.S029.entries ++
  PA213.CoverageShards.S030.entries ++
  PA213.CoverageShards.S031.entries ++
  PA213.CoverageShards.S032.entries ++
  PA213.CoverageShards.S033.entries ++
  PA213.CoverageShards.S034.entries ++
  PA213.CoverageShards.S035.entries ++
  PA213.CoverageShards.S036.entries ++
  PA213.CoverageShards.S037.entries ++
  PA213.CoverageShards.S038.entries ++
  PA213.CoverageShards.S039.entries ++
  PA213.CoverageShards.S040.entries ++
  PA213.CoverageShards.S041.entries ++
  PA213.CoverageShards.S042.entries ++
  PA213.CoverageShards.S043.entries ++
  PA213.CoverageShards.S044.entries ++
  PA213.CoverageShards.S045.entries ++
  PA213.CoverageShards.S046.entries ++
  PA213.CoverageShards.S047.entries ++
  PA213.CoverageShards.S048.entries ++
  PA213.CoverageShards.S049.entries ++
  PA213.CoverageShards.S050.entries ++
  PA213.CoverageShards.S051.entries ++
  PA213.CoverageShards.S052.entries ++
  PA213.CoverageShards.S053.entries ++
  PA213.CoverageShards.S054.entries ++
  PA213.CoverageShards.S055.entries ++
  PA213.CoverageShards.S056.entries ++
  PA213.CoverageShards.S057.entries ++
  PA213.CoverageShards.S058.entries ++
  PA213.CoverageShards.S059.entries ++
  PA213.CoverageShards.S060.entries ++
  PA213.CoverageShards.S061.entries
private theorem sites_blocks : entries.toList.map (·.site) =
    PA213.ListBlocks.blocks sites.toList 62 := by
  simp only [entries, Array.toList_append, List.map_append,
    PA213.CoverageShards.S000.sites_block,
    PA213.CoverageShards.S001.sites_block,
    PA213.CoverageShards.S002.sites_block,
    PA213.CoverageShards.S003.sites_block,
    PA213.CoverageShards.S004.sites_block,
    PA213.CoverageShards.S005.sites_block,
    PA213.CoverageShards.S006.sites_block,
    PA213.CoverageShards.S007.sites_block,
    PA213.CoverageShards.S008.sites_block,
    PA213.CoverageShards.S009.sites_block,
    PA213.CoverageShards.S010.sites_block,
    PA213.CoverageShards.S011.sites_block,
    PA213.CoverageShards.S012.sites_block,
    PA213.CoverageShards.S013.sites_block,
    PA213.CoverageShards.S014.sites_block,
    PA213.CoverageShards.S015.sites_block,
    PA213.CoverageShards.S016.sites_block,
    PA213.CoverageShards.S017.sites_block,
    PA213.CoverageShards.S018.sites_block,
    PA213.CoverageShards.S019.sites_block,
    PA213.CoverageShards.S020.sites_block,
    PA213.CoverageShards.S021.sites_block,
    PA213.CoverageShards.S022.sites_block,
    PA213.CoverageShards.S023.sites_block,
    PA213.CoverageShards.S024.sites_block,
    PA213.CoverageShards.S025.sites_block,
    PA213.CoverageShards.S026.sites_block,
    PA213.CoverageShards.S027.sites_block,
    PA213.CoverageShards.S028.sites_block,
    PA213.CoverageShards.S029.sites_block,
    PA213.CoverageShards.S030.sites_block,
    PA213.CoverageShards.S031.sites_block,
    PA213.CoverageShards.S032.sites_block,
    PA213.CoverageShards.S033.sites_block,
    PA213.CoverageShards.S034.sites_block,
    PA213.CoverageShards.S035.sites_block,
    PA213.CoverageShards.S036.sites_block,
    PA213.CoverageShards.S037.sites_block,
    PA213.CoverageShards.S038.sites_block,
    PA213.CoverageShards.S039.sites_block,
    PA213.CoverageShards.S040.sites_block,
    PA213.CoverageShards.S041.sites_block,
    PA213.CoverageShards.S042.sites_block,
    PA213.CoverageShards.S043.sites_block,
    PA213.CoverageShards.S044.sites_block,
    PA213.CoverageShards.S045.sites_block,
    PA213.CoverageShards.S046.sites_block,
    PA213.CoverageShards.S047.sites_block,
    PA213.CoverageShards.S048.sites_block,
    PA213.CoverageShards.S049.sites_block,
    PA213.CoverageShards.S050.sites_block,
    PA213.CoverageShards.S051.sites_block,
    PA213.CoverageShards.S052.sites_block,
    PA213.CoverageShards.S053.sites_block,
    PA213.CoverageShards.S054.sites_block,
    PA213.CoverageShards.S055.sites_block,
    PA213.CoverageShards.S056.sites_block,
    PA213.CoverageShards.S057.sites_block,
    PA213.CoverageShards.S058.sites_block,
    PA213.CoverageShards.S059.sites_block,
    PA213.CoverageShards.S060.sites_block,
    PA213.CoverageShards.S061.sites_block]
  rfl
private theorem codes_blocks : entries.toList.map (·.code) =
    PA213.ListBlocks.blocks codes.toList 62 := by
  simp only [entries, Array.toList_append, List.map_append,
    PA213.CoverageShards.S000.codes_block,
    PA213.CoverageShards.S001.codes_block,
    PA213.CoverageShards.S002.codes_block,
    PA213.CoverageShards.S003.codes_block,
    PA213.CoverageShards.S004.codes_block,
    PA213.CoverageShards.S005.codes_block,
    PA213.CoverageShards.S006.codes_block,
    PA213.CoverageShards.S007.codes_block,
    PA213.CoverageShards.S008.codes_block,
    PA213.CoverageShards.S009.codes_block,
    PA213.CoverageShards.S010.codes_block,
    PA213.CoverageShards.S011.codes_block,
    PA213.CoverageShards.S012.codes_block,
    PA213.CoverageShards.S013.codes_block,
    PA213.CoverageShards.S014.codes_block,
    PA213.CoverageShards.S015.codes_block,
    PA213.CoverageShards.S016.codes_block,
    PA213.CoverageShards.S017.codes_block,
    PA213.CoverageShards.S018.codes_block,
    PA213.CoverageShards.S019.codes_block,
    PA213.CoverageShards.S020.codes_block,
    PA213.CoverageShards.S021.codes_block,
    PA213.CoverageShards.S022.codes_block,
    PA213.CoverageShards.S023.codes_block,
    PA213.CoverageShards.S024.codes_block,
    PA213.CoverageShards.S025.codes_block,
    PA213.CoverageShards.S026.codes_block,
    PA213.CoverageShards.S027.codes_block,
    PA213.CoverageShards.S028.codes_block,
    PA213.CoverageShards.S029.codes_block,
    PA213.CoverageShards.S030.codes_block,
    PA213.CoverageShards.S031.codes_block,
    PA213.CoverageShards.S032.codes_block,
    PA213.CoverageShards.S033.codes_block,
    PA213.CoverageShards.S034.codes_block,
    PA213.CoverageShards.S035.codes_block,
    PA213.CoverageShards.S036.codes_block,
    PA213.CoverageShards.S037.codes_block,
    PA213.CoverageShards.S038.codes_block,
    PA213.CoverageShards.S039.codes_block,
    PA213.CoverageShards.S040.codes_block,
    PA213.CoverageShards.S041.codes_block,
    PA213.CoverageShards.S042.codes_block,
    PA213.CoverageShards.S043.codes_block,
    PA213.CoverageShards.S044.codes_block,
    PA213.CoverageShards.S045.codes_block,
    PA213.CoverageShards.S046.codes_block,
    PA213.CoverageShards.S047.codes_block,
    PA213.CoverageShards.S048.codes_block,
    PA213.CoverageShards.S049.codes_block,
    PA213.CoverageShards.S050.codes_block,
    PA213.CoverageShards.S051.codes_block,
    PA213.CoverageShards.S052.codes_block,
    PA213.CoverageShards.S053.codes_block,
    PA213.CoverageShards.S054.codes_block,
    PA213.CoverageShards.S055.codes_block,
    PA213.CoverageShards.S056.codes_block,
    PA213.CoverageShards.S057.codes_block,
    PA213.CoverageShards.S058.codes_block,
    PA213.CoverageShards.S059.codes_block,
    PA213.CoverageShards.S060.codes_block,
    PA213.CoverageShards.S061.codes_block]
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
end PA213.RuntimeCoverage
