module

public import PA213.ListBlocks
public import PA211.UserCandidate.CoverageShards.S000
public import PA211.UserCandidate.CoverageShards.S001
public import PA211.UserCandidate.CoverageShards.S002
public import PA211.UserCandidate.CoverageShards.S003
public import PA211.UserCandidate.CoverageShards.S004
public import PA211.UserCandidate.CoverageShards.S005
public import PA211.UserCandidate.CoverageShards.S006
public import PA211.UserCandidate.CoverageShards.S007
public import PA211.UserCandidate.CoverageShards.S008
public import PA211.UserCandidate.CoverageShards.S009
public import PA211.UserCandidate.CoverageShards.S010
public import PA211.UserCandidate.CoverageShards.S011
public import PA211.UserCandidate.CoverageShards.S012
public import PA211.UserCandidate.CoverageShards.S013
public import PA211.UserCandidate.CoverageShards.S014
public import PA211.UserCandidate.CoverageShards.S015
public import PA211.UserCandidate.CoverageShards.S016
public import PA211.UserCandidate.CoverageShards.S017
public import PA211.UserCandidate.CoverageShards.S018
public import PA211.UserCandidate.CoverageShards.S019
public import PA211.UserCandidate.CoverageShards.S020
public import PA211.UserCandidate.CoverageShards.S021
public import PA211.UserCandidate.CoverageShards.S022
public import PA211.UserCandidate.CoverageShards.S023
public import PA211.UserCandidate.CoverageShards.S024
public import PA211.UserCandidate.CoverageShards.S025
public import PA211.UserCandidate.CoverageShards.S026
public import PA211.UserCandidate.CoverageShards.S027
public import PA211.UserCandidate.CoverageShards.S028
public import PA211.UserCandidate.CoverageShards.S029
public import PA211.UserCandidate.CoverageShards.S030
public import PA211.UserCandidate.CoverageShards.S031
public import PA211.UserCandidate.CoverageShards.S032
public import PA211.UserCandidate.CoverageShards.S033
public import PA211.UserCandidate.CoverageShards.S034
public import PA211.UserCandidate.CoverageShards.S035
public import PA211.UserCandidate.CoverageShards.S036
public import PA211.UserCandidate.CoverageShards.S037
public import PA211.UserCandidate.CoverageShards.S038
public import PA211.UserCandidate.CoverageShards.S039
public import PA211.UserCandidate.CoverageShards.S040
public import PA211.UserCandidate.CoverageShards.S041
public import PA211.UserCandidate.CoverageShards.S042
public import PA211.UserCandidate.CoverageShards.S043
public import PA211.UserCandidate.CoverageShards.S044
public import PA211.UserCandidate.CoverageShards.S045
public import PA211.UserCandidate.CoverageShards.S046
public import PA211.UserCandidate.CoverageShards.S047
public import PA211.UserCandidate.CoverageShards.S048
public import PA211.UserCandidate.CoverageShards.S049
public import PA211.UserCandidate.CoverageShards.S050
public import PA211.UserCandidate.CoverageShards.S051
public import PA211.UserCandidate.CoverageShards.S052
public import PA211.UserCandidate.CoverageShards.S053
public import PA211.UserCandidate.CoverageShards.S054
public import PA211.UserCandidate.CoverageShards.S055
public import PA211.UserCandidate.CoverageShards.S056
public import PA211.UserCandidate.CoverageShards.S057
public import PA211.UserCandidate.CoverageShards.S058
public import PA211.UserCandidate.CoverageShards.S059
public import PA211.UserCandidate.CoverageShards.S060
public import PA211.UserCandidate.CoverageShards.S061

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000
namespace PA211.UserCandidate.RuntimeCoverage
open PA215.Source PA211.UserCandidate.PrimitiveSimulation
def entries : Array (Entry PA211.UserCandidate.Source.path 3947) :=
  PA211.UserCandidate.CoverageShards.S000.entries ++
  PA211.UserCandidate.CoverageShards.S001.entries ++
  PA211.UserCandidate.CoverageShards.S002.entries ++
  PA211.UserCandidate.CoverageShards.S003.entries ++
  PA211.UserCandidate.CoverageShards.S004.entries ++
  PA211.UserCandidate.CoverageShards.S005.entries ++
  PA211.UserCandidate.CoverageShards.S006.entries ++
  PA211.UserCandidate.CoverageShards.S007.entries ++
  PA211.UserCandidate.CoverageShards.S008.entries ++
  PA211.UserCandidate.CoverageShards.S009.entries ++
  PA211.UserCandidate.CoverageShards.S010.entries ++
  PA211.UserCandidate.CoverageShards.S011.entries ++
  PA211.UserCandidate.CoverageShards.S012.entries ++
  PA211.UserCandidate.CoverageShards.S013.entries ++
  PA211.UserCandidate.CoverageShards.S014.entries ++
  PA211.UserCandidate.CoverageShards.S015.entries ++
  PA211.UserCandidate.CoverageShards.S016.entries ++
  PA211.UserCandidate.CoverageShards.S017.entries ++
  PA211.UserCandidate.CoverageShards.S018.entries ++
  PA211.UserCandidate.CoverageShards.S019.entries ++
  PA211.UserCandidate.CoverageShards.S020.entries ++
  PA211.UserCandidate.CoverageShards.S021.entries ++
  PA211.UserCandidate.CoverageShards.S022.entries ++
  PA211.UserCandidate.CoverageShards.S023.entries ++
  PA211.UserCandidate.CoverageShards.S024.entries ++
  PA211.UserCandidate.CoverageShards.S025.entries ++
  PA211.UserCandidate.CoverageShards.S026.entries ++
  PA211.UserCandidate.CoverageShards.S027.entries ++
  PA211.UserCandidate.CoverageShards.S028.entries ++
  PA211.UserCandidate.CoverageShards.S029.entries ++
  PA211.UserCandidate.CoverageShards.S030.entries ++
  PA211.UserCandidate.CoverageShards.S031.entries ++
  PA211.UserCandidate.CoverageShards.S032.entries ++
  PA211.UserCandidate.CoverageShards.S033.entries ++
  PA211.UserCandidate.CoverageShards.S034.entries ++
  PA211.UserCandidate.CoverageShards.S035.entries ++
  PA211.UserCandidate.CoverageShards.S036.entries ++
  PA211.UserCandidate.CoverageShards.S037.entries ++
  PA211.UserCandidate.CoverageShards.S038.entries ++
  PA211.UserCandidate.CoverageShards.S039.entries ++
  PA211.UserCandidate.CoverageShards.S040.entries ++
  PA211.UserCandidate.CoverageShards.S041.entries ++
  PA211.UserCandidate.CoverageShards.S042.entries ++
  PA211.UserCandidate.CoverageShards.S043.entries ++
  PA211.UserCandidate.CoverageShards.S044.entries ++
  PA211.UserCandidate.CoverageShards.S045.entries ++
  PA211.UserCandidate.CoverageShards.S046.entries ++
  PA211.UserCandidate.CoverageShards.S047.entries ++
  PA211.UserCandidate.CoverageShards.S048.entries ++
  PA211.UserCandidate.CoverageShards.S049.entries ++
  PA211.UserCandidate.CoverageShards.S050.entries ++
  PA211.UserCandidate.CoverageShards.S051.entries ++
  PA211.UserCandidate.CoverageShards.S052.entries ++
  PA211.UserCandidate.CoverageShards.S053.entries ++
  PA211.UserCandidate.CoverageShards.S054.entries ++
  PA211.UserCandidate.CoverageShards.S055.entries ++
  PA211.UserCandidate.CoverageShards.S056.entries ++
  PA211.UserCandidate.CoverageShards.S057.entries ++
  PA211.UserCandidate.CoverageShards.S058.entries ++
  PA211.UserCandidate.CoverageShards.S059.entries ++
  PA211.UserCandidate.CoverageShards.S060.entries ++
  PA211.UserCandidate.CoverageShards.S061.entries
private theorem sites_blocks : entries.toList.map (·.site) =
    PA213.ListBlocks.blocks PA211.UserCandidate.Source.sites.toList 62 := by
  simp only [entries, Array.toList_append, List.map_append,
    PA211.UserCandidate.CoverageShards.S000.sites_block,
    PA211.UserCandidate.CoverageShards.S001.sites_block,
    PA211.UserCandidate.CoverageShards.S002.sites_block,
    PA211.UserCandidate.CoverageShards.S003.sites_block,
    PA211.UserCandidate.CoverageShards.S004.sites_block,
    PA211.UserCandidate.CoverageShards.S005.sites_block,
    PA211.UserCandidate.CoverageShards.S006.sites_block,
    PA211.UserCandidate.CoverageShards.S007.sites_block,
    PA211.UserCandidate.CoverageShards.S008.sites_block,
    PA211.UserCandidate.CoverageShards.S009.sites_block,
    PA211.UserCandidate.CoverageShards.S010.sites_block,
    PA211.UserCandidate.CoverageShards.S011.sites_block,
    PA211.UserCandidate.CoverageShards.S012.sites_block,
    PA211.UserCandidate.CoverageShards.S013.sites_block,
    PA211.UserCandidate.CoverageShards.S014.sites_block,
    PA211.UserCandidate.CoverageShards.S015.sites_block,
    PA211.UserCandidate.CoverageShards.S016.sites_block,
    PA211.UserCandidate.CoverageShards.S017.sites_block,
    PA211.UserCandidate.CoverageShards.S018.sites_block,
    PA211.UserCandidate.CoverageShards.S019.sites_block,
    PA211.UserCandidate.CoverageShards.S020.sites_block,
    PA211.UserCandidate.CoverageShards.S021.sites_block,
    PA211.UserCandidate.CoverageShards.S022.sites_block,
    PA211.UserCandidate.CoverageShards.S023.sites_block,
    PA211.UserCandidate.CoverageShards.S024.sites_block,
    PA211.UserCandidate.CoverageShards.S025.sites_block,
    PA211.UserCandidate.CoverageShards.S026.sites_block,
    PA211.UserCandidate.CoverageShards.S027.sites_block,
    PA211.UserCandidate.CoverageShards.S028.sites_block,
    PA211.UserCandidate.CoverageShards.S029.sites_block,
    PA211.UserCandidate.CoverageShards.S030.sites_block,
    PA211.UserCandidate.CoverageShards.S031.sites_block,
    PA211.UserCandidate.CoverageShards.S032.sites_block,
    PA211.UserCandidate.CoverageShards.S033.sites_block,
    PA211.UserCandidate.CoverageShards.S034.sites_block,
    PA211.UserCandidate.CoverageShards.S035.sites_block,
    PA211.UserCandidate.CoverageShards.S036.sites_block,
    PA211.UserCandidate.CoverageShards.S037.sites_block,
    PA211.UserCandidate.CoverageShards.S038.sites_block,
    PA211.UserCandidate.CoverageShards.S039.sites_block,
    PA211.UserCandidate.CoverageShards.S040.sites_block,
    PA211.UserCandidate.CoverageShards.S041.sites_block,
    PA211.UserCandidate.CoverageShards.S042.sites_block,
    PA211.UserCandidate.CoverageShards.S043.sites_block,
    PA211.UserCandidate.CoverageShards.S044.sites_block,
    PA211.UserCandidate.CoverageShards.S045.sites_block,
    PA211.UserCandidate.CoverageShards.S046.sites_block,
    PA211.UserCandidate.CoverageShards.S047.sites_block,
    PA211.UserCandidate.CoverageShards.S048.sites_block,
    PA211.UserCandidate.CoverageShards.S049.sites_block,
    PA211.UserCandidate.CoverageShards.S050.sites_block,
    PA211.UserCandidate.CoverageShards.S051.sites_block,
    PA211.UserCandidate.CoverageShards.S052.sites_block,
    PA211.UserCandidate.CoverageShards.S053.sites_block,
    PA211.UserCandidate.CoverageShards.S054.sites_block,
    PA211.UserCandidate.CoverageShards.S055.sites_block,
    PA211.UserCandidate.CoverageShards.S056.sites_block,
    PA211.UserCandidate.CoverageShards.S057.sites_block,
    PA211.UserCandidate.CoverageShards.S058.sites_block,
    PA211.UserCandidate.CoverageShards.S059.sites_block,
    PA211.UserCandidate.CoverageShards.S060.sites_block,
    PA211.UserCandidate.CoverageShards.S061.sites_block]
  rfl
private theorem codes_blocks : entries.toList.map (·.code) =
    PA213.ListBlocks.blocks PA213.SourceProgram.codes.toList 62 := by
  simp only [entries, Array.toList_append, List.map_append,
    PA211.UserCandidate.CoverageShards.S000.codes_block,
    PA211.UserCandidate.CoverageShards.S001.codes_block,
    PA211.UserCandidate.CoverageShards.S002.codes_block,
    PA211.UserCandidate.CoverageShards.S003.codes_block,
    PA211.UserCandidate.CoverageShards.S004.codes_block,
    PA211.UserCandidate.CoverageShards.S005.codes_block,
    PA211.UserCandidate.CoverageShards.S006.codes_block,
    PA211.UserCandidate.CoverageShards.S007.codes_block,
    PA211.UserCandidate.CoverageShards.S008.codes_block,
    PA211.UserCandidate.CoverageShards.S009.codes_block,
    PA211.UserCandidate.CoverageShards.S010.codes_block,
    PA211.UserCandidate.CoverageShards.S011.codes_block,
    PA211.UserCandidate.CoverageShards.S012.codes_block,
    PA211.UserCandidate.CoverageShards.S013.codes_block,
    PA211.UserCandidate.CoverageShards.S014.codes_block,
    PA211.UserCandidate.CoverageShards.S015.codes_block,
    PA211.UserCandidate.CoverageShards.S016.codes_block,
    PA211.UserCandidate.CoverageShards.S017.codes_block,
    PA211.UserCandidate.CoverageShards.S018.codes_block,
    PA211.UserCandidate.CoverageShards.S019.codes_block,
    PA211.UserCandidate.CoverageShards.S020.codes_block,
    PA211.UserCandidate.CoverageShards.S021.codes_block,
    PA211.UserCandidate.CoverageShards.S022.codes_block,
    PA211.UserCandidate.CoverageShards.S023.codes_block,
    PA211.UserCandidate.CoverageShards.S024.codes_block,
    PA211.UserCandidate.CoverageShards.S025.codes_block,
    PA211.UserCandidate.CoverageShards.S026.codes_block,
    PA211.UserCandidate.CoverageShards.S027.codes_block,
    PA211.UserCandidate.CoverageShards.S028.codes_block,
    PA211.UserCandidate.CoverageShards.S029.codes_block,
    PA211.UserCandidate.CoverageShards.S030.codes_block,
    PA211.UserCandidate.CoverageShards.S031.codes_block,
    PA211.UserCandidate.CoverageShards.S032.codes_block,
    PA211.UserCandidate.CoverageShards.S033.codes_block,
    PA211.UserCandidate.CoverageShards.S034.codes_block,
    PA211.UserCandidate.CoverageShards.S035.codes_block,
    PA211.UserCandidate.CoverageShards.S036.codes_block,
    PA211.UserCandidate.CoverageShards.S037.codes_block,
    PA211.UserCandidate.CoverageShards.S038.codes_block,
    PA211.UserCandidate.CoverageShards.S039.codes_block,
    PA211.UserCandidate.CoverageShards.S040.codes_block,
    PA211.UserCandidate.CoverageShards.S041.codes_block,
    PA211.UserCandidate.CoverageShards.S042.codes_block,
    PA211.UserCandidate.CoverageShards.S043.codes_block,
    PA211.UserCandidate.CoverageShards.S044.codes_block,
    PA211.UserCandidate.CoverageShards.S045.codes_block,
    PA211.UserCandidate.CoverageShards.S046.codes_block,
    PA211.UserCandidate.CoverageShards.S047.codes_block,
    PA211.UserCandidate.CoverageShards.S048.codes_block,
    PA211.UserCandidate.CoverageShards.S049.codes_block,
    PA211.UserCandidate.CoverageShards.S050.codes_block,
    PA211.UserCandidate.CoverageShards.S051.codes_block,
    PA211.UserCandidate.CoverageShards.S052.codes_block,
    PA211.UserCandidate.CoverageShards.S053.codes_block,
    PA211.UserCandidate.CoverageShards.S054.codes_block,
    PA211.UserCandidate.CoverageShards.S055.codes_block,
    PA211.UserCandidate.CoverageShards.S056.codes_block,
    PA211.UserCandidate.CoverageShards.S057.codes_block,
    PA211.UserCandidate.CoverageShards.S058.codes_block,
    PA211.UserCandidate.CoverageShards.S059.codes_block,
    PA211.UserCandidate.CoverageShards.S060.codes_block,
    PA211.UserCandidate.CoverageShards.S061.codes_block]
  rfl
theorem sites_list_eq : entries.toList.map (·.site) = PA211.UserCandidate.Source.sites.toList := by
  rw [sites_blocks, PA213.ListBlocks.blocks_eq_take, List.take_of_length_le]
  decide
theorem sites_eq : entries.map (·.site) = PA211.UserCandidate.Source.sites := by
  apply Array.toList_inj.mp
  simpa using sites_list_eq
theorem codes_list_eq : entries.toList.map (·.code) = PA213.SourceProgram.codes.toList := by
  rw [codes_blocks, PA213.ListBlocks.blocks_eq_take, List.take_of_length_le]
  decide
theorem codes_eq : entries.map (·.code) = PA213.SourceProgram.codes := by
  apply Array.toList_inj.mp
  simpa using codes_list_eq
theorem count_eq : entries.size = 3947 := by
  have h := congrArg Array.size sites_eq
  simpa only [Array.size_map, PA211.UserCandidate.Source.sites_count] using h
end PA211.UserCandidate.RuntimeCoverage
