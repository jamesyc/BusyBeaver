module

public import PA213.ListBlocks
public import User211ModelCoverage000
public import User211ModelCoverage001
public import User211ModelCoverage002
public import User211ModelCoverage003
public import User211ModelCoverage004
public import User211ModelCoverage005
public import User211ModelCoverage006
public import User211ModelCoverage007
public import User211ModelCoverage008
public import User211ModelCoverage009
public import User211ModelCoverage010
public import User211ModelCoverage011
public import User211ModelCoverage012
public import User211ModelCoverage013
public import User211ModelCoverage014
public import User211ModelCoverage015
public import User211ModelCoverage016
public import User211ModelCoverage017
public import User211ModelCoverage018
public import User211ModelCoverage019
public import User211ModelCoverage020
public import User211ModelCoverage021
public import User211ModelCoverage022
public import User211ModelCoverage023
public import User211ModelCoverage024
public import User211ModelCoverage025
public import User211ModelCoverage026
public import User211ModelCoverage027
public import User211ModelCoverage028
public import User211ModelCoverage029
public import User211ModelCoverage030
public import User211ModelCoverage031
public import User211ModelCoverage032
public import User211ModelCoverage033
public import User211ModelCoverage034
public import User211ModelCoverage035
public import User211ModelCoverage036
public import User211ModelCoverage037
public import User211ModelCoverage038
public import User211ModelCoverage039
public import User211ModelCoverage040
public import User211ModelCoverage041
public import User211ModelCoverage042
public import User211ModelCoverage043
public import User211ModelCoverage044
public import User211ModelCoverage045
public import User211ModelCoverage046
public import User211ModelCoverage047
public import User211ModelCoverage048
public import User211ModelCoverage049
public import User211ModelCoverage050
public import User211ModelCoverage051
public import User211ModelCoverage052
public import User211ModelCoverage053
public import User211ModelCoverage054
public import User211ModelCoverage055
public import User211ModelCoverage056
public import User211ModelCoverage057
public import User211ModelCoverage058
public import User211ModelCoverage059
public import User211ModelCoverage060
public import User211ModelCoverage061

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000
namespace PA211.UserCandidate.PA.ModelCoverage
open PA215.Source PA211.UserCandidate.PA.ModelPrimitive
def entries : Array (Entry PA211.UserCandidate.Source.path 3947) :=
  PA211.UserCandidate.PA.ModelCoverageShards.S000.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S001.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S002.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S003.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S004.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S005.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S006.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S007.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S008.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S009.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S010.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S011.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S012.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S013.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S014.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S015.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S016.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S017.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S018.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S019.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S020.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S021.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S022.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S023.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S024.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S025.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S026.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S027.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S028.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S029.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S030.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S031.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S032.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S033.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S034.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S035.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S036.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S037.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S038.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S039.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S040.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S041.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S042.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S043.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S044.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S045.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S046.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S047.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S048.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S049.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S050.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S051.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S052.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S053.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S054.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S055.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S056.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S057.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S058.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S059.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S060.entries ++
  PA211.UserCandidate.PA.ModelCoverageShards.S061.entries
private theorem sites_blocks : entries.toList.map (·.site) =
    PA213.ListBlocks.blocks PA211.UserCandidate.Source.sites.toList 62 := by
  simp only [entries, Array.toList_append, List.map_append,
    PA211.UserCandidate.PA.ModelCoverageShards.S000.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S001.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S002.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S003.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S004.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S005.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S006.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S007.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S008.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S009.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S010.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S011.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S012.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S013.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S014.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S015.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S016.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S017.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S018.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S019.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S020.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S021.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S022.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S023.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S024.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S025.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S026.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S027.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S028.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S029.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S030.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S031.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S032.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S033.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S034.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S035.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S036.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S037.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S038.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S039.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S040.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S041.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S042.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S043.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S044.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S045.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S046.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S047.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S048.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S049.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S050.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S051.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S052.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S053.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S054.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S055.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S056.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S057.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S058.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S059.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S060.sites_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S061.sites_block]
  rfl
private theorem codes_blocks : entries.toList.map (·.code) =
    PA213.ListBlocks.blocks PA213.SourceProgram.codes.toList 62 := by
  simp only [entries, Array.toList_append, List.map_append,
    PA211.UserCandidate.PA.ModelCoverageShards.S000.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S001.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S002.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S003.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S004.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S005.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S006.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S007.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S008.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S009.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S010.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S011.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S012.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S013.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S014.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S015.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S016.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S017.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S018.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S019.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S020.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S021.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S022.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S023.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S024.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S025.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S026.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S027.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S028.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S029.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S030.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S031.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S032.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S033.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S034.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S035.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S036.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S037.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S038.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S039.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S040.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S041.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S042.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S043.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S044.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S045.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S046.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S047.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S048.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S049.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S050.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S051.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S052.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S053.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S054.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S055.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S056.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S057.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S058.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S059.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S060.codes_block,
    PA211.UserCandidate.PA.ModelCoverageShards.S061.codes_block]
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
end PA211.UserCandidate.PA.ModelCoverage
