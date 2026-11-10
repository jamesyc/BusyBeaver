import PA213.SourceCheckShards.S000
import PA213.SourceCheckShards.S001
import PA213.SourceCheckShards.S002
import PA213.SourceCheckShards.S003
import PA213.SourceCheckShards.S004
import PA213.SourceCheckShards.S005
import PA213.SourceCheckShards.S006
import PA213.SourceCheckShards.S007
import PA213.SourceCheckShards.S008
import PA213.SourceCheckShards.S009
import PA213.SourceCheckShards.S010
import PA213.SourceCheckShards.S011
import PA213.SourceCheckShards.S012
import PA213.SourceCheckShards.S013
import PA213.SourceCheckShards.S014
import PA213.SourceCheckShards.S015
import PA213.SourceCheckShards.S016
import PA213.SourceCheckShards.S017
import PA213.SourceCheckShards.S018
import PA213.SourceCheckShards.S019
import PA213.SourceCheckShards.S020
import PA213.SourceCheckShards.S021
import PA213.SourceCheckShards.S022
import PA213.SourceCheckShards.S023
import PA213.SourceCheckShards.S024
import PA213.SourceCheckShards.S025
import PA213.SourceCheckShards.S026
import PA213.SourceCheckShards.S027
import PA213.SourceCheckShards.S028
import PA213.SourceCheckShards.S029
import PA213.SourceCheckShards.S030
import PA213.SourceCheckShards.S031
import PA213.SourceCheckShards.S032
import PA213.SourceCheckShards.S033
import PA213.SourceCheckShards.S034
import PA213.SourceCheckShards.S035
import PA213.SourceCheckShards.S036
import PA213.SourceCheckShards.S037
import PA213.SourceCheckShards.S038
import PA213.SourceCheckShards.S039
import PA213.SourceCheckShards.S040
import PA213.SourceCheckShards.S041
import PA213.SourceCheckShards.S042
import PA213.SourceCheckShards.S043
import PA213.SourceCheckShards.S044
import PA213.SourceCheckShards.S045
import PA213.SourceCheckShards.S046
import PA213.SourceCheckShards.S047
import PA213.SourceCheckShards.S048
import PA213.SourceCheckShards.S049
import PA213.SourceCheckShards.S050
import PA213.SourceCheckShards.S051
import PA213.SourceCheckShards.S052
import PA213.SourceCheckShards.S053
import PA213.SourceCheckShards.S054
import PA213.SourceCheckShards.S055
import PA213.SourceCheckShards.S056
import PA213.SourceCheckShards.S057
import PA213.SourceCheckShards.S058
import PA213.SourceCheckShards.S059
import PA213.SourceCheckShards.S060
import PA213.SourceCheckShards.S061
namespace PA213.AllSourceChecks
open PA213.SourceCheck
theorem checked (i : Nat) (hi : i < 3947) : atCheck i = true := by
  by_cases h0 : i < 64
  · exact range_sound PA213.SourceCheckShards.S000.checked i (by omega) h0
  by_cases h1 : i < 128
  · exact range_sound PA213.SourceCheckShards.S001.checked i (by omega) h1
  by_cases h2 : i < 192
  · exact range_sound PA213.SourceCheckShards.S002.checked i (by omega) h2
  by_cases h3 : i < 256
  · exact range_sound PA213.SourceCheckShards.S003.checked i (by omega) h3
  by_cases h4 : i < 320
  · exact range_sound PA213.SourceCheckShards.S004.checked i (by omega) h4
  by_cases h5 : i < 384
  · exact range_sound PA213.SourceCheckShards.S005.checked i (by omega) h5
  by_cases h6 : i < 448
  · exact range_sound PA213.SourceCheckShards.S006.checked i (by omega) h6
  by_cases h7 : i < 512
  · exact range_sound PA213.SourceCheckShards.S007.checked i (by omega) h7
  by_cases h8 : i < 576
  · exact range_sound PA213.SourceCheckShards.S008.checked i (by omega) h8
  by_cases h9 : i < 640
  · exact range_sound PA213.SourceCheckShards.S009.checked i (by omega) h9
  by_cases h10 : i < 704
  · exact range_sound PA213.SourceCheckShards.S010.checked i (by omega) h10
  by_cases h11 : i < 768
  · exact range_sound PA213.SourceCheckShards.S011.checked i (by omega) h11
  by_cases h12 : i < 832
  · exact range_sound PA213.SourceCheckShards.S012.checked i (by omega) h12
  by_cases h13 : i < 896
  · exact range_sound PA213.SourceCheckShards.S013.checked i (by omega) h13
  by_cases h14 : i < 960
  · exact range_sound PA213.SourceCheckShards.S014.checked i (by omega) h14
  by_cases h15 : i < 1024
  · exact range_sound PA213.SourceCheckShards.S015.checked i (by omega) h15
  by_cases h16 : i < 1088
  · exact range_sound PA213.SourceCheckShards.S016.checked i (by omega) h16
  by_cases h17 : i < 1152
  · exact range_sound PA213.SourceCheckShards.S017.checked i (by omega) h17
  by_cases h18 : i < 1216
  · exact range_sound PA213.SourceCheckShards.S018.checked i (by omega) h18
  by_cases h19 : i < 1280
  · exact range_sound PA213.SourceCheckShards.S019.checked i (by omega) h19
  by_cases h20 : i < 1344
  · exact range_sound PA213.SourceCheckShards.S020.checked i (by omega) h20
  by_cases h21 : i < 1408
  · exact range_sound PA213.SourceCheckShards.S021.checked i (by omega) h21
  by_cases h22 : i < 1472
  · exact range_sound PA213.SourceCheckShards.S022.checked i (by omega) h22
  by_cases h23 : i < 1536
  · exact range_sound PA213.SourceCheckShards.S023.checked i (by omega) h23
  by_cases h24 : i < 1600
  · exact range_sound PA213.SourceCheckShards.S024.checked i (by omega) h24
  by_cases h25 : i < 1664
  · exact range_sound PA213.SourceCheckShards.S025.checked i (by omega) h25
  by_cases h26 : i < 1728
  · exact range_sound PA213.SourceCheckShards.S026.checked i (by omega) h26
  by_cases h27 : i < 1792
  · exact range_sound PA213.SourceCheckShards.S027.checked i (by omega) h27
  by_cases h28 : i < 1856
  · exact range_sound PA213.SourceCheckShards.S028.checked i (by omega) h28
  by_cases h29 : i < 1920
  · exact range_sound PA213.SourceCheckShards.S029.checked i (by omega) h29
  by_cases h30 : i < 1984
  · exact range_sound PA213.SourceCheckShards.S030.checked i (by omega) h30
  by_cases h31 : i < 2048
  · exact range_sound PA213.SourceCheckShards.S031.checked i (by omega) h31
  by_cases h32 : i < 2112
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S032.checked i (by omega) h32
  by_cases h33 : i < 2176
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S033.checked i (by omega) h33
  by_cases h34 : i < 2240
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S034.checked i (by omega) h34
  by_cases h35 : i < 2304
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S035.checked i (by omega) h35
  by_cases h36 : i < 2368
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S036.checked i (by omega) h36
  by_cases h37 : i < 2432
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S037.checked i (by omega) h37
  by_cases h38 : i < 2496
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S038.checked i (by omega) h38
  by_cases h39 : i < 2560
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S039.checked i (by omega) h39
  by_cases h40 : i < 2624
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S040.checked i (by omega) h40
  by_cases h41 : i < 2688
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S041.checked i (by omega) h41
  by_cases h42 : i < 2752
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S042.checked i (by omega) h42
  by_cases h43 : i < 2816
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S043.checked i (by omega) h43
  by_cases h44 : i < 2880
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S044.checked i (by omega) h44
  by_cases h45 : i < 2944
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S045.checked i (by omega) h45
  by_cases h46 : i < 3008
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S046.checked i (by omega) h46
  by_cases h47 : i < 3072
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S047.checked i (by omega) h47
  by_cases h48 : i < 3136
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S048.checked i (by omega) h48
  by_cases h49 : i < 3200
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S049.checked i (by omega) h49
  by_cases h50 : i < 3264
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S050.checked i (by omega) h50
  by_cases h51 : i < 3328
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S051.checked i (by omega) h51
  by_cases h52 : i < 3392
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S052.checked i (by omega) h52
  by_cases h53 : i < 3456
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S053.checked i (by omega) h53
  by_cases h54 : i < 3520
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S054.checked i (by omega) h54
  by_cases h55 : i < 3584
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S055.checked i (by omega) h55
  by_cases h56 : i < 3648
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S056.checked i (by omega) h56
  by_cases h57 : i < 3712
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S057.checked i (by omega) h57
  by_cases h58 : i < 3776
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S058.checked i (by omega) h58
  by_cases h59 : i < 3840
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S059.checked i (by omega) h59
  by_cases h60 : i < 3904
  · exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S060.checked i (by omega) h60
  exact PA213.FastSourceCheck.sound PA213.SourceCheckShards.S061.checked i (by omega) hi
end PA213.AllSourceChecks
