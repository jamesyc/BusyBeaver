import PA215.ContractShards.Shard022Part0
import PA215.ContractShards.Shard022Part1
import PA215.ContractShards.Shard022Part2
import PA215.ContractShards.Shard022Part3
import PA215.ContractShards.Shard022Part4
import PA215.ContractShards.Shard022Part5
import PA215.ContractShards.Shard022Part6
import PA215.ContractShards.Shard022Part7
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard022
open PA215.Contracts

def records : List Certified :=
  PA215.ContractShards.Shard022Part0.records ++
  PA215.ContractShards.Shard022Part1.records ++
  PA215.ContractShards.Shard022Part2.records ++
  PA215.ContractShards.Shard022Part3.records ++
  PA215.ContractShards.Shard022Part4.records ++
  PA215.ContractShards.Shard022Part5.records ++
  PA215.ContractShards.Shard022Part6.records ++
  PA215.ContractShards.Shard022Part7.records

def ids : List Nat := records.map Certified.id

theorem exact_ids : ids = [2822, 2823, 2824, 2825, 2826, 2827, 2828, 2829, 2830, 2831, 2832, 2833, 2834, 2835, 2836, 2837, 2838, 2839, 2840, 2841, 2842, 2843, 2844, 2845, 2846, 2847, 2848, 2849, 2850, 2851, 2852, 2853, 2854, 2855, 2856, 2857, 2858, 2859, 2860, 2861, 2862, 2863, 2864, 2865, 2866, 2867, 2868, 2869, 2870, 2871, 2872, 2873, 2874, 2875, 2876, 2877, 2878, 2879, 2880, 2881, 2882, 2883, 2884, 2885, 2886, 2887, 2888, 2889, 2890, 2891, 2892, 2893, 2894, 2895, 2896, 2897, 2898, 2899, 2900, 2901, 2902, 2903, 2904, 2905, 2906, 2907, 2908, 2909, 2910, 2911, 2912, 2913, 2914, 2915, 2916, 2917, 2918, 2919, 2920, 2921, 2922, 2923, 2924, 2925, 2926, 2927, 2928, 2929, 2930, 2931, 2932, 2933, 2934, 2935, 2936, 2937, 2938, 2939, 2940, 2941, 2942, 2943, 2944, 2945, 2946, 2947, 2948, 2949] := by decide
theorem count : records.length = 128 := by decide
theorem distinct_ids : ids.Nodup := by decide

end PA215.ContractShards.Shard022
