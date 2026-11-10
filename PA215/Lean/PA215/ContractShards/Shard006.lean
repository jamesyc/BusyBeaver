import PA215.ContractShards.Shard006Part0
import PA215.ContractShards.Shard006Part1
import PA215.ContractShards.Shard006Part2
import PA215.ContractShards.Shard006Part3
import PA215.ContractShards.Shard006Part4
import PA215.ContractShards.Shard006Part5
import PA215.ContractShards.Shard006Part6
import PA215.ContractShards.Shard006Part7
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard006
open PA215.Contracts

def records : List Certified :=
  PA215.ContractShards.Shard006Part0.records ++
  PA215.ContractShards.Shard006Part1.records ++
  PA215.ContractShards.Shard006Part2.records ++
  PA215.ContractShards.Shard006Part3.records ++
  PA215.ContractShards.Shard006Part4.records ++
  PA215.ContractShards.Shard006Part5.records ++
  PA215.ContractShards.Shard006Part6.records ++
  PA215.ContractShards.Shard006Part7.records

def ids : List Nat := records.map Certified.id

theorem exact_ids : ids = [774, 775, 776, 777, 778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799, 800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831, 832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895, 896, 897, 898, 899, 900, 901] := by decide
theorem count : records.length = 128 := by decide
theorem distinct_ids : ids.Nodup := by decide

end PA215.ContractShards.Shard006
