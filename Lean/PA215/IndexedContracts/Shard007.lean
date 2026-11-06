import PA215.IndexedContracts.Shard007Part0
import PA215.IndexedContracts.Shard007Part1
import PA215.IndexedContracts.Shard007Part2
import PA215.IndexedContracts.Shard007Part3
import PA215.IndexedContracts.Shard007Part4
import PA215.IndexedContracts.Shard007Part5
import PA215.IndexedContracts.Shard007Part6
import PA215.IndexedContracts.Shard007Part7
namespace PA215.IndexedContracts.Shard007
open PA215.Census
def records : OriginalRegistry :=
  PA215.IndexedContracts.Shard007Part0.records ++
  PA215.IndexedContracts.Shard007Part1.records ++
  PA215.IndexedContracts.Shard007Part2.records ++
  PA215.IndexedContracts.Shard007Part3.records ++
  PA215.IndexedContracts.Shard007Part4.records ++
  PA215.IndexedContracts.Shard007Part5.records ++
  PA215.IndexedContracts.Shard007Part6.records ++
  PA215.IndexedContracts.Shard007Part7.records

theorem exact_ids : records.map (fun e => e.1.val) = [902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029] := by
  simp only [records, List.map_append, PA215.IndexedContracts.Shard007Part0.exact_ids, PA215.IndexedContracts.Shard007Part1.exact_ids, PA215.IndexedContracts.Shard007Part2.exact_ids, PA215.IndexedContracts.Shard007Part3.exact_ids, PA215.IndexedContracts.Shard007Part4.exact_ids, PA215.IndexedContracts.Shard007Part5.exact_ids, PA215.IndexedContracts.Shard007Part6.exact_ids, PA215.IndexedContracts.Shard007Part7.exact_ids]
  rfl

end PA215.IndexedContracts.Shard007
