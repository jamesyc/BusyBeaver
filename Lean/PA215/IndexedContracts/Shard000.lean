import PA215.IndexedContracts.Shard000Part0
import PA215.IndexedContracts.Shard000Part1
import PA215.IndexedContracts.Shard000Part2
import PA215.IndexedContracts.Shard000Part3
import PA215.IndexedContracts.Shard000Part4
import PA215.IndexedContracts.Shard000Part5
import PA215.IndexedContracts.Shard000Part6
import PA215.IndexedContracts.Shard000Part7
namespace PA215.IndexedContracts.Shard000
open PA215.Census
def records : OriginalRegistry :=
  PA215.IndexedContracts.Shard000Part0.records ++
  PA215.IndexedContracts.Shard000Part1.records ++
  PA215.IndexedContracts.Shard000Part2.records ++
  PA215.IndexedContracts.Shard000Part3.records ++
  PA215.IndexedContracts.Shard000Part4.records ++
  PA215.IndexedContracts.Shard000Part5.records ++
  PA215.IndexedContracts.Shard000Part6.records ++
  PA215.IndexedContracts.Shard000Part7.records

theorem exact_ids : records.map (fun e => e.1.val) = [3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133] := by
  simp only [records, List.map_append, PA215.IndexedContracts.Shard000Part0.exact_ids, PA215.IndexedContracts.Shard000Part1.exact_ids, PA215.IndexedContracts.Shard000Part2.exact_ids, PA215.IndexedContracts.Shard000Part3.exact_ids, PA215.IndexedContracts.Shard000Part4.exact_ids, PA215.IndexedContracts.Shard000Part5.exact_ids, PA215.IndexedContracts.Shard000Part6.exact_ids, PA215.IndexedContracts.Shard000Part7.exact_ids]
  rfl

end PA215.IndexedContracts.Shard000
