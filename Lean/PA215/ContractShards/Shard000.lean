import PA215.ContractShards.Shard000Part0
import PA215.ContractShards.Shard000Part1
import PA215.ContractShards.Shard000Part2
import PA215.ContractShards.Shard000Part3
import PA215.ContractShards.Shard000Part4
import PA215.ContractShards.Shard000Part5
import PA215.ContractShards.Shard000Part6
import PA215.ContractShards.Shard000Part7

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard000
open PA215.Contracts

def records : List Certified :=
  PA215.ContractShards.Shard000Part0.records ++
  PA215.ContractShards.Shard000Part1.records ++
  PA215.ContractShards.Shard000Part2.records ++
  PA215.ContractShards.Shard000Part3.records ++
  PA215.ContractShards.Shard000Part4.records ++
  PA215.ContractShards.Shard000Part5.records ++
  PA215.ContractShards.Shard000Part6.records ++
  PA215.ContractShards.Shard000Part7.records

def ids : List Nat := records.map Certified.id

theorem exact_ids : ids = [3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133] := by decide
theorem count : records.length = 128 := by decide
theorem distinct_ids : ids.Nodup := by decide

end PA215.ContractShards.Shard000
