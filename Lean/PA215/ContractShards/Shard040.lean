import PA215.ContractShards.Shard040Part0
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard040
open PA215.Contracts

def records : List Certified :=
  PA215.ContractShards.Shard040Part0.records

def ids : List Nat := records.map Certified.id

theorem exact_ids : ids = [5133] := by decide
theorem count : records.length = 1 := by decide
theorem distinct_ids : ids.Nodup := by decide

end PA215.ContractShards.Shard040
