import PA215.IndexedContracts.Shard040Part0
namespace PA215.IndexedContracts.Shard040
open PA215.Census
def records : OriginalRegistry :=
  PA215.IndexedContracts.Shard040Part0.records

theorem exact_ids : records.map (fun e => e.1.val) = [5133] := by
  simp only [records, List.map_append, PA215.IndexedContracts.Shard040Part0.exact_ids]
  all_goals rfl

end PA215.IndexedContracts.Shard040
