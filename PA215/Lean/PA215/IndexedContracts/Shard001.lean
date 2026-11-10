import PA215.IndexedContracts.Shard001Part0
import PA215.IndexedContracts.Shard001Part1
import PA215.IndexedContracts.Shard001Part2
import PA215.IndexedContracts.Shard001Part3
import PA215.IndexedContracts.Shard001Part4
import PA215.IndexedContracts.Shard001Part5
import PA215.IndexedContracts.Shard001Part6
import PA215.IndexedContracts.Shard001Part7
namespace PA215.IndexedContracts.Shard001
open PA215.Census
def records : OriginalRegistry :=
  PA215.IndexedContracts.Shard001Part0.records ++
  PA215.IndexedContracts.Shard001Part1.records ++
  PA215.IndexedContracts.Shard001Part2.records ++
  PA215.IndexedContracts.Shard001Part3.records ++
  PA215.IndexedContracts.Shard001Part4.records ++
  PA215.IndexedContracts.Shard001Part5.records ++
  PA215.IndexedContracts.Shard001Part6.records ++
  PA215.IndexedContracts.Shard001Part7.records

theorem exact_ids : records.map (fun e => e.1.val) = [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261] := by
  simp only [records, List.map_append, PA215.IndexedContracts.Shard001Part0.exact_ids, PA215.IndexedContracts.Shard001Part1.exact_ids, PA215.IndexedContracts.Shard001Part2.exact_ids, PA215.IndexedContracts.Shard001Part3.exact_ids, PA215.IndexedContracts.Shard001Part4.exact_ids, PA215.IndexedContracts.Shard001Part5.exact_ids, PA215.IndexedContracts.Shard001Part6.exact_ids, PA215.IndexedContracts.Shard001Part7.exact_ids]
  rfl

end PA215.IndexedContracts.Shard001
