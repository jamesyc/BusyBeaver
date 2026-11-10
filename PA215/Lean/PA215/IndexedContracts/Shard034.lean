import PA215.IndexedContracts.Shard034Part0
import PA215.IndexedContracts.Shard034Part1
import PA215.IndexedContracts.Shard034Part2
import PA215.IndexedContracts.Shard034Part3
import PA215.IndexedContracts.Shard034Part4
import PA215.IndexedContracts.Shard034Part5
import PA215.IndexedContracts.Shard034Part6
import PA215.IndexedContracts.Shard034Part7
namespace PA215.IndexedContracts.Shard034
open PA215.Census
def records : OriginalRegistry :=
  PA215.IndexedContracts.Shard034Part0.records ++
  PA215.IndexedContracts.Shard034Part1.records ++
  PA215.IndexedContracts.Shard034Part2.records ++
  PA215.IndexedContracts.Shard034Part3.records ++
  PA215.IndexedContracts.Shard034Part4.records ++
  PA215.IndexedContracts.Shard034Part5.records ++
  PA215.IndexedContracts.Shard034Part6.records ++
  PA215.IndexedContracts.Shard034Part7.records

theorem exact_ids : records.map (fun e => e.1.val) = [4358, 4359, 4360, 4361, 4362, 4363, 4364, 4365, 4366, 4367, 4368, 4369, 4370, 4371, 4372, 4373, 4374, 4375, 4376, 4377, 4378, 4379, 4380, 4381, 4382, 4383, 4384, 4385, 4386, 4387, 4388, 4389, 4390, 4391, 4392, 4393, 4394, 4395, 4396, 4397, 4398, 4399, 4400, 4401, 4402, 4403, 4404, 4405, 4406, 4407, 4408, 4409, 4410, 4411, 4412, 4413, 4414, 4415, 4416, 4417, 4418, 4419, 4420, 4421, 4422, 4423, 4424, 4425, 4426, 4427, 4428, 4429, 4430, 4431, 4432, 4433, 4434, 4435, 4436, 4437, 4438, 4439, 4440, 4441, 4442, 4443, 4444, 4445, 4446, 4447, 4448, 4449, 4450, 4451, 4452, 4453, 4454, 4455, 4456, 4457, 4458, 4459, 4460, 4461, 4462, 4463, 4464, 4465, 4466, 4467, 4468, 4469, 4470, 4471, 4472, 4473, 4474, 4475, 4476, 4477, 4478, 4479, 4480, 4481, 4482, 4483, 4484, 4485] := by
  simp only [records, List.map_append, PA215.IndexedContracts.Shard034Part0.exact_ids, PA215.IndexedContracts.Shard034Part1.exact_ids, PA215.IndexedContracts.Shard034Part2.exact_ids, PA215.IndexedContracts.Shard034Part3.exact_ids, PA215.IndexedContracts.Shard034Part4.exact_ids, PA215.IndexedContracts.Shard034Part5.exact_ids, PA215.IndexedContracts.Shard034Part6.exact_ids, PA215.IndexedContracts.Shard034Part7.exact_ids]
  all_goals rfl

end PA215.IndexedContracts.Shard034
