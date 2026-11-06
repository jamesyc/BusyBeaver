import PA215.ContractShards.Shard036Part0
import PA215.ContractShards.Shard036Part1
import PA215.ContractShards.Shard036Part2
import PA215.ContractShards.Shard036Part3
import PA215.ContractShards.Shard036Part4
import PA215.ContractShards.Shard036Part5
import PA215.ContractShards.Shard036Part6
import PA215.ContractShards.Shard036Part7
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard036
open PA215.Contracts

def records : List Certified :=
  PA215.ContractShards.Shard036Part0.records ++
  PA215.ContractShards.Shard036Part1.records ++
  PA215.ContractShards.Shard036Part2.records ++
  PA215.ContractShards.Shard036Part3.records ++
  PA215.ContractShards.Shard036Part4.records ++
  PA215.ContractShards.Shard036Part5.records ++
  PA215.ContractShards.Shard036Part6.records ++
  PA215.ContractShards.Shard036Part7.records

def ids : List Nat := records.map Certified.id

theorem exact_ids : ids = [4614, 4615, 4616, 4617, 4618, 4619, 4620, 4621, 4622, 4623, 4624, 4625, 4626, 4627, 4628, 4629, 4630, 4631, 4632, 4633, 4634, 4635, 4636, 4637, 4638, 4639, 4640, 4641, 4642, 4643, 4644, 4645, 4646, 4647, 4648, 4649, 4650, 4651, 4652, 4653, 4654, 4655, 4656, 4657, 4658, 4659, 4660, 4661, 4662, 4663, 4664, 4665, 4666, 4667, 4668, 4669, 4670, 4671, 4672, 4673, 4674, 4675, 4676, 4677, 4678, 4679, 4680, 4681, 4682, 4683, 4684, 4685, 4686, 4687, 4688, 4689, 4690, 4691, 4692, 4693, 4694, 4695, 4696, 4697, 4698, 4699, 4700, 4701, 4702, 4703, 4704, 4705, 4706, 4707, 4708, 4709, 4710, 4711, 4712, 4713, 4714, 4715, 4716, 4717, 4718, 4719, 4720, 4721, 4722, 4723, 4724, 4725, 4726, 4727, 4728, 4729, 4730, 4731, 4732, 4733, 4734, 4735, 4736, 4737, 4738, 4739, 4740, 4741] := by decide
theorem count : records.length = 128 := by decide
theorem distinct_ids : ids.Nodup := by decide

end PA215.ContractShards.Shard036
