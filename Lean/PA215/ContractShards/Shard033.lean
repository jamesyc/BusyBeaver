import PA215.ContractShards.Shard033Part0
import PA215.ContractShards.Shard033Part1
import PA215.ContractShards.Shard033Part2
import PA215.ContractShards.Shard033Part3
import PA215.ContractShards.Shard033Part4
import PA215.ContractShards.Shard033Part5
import PA215.ContractShards.Shard033Part6
import PA215.ContractShards.Shard033Part7
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard033
open PA215.Contracts

def records : List Certified :=
  PA215.ContractShards.Shard033Part0.records ++
  PA215.ContractShards.Shard033Part1.records ++
  PA215.ContractShards.Shard033Part2.records ++
  PA215.ContractShards.Shard033Part3.records ++
  PA215.ContractShards.Shard033Part4.records ++
  PA215.ContractShards.Shard033Part5.records ++
  PA215.ContractShards.Shard033Part6.records ++
  PA215.ContractShards.Shard033Part7.records

def ids : List Nat := records.map Certified.id

theorem exact_ids : ids = [4230, 4231, 4232, 4233, 4234, 4235, 4236, 4237, 4238, 4239, 4240, 4241, 4242, 4243, 4244, 4245, 4246, 4247, 4248, 4249, 4250, 4251, 4252, 4253, 4254, 4255, 4256, 4257, 4258, 4259, 4260, 4261, 4262, 4263, 4264, 4265, 4266, 4267, 4268, 4269, 4270, 4271, 4272, 4273, 4274, 4275, 4276, 4277, 4278, 4279, 4280, 4281, 4282, 4283, 4284, 4285, 4286, 4287, 4288, 4289, 4290, 4291, 4292, 4293, 4294, 4295, 4296, 4297, 4298, 4299, 4300, 4301, 4302, 4303, 4304, 4305, 4306, 4307, 4308, 4309, 4310, 4311, 4312, 4313, 4314, 4315, 4316, 4317, 4318, 4319, 4320, 4321, 4322, 4323, 4324, 4325, 4326, 4327, 4328, 4329, 4330, 4331, 4332, 4333, 4334, 4335, 4336, 4337, 4338, 4339, 4340, 4341, 4342, 4343, 4344, 4345, 4346, 4347, 4348, 4349, 4350, 4351, 4352, 4353, 4354, 4355, 4356, 4357] := by decide
theorem count : records.length = 128 := by decide
theorem distinct_ids : ids.Nodup := by decide

end PA215.ContractShards.Shard033
