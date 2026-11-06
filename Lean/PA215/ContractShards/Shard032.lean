import PA215.ContractShards.Shard032Part0
import PA215.ContractShards.Shard032Part1
import PA215.ContractShards.Shard032Part2
import PA215.ContractShards.Shard032Part3
import PA215.ContractShards.Shard032Part4
import PA215.ContractShards.Shard032Part5
import PA215.ContractShards.Shard032Part6
import PA215.ContractShards.Shard032Part7
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard032
open PA215.Contracts

def records : List Certified :=
  PA215.ContractShards.Shard032Part0.records ++
  PA215.ContractShards.Shard032Part1.records ++
  PA215.ContractShards.Shard032Part2.records ++
  PA215.ContractShards.Shard032Part3.records ++
  PA215.ContractShards.Shard032Part4.records ++
  PA215.ContractShards.Shard032Part5.records ++
  PA215.ContractShards.Shard032Part6.records ++
  PA215.ContractShards.Shard032Part7.records

def ids : List Nat := records.map Certified.id

theorem exact_ids : ids = [4102, 4103, 4104, 4105, 4106, 4107, 4108, 4109, 4110, 4111, 4112, 4113, 4114, 4115, 4116, 4117, 4118, 4119, 4120, 4121, 4122, 4123, 4124, 4125, 4126, 4127, 4128, 4129, 4130, 4131, 4132, 4133, 4134, 4135, 4136, 4137, 4138, 4139, 4140, 4141, 4142, 4143, 4144, 4145, 4146, 4147, 4148, 4149, 4150, 4151, 4152, 4153, 4154, 4155, 4156, 4157, 4158, 4159, 4160, 4161, 4162, 4163, 4164, 4165, 4166, 4167, 4168, 4169, 4170, 4171, 4172, 4173, 4174, 4175, 4176, 4177, 4178, 4179, 4180, 4181, 4182, 4183, 4184, 4185, 4186, 4187, 4188, 4189, 4190, 4191, 4192, 4193, 4194, 4195, 4196, 4197, 4198, 4199, 4200, 4201, 4202, 4203, 4204, 4205, 4206, 4207, 4208, 4209, 4210, 4211, 4212, 4213, 4214, 4215, 4216, 4217, 4218, 4219, 4220, 4221, 4222, 4223, 4224, 4225, 4226, 4227, 4228, 4229] := by decide
theorem count : records.length = 128 := by decide
theorem distinct_ids : ids.Nodup := by decide

end PA215.ContractShards.Shard032
