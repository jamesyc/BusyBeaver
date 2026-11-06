import PA215.IndexedContracts.Shard031Part0
import PA215.IndexedContracts.Shard031Part1
import PA215.IndexedContracts.Shard031Part2
import PA215.IndexedContracts.Shard031Part3
import PA215.IndexedContracts.Shard031Part4
import PA215.IndexedContracts.Shard031Part5
import PA215.IndexedContracts.Shard031Part6
import PA215.IndexedContracts.Shard031Part7
namespace PA215.IndexedContracts.Shard031
open PA215.Census
def records : OriginalRegistry :=
  PA215.IndexedContracts.Shard031Part0.records ++
  PA215.IndexedContracts.Shard031Part1.records ++
  PA215.IndexedContracts.Shard031Part2.records ++
  PA215.IndexedContracts.Shard031Part3.records ++
  PA215.IndexedContracts.Shard031Part4.records ++
  PA215.IndexedContracts.Shard031Part5.records ++
  PA215.IndexedContracts.Shard031Part6.records ++
  PA215.IndexedContracts.Shard031Part7.records

theorem exact_ids : records.map (fun e => e.1.val) = [3974, 3975, 3976, 3977, 3978, 3979, 3980, 3981, 3982, 3983, 3984, 3985, 3986, 3987, 3988, 3989, 3990, 3991, 3992, 3993, 3994, 3995, 3996, 3997, 3998, 3999, 4000, 4001, 4002, 4003, 4004, 4005, 4006, 4007, 4008, 4009, 4010, 4011, 4012, 4013, 4014, 4015, 4016, 4017, 4018, 4019, 4020, 4021, 4022, 4023, 4024, 4025, 4026, 4027, 4028, 4029, 4030, 4031, 4032, 4033, 4034, 4035, 4036, 4037, 4038, 4039, 4040, 4041, 4042, 4043, 4044, 4045, 4046, 4047, 4048, 4049, 4050, 4051, 4052, 4053, 4054, 4055, 4056, 4057, 4058, 4059, 4060, 4061, 4062, 4063, 4064, 4065, 4066, 4067, 4068, 4069, 4070, 4071, 4072, 4073, 4074, 4075, 4076, 4077, 4078, 4079, 4080, 4081, 4082, 4083, 4084, 4085, 4086, 4087, 4088, 4089, 4090, 4091, 4092, 4093, 4094, 4095, 4096, 4097, 4098, 4099, 4100, 4101] := by
  simp only [records, List.map_append, PA215.IndexedContracts.Shard031Part0.exact_ids, PA215.IndexedContracts.Shard031Part1.exact_ids, PA215.IndexedContracts.Shard031Part2.exact_ids, PA215.IndexedContracts.Shard031Part3.exact_ids, PA215.IndexedContracts.Shard031Part4.exact_ids, PA215.IndexedContracts.Shard031Part5.exact_ids, PA215.IndexedContracts.Shard031Part6.exact_ids, PA215.IndexedContracts.Shard031Part7.exact_ids]
  all_goals rfl

end PA215.IndexedContracts.Shard031
