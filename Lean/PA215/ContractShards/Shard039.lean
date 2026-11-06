import PA215.ContractShards.Shard039Part0
import PA215.ContractShards.Shard039Part1
import PA215.ContractShards.Shard039Part2
import PA215.ContractShards.Shard039Part3
import PA215.ContractShards.Shard039Part4
import PA215.ContractShards.Shard039Part5
import PA215.ContractShards.Shard039Part6
import PA215.ContractShards.Shard039Part7
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard039
open PA215.Contracts

def records : List Certified :=
  PA215.ContractShards.Shard039Part0.records ++
  PA215.ContractShards.Shard039Part1.records ++
  PA215.ContractShards.Shard039Part2.records ++
  PA215.ContractShards.Shard039Part3.records ++
  PA215.ContractShards.Shard039Part4.records ++
  PA215.ContractShards.Shard039Part5.records ++
  PA215.ContractShards.Shard039Part6.records ++
  PA215.ContractShards.Shard039Part7.records

def ids : List Nat := records.map Certified.id

theorem exact_ids : ids = [4999, 5000, 5001, 5002, 5003, 5004, 5005, 5006, 5007, 5008, 5009, 5010, 5011, 5012, 5013, 5014, 5015, 5016, 5017, 5018, 5019, 5020, 5021, 5022, 5023, 5024, 5025, 5026, 5027, 5028, 5029, 5030, 5031, 5032, 5033, 5034, 5035, 5036, 5037, 5038, 5039, 5040, 5041, 5042, 5043, 5044, 5045, 5046, 5047, 5048, 5049, 5050, 5051, 5052, 5053, 5054, 5055, 5056, 5057, 5058, 5059, 5060, 5061, 5062, 5063, 5064, 5065, 5066, 5067, 5068, 5069, 5070, 5071, 5072, 5073, 5074, 5075, 5076, 5077, 5078, 5079, 5080, 5081, 5082, 5083, 5089, 5090, 5091, 5092, 5093, 5094, 5095, 5096, 5097, 5098, 5099, 5100, 5101, 5102, 5103, 5104, 5105, 5106, 5107, 5108, 5109, 5110, 5111, 5112, 5113, 5115, 5116, 5117, 5118, 5119, 5120, 5121, 5122, 5123, 5124, 5125, 5126, 5127, 5128, 5129, 5130, 5131, 5132] := by decide
theorem count : records.length = 128 := by decide
theorem distinct_ids : ids.Nodup := by decide

end PA215.ContractShards.Shard039
