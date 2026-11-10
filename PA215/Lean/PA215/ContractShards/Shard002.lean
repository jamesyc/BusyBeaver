import PA215.ContractShards.Shard002Part0
import PA215.ContractShards.Shard002Part1
import PA215.ContractShards.Shard002Part2
import PA215.ContractShards.Shard002Part3
import PA215.ContractShards.Shard002Part4
import PA215.ContractShards.Shard002Part5
import PA215.ContractShards.Shard002Part6
import PA215.ContractShards.Shard002Part7
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard002
open PA215.Contracts

def records : List Certified :=
  PA215.ContractShards.Shard002Part0.records ++
  PA215.ContractShards.Shard002Part1.records ++
  PA215.ContractShards.Shard002Part2.records ++
  PA215.ContractShards.Shard002Part3.records ++
  PA215.ContractShards.Shard002Part4.records ++
  PA215.ContractShards.Shard002Part5.records ++
  PA215.ContractShards.Shard002Part6.records ++
  PA215.ContractShards.Shard002Part7.records

def ids : List Nat := records.map Certified.id

theorem exact_ids : ids = [262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389] := by decide
theorem count : records.length = 128 := by decide
theorem distinct_ids : ids.Nodup := by decide

end PA215.ContractShards.Shard002
