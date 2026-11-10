import PA215.ContractShards.Shard003Part0
import PA215.ContractShards.Shard003Part1
import PA215.ContractShards.Shard003Part2
import PA215.ContractShards.Shard003Part3
import PA215.ContractShards.Shard003Part4
import PA215.ContractShards.Shard003Part5
import PA215.ContractShards.Shard003Part6
import PA215.ContractShards.Shard003Part7
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard003
open PA215.Contracts

def records : List Certified :=
  PA215.ContractShards.Shard003Part0.records ++
  PA215.ContractShards.Shard003Part1.records ++
  PA215.ContractShards.Shard003Part2.records ++
  PA215.ContractShards.Shard003Part3.records ++
  PA215.ContractShards.Shard003Part4.records ++
  PA215.ContractShards.Shard003Part5.records ++
  PA215.ContractShards.Shard003Part6.records ++
  PA215.ContractShards.Shard003Part7.records

def ids : List Nat := records.map Certified.id

theorem exact_ids : ids = [390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517] := by decide
theorem count : records.length = 128 := by decide
theorem distinct_ids : ids.Nodup := by decide

end PA215.ContractShards.Shard003
