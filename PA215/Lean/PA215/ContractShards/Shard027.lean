import PA215.ContractShards.Shard027Part0
import PA215.ContractShards.Shard027Part1
import PA215.ContractShards.Shard027Part2
import PA215.ContractShards.Shard027Part3
import PA215.ContractShards.Shard027Part4
import PA215.ContractShards.Shard027Part5
import PA215.ContractShards.Shard027Part6
import PA215.ContractShards.Shard027Part7
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard027
open PA215.Contracts

def records : List Certified :=
  PA215.ContractShards.Shard027Part0.records ++
  PA215.ContractShards.Shard027Part1.records ++
  PA215.ContractShards.Shard027Part2.records ++
  PA215.ContractShards.Shard027Part3.records ++
  PA215.ContractShards.Shard027Part4.records ++
  PA215.ContractShards.Shard027Part5.records ++
  PA215.ContractShards.Shard027Part6.records ++
  PA215.ContractShards.Shard027Part7.records

def ids : List Nat := records.map Certified.id

theorem exact_ids : ids = [3462, 3463, 3464, 3465, 3466, 3467, 3468, 3469, 3470, 3471, 3472, 3473, 3474, 3475, 3476, 3477, 3478, 3479, 3480, 3481, 3482, 3483, 3484, 3485, 3486, 3487, 3488, 3489, 3490, 3491, 3492, 3493, 3494, 3495, 3496, 3497, 3498, 3499, 3500, 3501, 3502, 3503, 3504, 3505, 3506, 3507, 3508, 3509, 3510, 3511, 3512, 3513, 3514, 3515, 3516, 3517, 3518, 3519, 3520, 3521, 3522, 3523, 3524, 3525, 3526, 3527, 3528, 3529, 3530, 3531, 3532, 3533, 3534, 3535, 3536, 3537, 3538, 3539, 3540, 3541, 3542, 3543, 3544, 3545, 3546, 3547, 3548, 3549, 3550, 3551, 3552, 3553, 3554, 3555, 3556, 3557, 3558, 3559, 3560, 3561, 3562, 3563, 3564, 3565, 3566, 3567, 3568, 3569, 3570, 3571, 3572, 3573, 3574, 3575, 3576, 3577, 3578, 3579, 3580, 3581, 3582, 3583, 3584, 3585, 3586, 3587, 3588, 3589] := by decide
theorem count : records.length = 128 := by decide
theorem distinct_ids : ids.Nodup := by decide

end PA215.ContractShards.Shard027
