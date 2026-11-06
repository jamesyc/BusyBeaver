import PA215.ContractShards.Shard029Part0
import PA215.ContractShards.Shard029Part1
import PA215.ContractShards.Shard029Part2
import PA215.ContractShards.Shard029Part3
import PA215.ContractShards.Shard029Part4
import PA215.ContractShards.Shard029Part5
import PA215.ContractShards.Shard029Part6
import PA215.ContractShards.Shard029Part7
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard029
open PA215.Contracts

def records : List Certified :=
  PA215.ContractShards.Shard029Part0.records ++
  PA215.ContractShards.Shard029Part1.records ++
  PA215.ContractShards.Shard029Part2.records ++
  PA215.ContractShards.Shard029Part3.records ++
  PA215.ContractShards.Shard029Part4.records ++
  PA215.ContractShards.Shard029Part5.records ++
  PA215.ContractShards.Shard029Part6.records ++
  PA215.ContractShards.Shard029Part7.records

def ids : List Nat := records.map Certified.id

theorem exact_ids : ids = [3718, 3719, 3720, 3721, 3722, 3723, 3724, 3725, 3726, 3727, 3728, 3729, 3730, 3731, 3732, 3733, 3734, 3735, 3736, 3737, 3738, 3739, 3740, 3741, 3742, 3743, 3744, 3745, 3746, 3747, 3748, 3749, 3750, 3751, 3752, 3753, 3754, 3755, 3756, 3757, 3758, 3759, 3760, 3761, 3762, 3763, 3764, 3765, 3766, 3767, 3768, 3769, 3770, 3771, 3772, 3773, 3774, 3775, 3776, 3777, 3778, 3779, 3780, 3781, 3782, 3783, 3784, 3785, 3786, 3787, 3788, 3789, 3790, 3791, 3792, 3793, 3794, 3795, 3796, 3797, 3798, 3799, 3800, 3801, 3802, 3803, 3804, 3805, 3806, 3807, 3808, 3809, 3810, 3811, 3812, 3813, 3814, 3815, 3816, 3817, 3818, 3819, 3820, 3821, 3822, 3823, 3824, 3825, 3826, 3827, 3828, 3829, 3830, 3831, 3832, 3833, 3834, 3835, 3836, 3837, 3838, 3839, 3840, 3841, 3842, 3843, 3844, 3845] := by decide
theorem count : records.length = 128 := by decide
theorem distinct_ids : ids.Nodup := by decide

end PA215.ContractShards.Shard029
