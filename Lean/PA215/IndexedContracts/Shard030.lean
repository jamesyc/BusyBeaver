import PA215.IndexedContracts.Shard030Part0
import PA215.IndexedContracts.Shard030Part1
import PA215.IndexedContracts.Shard030Part2
import PA215.IndexedContracts.Shard030Part3
import PA215.IndexedContracts.Shard030Part4
import PA215.IndexedContracts.Shard030Part5
import PA215.IndexedContracts.Shard030Part6
import PA215.IndexedContracts.Shard030Part7
namespace PA215.IndexedContracts.Shard030
open PA215.Census
def records : OriginalRegistry :=
  PA215.IndexedContracts.Shard030Part0.records ++
  PA215.IndexedContracts.Shard030Part1.records ++
  PA215.IndexedContracts.Shard030Part2.records ++
  PA215.IndexedContracts.Shard030Part3.records ++
  PA215.IndexedContracts.Shard030Part4.records ++
  PA215.IndexedContracts.Shard030Part5.records ++
  PA215.IndexedContracts.Shard030Part6.records ++
  PA215.IndexedContracts.Shard030Part7.records

theorem exact_ids : records.map (fun e => e.1.val) = [3846, 3847, 3848, 3849, 3850, 3851, 3852, 3853, 3854, 3855, 3856, 3857, 3858, 3859, 3860, 3861, 3862, 3863, 3864, 3865, 3866, 3867, 3868, 3869, 3870, 3871, 3872, 3873, 3874, 3875, 3876, 3877, 3878, 3879, 3880, 3881, 3882, 3883, 3884, 3885, 3886, 3887, 3888, 3889, 3890, 3891, 3892, 3893, 3894, 3895, 3896, 3897, 3898, 3899, 3900, 3901, 3902, 3903, 3904, 3905, 3906, 3907, 3908, 3909, 3910, 3911, 3912, 3913, 3914, 3915, 3916, 3917, 3918, 3919, 3920, 3921, 3922, 3923, 3924, 3925, 3926, 3927, 3928, 3929, 3930, 3931, 3932, 3933, 3934, 3935, 3936, 3937, 3938, 3939, 3940, 3941, 3942, 3943, 3944, 3945, 3946, 3947, 3948, 3949, 3950, 3951, 3952, 3953, 3954, 3955, 3956, 3957, 3958, 3959, 3960, 3961, 3962, 3963, 3964, 3965, 3966, 3967, 3968, 3969, 3970, 3971, 3972, 3973] := by
  simp only [records, List.map_append, PA215.IndexedContracts.Shard030Part0.exact_ids, PA215.IndexedContracts.Shard030Part1.exact_ids, PA215.IndexedContracts.Shard030Part2.exact_ids, PA215.IndexedContracts.Shard030Part3.exact_ids, PA215.IndexedContracts.Shard030Part4.exact_ids, PA215.IndexedContracts.Shard030Part5.exact_ids, PA215.IndexedContracts.Shard030Part6.exact_ids, PA215.IndexedContracts.Shard030Part7.exact_ids]
  all_goals rfl

end PA215.IndexedContracts.Shard030
