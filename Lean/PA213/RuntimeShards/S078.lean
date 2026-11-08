import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S078
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s3841_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, true, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s3841_zero_checked : check 284 s3841_zero_contract = true := by decide +kernel
def s3841_zero : CertifiedContract :=
  ⟨3841, 3844, 0, .none, s3841_zero_contract, 284, s3841_zero_checked⟩

def s3841_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, true, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, true, true, true, false] 1 (.dec 8)⟩
theorem s3841_positive_checked : check 278 s3841_positive_contract = true := by decide +kernel
def s3841_positive : CertifiedContract :=
  ⟨3841, 3842, 1, (.dec 8), s3841_positive_contract, 278, s3841_positive_checked⟩

def s3842_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, true, true, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, true, true, true, true] 0 (.inc 3)⟩
theorem s3842_plain_checked : check 294 s3842_plain_contract = true := by decide +kernel
def s3842_plain : CertifiedContract :=
  ⟨3842, 3843, 0, (.inc 3), s3842_plain_contract, 294, s3842_plain_checked⟩

def s3843_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, true, true, true, true], rootFrame [true, false, true, false, true, false, false, false, true, true, true, true, false] 0 .none⟩
theorem s3843_plain_checked : check 70 s3843_plain_contract = true := by decide +kernel
def s3843_plain : CertifiedContract :=
  ⟨3843, 3841, 0, .none, s3843_plain_contract, 70, s3843_plain_checked⟩

def s3844_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, true, false, false, true, false, true, false] 0 .none⟩
theorem s3844_zero_checked : check 266 s3844_zero_contract = true := by decide +kernel
def s3844_zero : CertifiedContract :=
  ⟨3844, 3852, 0, .none, s3844_zero_contract, 266, s3844_zero_checked⟩

def s3844_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, true, false, false, true, false, false, true, false] 1 (.dec 0)⟩
theorem s3844_positive_checked : check 272 s3844_positive_contract = true := by decide +kernel
def s3844_positive : CertifiedContract :=
  ⟨3844, 3845, 1, (.dec 0), s3844_positive_contract, 272, s3844_positive_checked⟩

def s3845_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, true, false, false, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3845_plain_checked : check 282 s3845_plain_contract = true := by decide +kernel
def s3845_plain : CertifiedContract :=
  ⟨3845, 3846, 0, (.inc 5), s3845_plain_contract, 282, s3845_plain_checked⟩

def s3846_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, true, false, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, true, false, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3846_zero_checked : check 308 s3846_zero_contract = true := by decide +kernel
def s3846_zero : CertifiedContract :=
  ⟨3846, 3848, 0, .none, s3846_zero_contract, 308, s3846_zero_checked⟩

def s3846_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, true, false, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, true, false, false, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3846_positive_checked : check 314 s3846_positive_contract = true := by decide +kernel
def s3846_positive : CertifiedContract :=
  ⟨3846, 3847, 1, (.dec 8), s3846_positive_contract, 314, s3846_positive_checked⟩

def s3847_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, true, false, false, true, false, false, true, true, true] 0 .none⟩
theorem s3847_plain_checked : check 79 s3847_plain_contract = true := by decide +kernel
def s3847_plain : CertifiedContract :=
  ⟨3847, 3851, 0, .none, s3847_plain_contract, 79, s3847_plain_checked⟩

def s3848_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, true, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, true, false, false, true, true, true] 0 .none⟩
theorem s3848_zero_checked : check 320 s3848_zero_contract = true := by decide +kernel
def s3848_zero : CertifiedContract :=
  ⟨3848, 3851, 0, .none, s3848_zero_contract, 320, s3848_zero_checked⟩

def s3848_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, true, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3848_positive_checked : check 323 s3848_positive_contract = true := by decide +kernel
def s3848_positive : CertifiedContract :=
  ⟨3848, 3849, 1, (.dec 5), s3848_positive_contract, 323, s3848_positive_checked⟩

def s3849_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, true, false, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3849_plain_checked : check 327 s3849_plain_contract = true := by decide +kernel
def s3849_plain : CertifiedContract :=
  ⟨3849, 3850, 0, (.inc 8), s3849_plain_contract, 327, s3849_plain_checked⟩

def s3850_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, true, false, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3850_plain_checked : check 82 s3850_plain_contract = true := by decide +kernel
def s3850_plain : CertifiedContract :=
  ⟨3850, 3848, 0, .none, s3850_plain_contract, 82, s3850_plain_checked⟩

def s3851_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s3851_plain_checked : check 73 s3851_plain_contract = true := by decide +kernel
def s3851_plain : CertifiedContract :=
  ⟨3851, 3844, 0, .none, s3851_plain_contract, 73, s3851_plain_checked⟩

def s3852_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s3852_zero_checked : check 266 s3852_zero_contract = true := by decide +kernel
def s3852_zero : CertifiedContract :=
  ⟨3852, 3855, 0, .none, s3852_zero_contract, 266, s3852_zero_checked⟩

def s3852_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, true, false, false, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3852_positive_checked : check 269 s3852_positive_contract = true := by decide +kernel
def s3852_positive : CertifiedContract :=
  ⟨3852, 3853, 1, (.dec 5), s3852_positive_contract, 269, s3852_positive_checked⟩

def s3853_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, true, false, true, true, false], rootFrame [true, false, true, false, true, false, false, true, false, true, true, true] 0 (.inc 0)⟩
theorem s3853_plain_checked : check 282 s3853_plain_contract = true := by decide +kernel
def s3853_plain : CertifiedContract :=
  ⟨3853, 3854, 0, (.inc 0), s3853_plain_contract, 282, s3853_plain_checked⟩

def s3854_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, true, false, false, true, false, true, false] 0 .none⟩
theorem s3854_plain_checked : check 67 s3854_plain_contract = true := by decide +kernel
def s3854_plain : CertifiedContract :=
  ⟨3854, 3852, 0, .none, s3854_plain_contract, 67, s3854_plain_checked⟩

def s3855_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3855_zero_checked : check 263 s3855_zero_contract = true := by decide +kernel
def s3855_zero : CertifiedContract :=
  ⟨3855, 3859, 0, .none, s3855_zero_contract, 263, s3855_zero_checked⟩

def s3855_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, true, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3855_positive_checked : check 269 s3855_positive_contract = true := by decide +kernel
def s3855_positive : CertifiedContract :=
  ⟨3855, 3856, 1, (.dec 2), s3855_positive_contract, 269, s3855_positive_checked⟩

def s3856_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, true, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3856_plain_checked : check 282 s3856_plain_contract = true := by decide +kernel
def s3856_plain : CertifiedContract :=
  ⟨3856, 3857, 0, (.inc 5), s3856_plain_contract, 282, s3856_plain_checked⟩

def s3857_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, true, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3857_plain_checked : check 309 s3857_plain_contract = true := by decide +kernel
def s3857_plain : CertifiedContract :=
  ⟨3857, 3858, 0, (.inc 8), s3857_plain_contract, 309, s3857_plain_checked⟩

def s3858_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s3858_plain_checked : check 76 s3858_plain_contract = true := by decide +kernel
def s3858_plain : CertifiedContract :=
  ⟨3858, 3855, 0, .none, s3858_plain_contract, 76, s3858_plain_checked⟩

def s3859_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s3859_zero_checked : check 284 s3859_zero_contract = true := by decide +kernel
def s3859_zero : CertifiedContract :=
  ⟨3859, 3865, 0, .none, s3859_zero_contract, 284, s3859_zero_checked⟩

def s3859_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3859_positive_checked : check 287 s3859_positive_contract = true := by decide +kernel
def s3859_positive : CertifiedContract :=
  ⟨3859, 3860, 1, (.dec 8), s3859_positive_contract, 287, s3859_positive_checked⟩

def s3860_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, true, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3860_plain_checked : check 282 s3860_plain_contract = true := by decide +kernel
def s3860_plain : CertifiedContract :=
  ⟨3860, 3861, 0, (.inc 5), s3860_plain_contract, 282, s3860_plain_checked⟩

def s3861_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s3861_zero_checked : check 302 s3861_zero_contract = true := by decide +kernel
def s3861_zero : CertifiedContract :=
  ⟨3861, 3864, 0, .none, s3861_zero_contract, 302, s3861_zero_checked⟩

def s3861_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3861_positive_checked : check 305 s3861_positive_contract = true := by decide +kernel
def s3861_positive : CertifiedContract :=
  ⟨3861, 3862, 1, (.dec 8), s3861_positive_contract, 305, s3861_positive_checked⟩

def s3862_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, true, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3862_plain_checked : check 300 s3862_plain_contract = true := by decide +kernel
def s3862_plain : CertifiedContract :=
  ⟨3862, 3863, 0, (.inc 2), s3862_plain_contract, 300, s3862_plain_checked⟩

def s3863_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, true, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3863_plain_checked : check 76 s3863_plain_contract = true := by decide +kernel
def s3863_plain : CertifiedContract :=
  ⟨3863, 3861, 0, .none, s3863_plain_contract, 76, s3863_plain_checked⟩

def s3864_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s3864_plain_checked : check 79 s3864_plain_contract = true := by decide +kernel
def s3864_plain : CertifiedContract :=
  ⟨3864, 3855, 0, .none, s3864_plain_contract, 79, s3864_plain_checked⟩

def s3865_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, true, false, true, false] 0 .none⟩
theorem s3865_zero_checked : check 272 s3865_zero_contract = true := by decide +kernel
def s3865_zero : CertifiedContract :=
  ⟨3865, 3871, 0, .none, s3865_zero_contract, 272, s3865_zero_checked⟩

def s3865_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, true, false, false, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3865_positive_checked : check 269 s3865_positive_contract = true := by decide +kernel
def s3865_positive : CertifiedContract :=
  ⟨3865, 3866, 1, (.dec 5), s3865_positive_contract, 269, s3865_positive_checked⟩

def s3866_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, true, false, false, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3866_plain_checked : check 282 s3866_plain_contract = true := by decide +kernel
def s3866_plain : CertifiedContract :=
  ⟨3866, 3867, 0, (.inc 2), s3866_plain_contract, 282, s3866_plain_checked⟩

def s3867_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, true, true, true, true, false, false, true], rootFrame [true, false, true, false, true, false, false, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3867_plain_checked : check 285 s3867_plain_contract = true := by decide +kernel
def s3867_plain : CertifiedContract :=
  ⟨3867, 3868, 0, (.inc 2), s3867_plain_contract, 285, s3867_plain_checked⟩

def s3868_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3868_plain_checked : check 282 s3868_plain_contract = true := by decide +kernel
def s3868_plain : CertifiedContract :=
  ⟨3868, 3869, 0, (.inc 2), s3868_plain_contract, 282, s3868_plain_checked⟩

def s3869_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, true, true, true, true, false, true, true], rootFrame [true, false, true, false, true, false, false, true, true, true, true, true] 0 (.inc 2)⟩
theorem s3869_plain_checked : check 288 s3869_plain_contract = true := by decide +kernel
def s3869_plain : CertifiedContract :=
  ⟨3869, 3870, 0, (.inc 2), s3869_plain_contract, 288, s3869_plain_checked⟩

def s3870_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s3870_plain_checked : check 64 s3870_plain_contract = true := by decide +kernel
def s3870_plain : CertifiedContract :=
  ⟨3870, 3865, 0, .none, s3870_plain_contract, 64, s3870_plain_checked⟩

def s3871_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, true, true, false, false, false, false] 0 .none⟩
theorem s3871_zero_checked : check 230 s3871_zero_contract = true := by decide +kernel
def s3871_zero : CertifiedContract :=
  ⟨3871, 3874, 0, .none, s3871_zero_contract, 230, s3871_zero_checked⟩

def s3871_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, true, false, true, true, false] 1 (.dec 2)⟩
theorem s3871_positive_checked : check 233 s3871_positive_contract = true := by decide +kernel
def s3871_positive : CertifiedContract :=
  ⟨3871, 3872, 1, (.dec 2), s3871_positive_contract, 233, s3871_positive_checked⟩

def s3872_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3872_plain_checked : check 246 s3872_plain_contract = true := by decide +kernel
def s3872_plain : CertifiedContract :=
  ⟨3872, 3873, 0, (.inc 8), s3872_plain_contract, 246, s3872_plain_checked⟩

def s3873_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, true, false, true, false] 0 .none⟩
theorem s3873_plain_checked : check 55 s3873_plain_contract = true := by decide +kernel
def s3873_plain : CertifiedContract :=
  ⟨3873, 3871, 0, .none, s3873_plain_contract, 55, s3873_plain_checked⟩

def s3874_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, true, true, false, false, false, false], rootFrame [true, false, true, false, true, true, false, false, true] 0 .none⟩
theorem s3874_zero_checked : check 254 s3874_zero_contract = true := by decide +kernel
def s3874_zero : CertifiedContract :=
  ⟨3874, 3878, 0, .none, s3874_zero_contract, 254, s3874_zero_checked⟩

def s3874_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, true, true, false, false, false, false], rootFrame [true, false, true, false, true, true, false, false, false, true, false, false] 1 (.dec 7)⟩
theorem s3874_positive_checked : check 260 s3874_positive_contract = true := by decide +kernel
def s3874_positive : CertifiedContract :=
  ⟨3874, 3875, 1, (.dec 7), s3874_positive_contract, 260, s3874_positive_checked⟩

def s3875_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, true, true, false, false, false, true, true] 0 .none⟩
theorem s3875_zero_checked : check 272 s3875_zero_contract = true := by decide +kernel
def s3875_zero : CertifiedContract :=
  ⟨3875, 3877, 0, .none, s3875_zero_contract, 272, s3875_zero_checked⟩

def s3875_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, true, true, false, false, false, true, false, true] 1 (.dec 8)⟩
theorem s3875_positive_checked : check 278 s3875_positive_contract = true := by decide +kernel
def s3875_positive : CertifiedContract :=
  ⟨3875, 3876, 1, (.dec 8), s3875_positive_contract, 278, s3875_positive_checked⟩

def s3876_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, false, false, false, true, false, true], rootFrame [true, false, true, false, true, true, false, false, false, false] 0 .none⟩
theorem s3876_plain_checked : check 67 s3876_plain_contract = true := by decide +kernel
def s3876_plain : CertifiedContract :=
  ⟨3876, 3874, 0, .none, s3876_plain_contract, 67, s3876_plain_checked⟩

def s3877_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, false, false, false, true, true], rootFrame [true, false, true, false, true, true, false, true, false, false] 0 .none⟩
theorem s3877_plain_checked : check 81 s3877_plain_contract = true := by decide +kernel
def s3877_plain : CertifiedContract :=
  ⟨3877, 3879, 0, .none, s3877_plain_contract, 81, s3877_plain_checked⟩

def s3878_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, true, true, false, false, true], rootFrame [true, false, true, false, true, true, true, false, false, false] 0 .none⟩
theorem s3878_zero_checked : check 248 s3878_zero_contract = true := by decide +kernel
def s3878_zero : CertifiedContract :=
  ⟨3878, 3884, 0, .none, s3878_zero_contract, 248, s3878_zero_checked⟩

def s3878_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, true, true, false, false, true], rootFrame [true, false, true, false, true, true, false, true, false, false] 1 (.dec 8)⟩
theorem s3878_positive_checked : check 254 s3878_positive_contract = true := by decide +kernel
def s3878_positive : CertifiedContract :=
  ⟨3878, 3879, 1, (.dec 8), s3878_positive_contract, 254, s3878_positive_checked⟩

def s3879_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, true, true, false, true, false, false], rootFrame [true, false, true, false, true, true, false, true, true, false, false] 0 .none⟩
theorem s3879_zero_checked : check 263 s3879_zero_contract = true := by decide +kernel
def s3879_zero : CertifiedContract :=
  ⟨3879, 3881, 0, .none, s3879_zero_contract, 263, s3879_zero_checked⟩

def s3879_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, true, true, false, true, false, false], rootFrame [true, false, true, false, true, true, false, true, false, true] 1 (.dec 7)⟩
theorem s3879_positive_checked : check 269 s3879_positive_contract = true := by decide +kernel
def s3879_positive : CertifiedContract :=
  ⟨3879, 3880, 1, (.dec 7), s3879_positive_contract, 269, s3879_positive_checked⟩

def s3880_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, false, true, false, true], rootFrame [true, false, true, false, true, true, false, true, false, false] 0 .none⟩
theorem s3880_plain_checked : check 61 s3880_plain_contract = true := by decide +kernel
def s3880_plain : CertifiedContract :=
  ⟨3880, 3879, 0, .none, s3880_plain_contract, 61, s3880_plain_checked⟩

def s3881_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s3881_zero_checked : check 263 s3881_zero_contract = true := by decide +kernel
def s3881_zero : CertifiedContract :=
  ⟨3881, 3883, 0, .none, s3881_zero_contract, 263, s3881_zero_checked⟩

def s3881_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, true, true, false, true, true, false, true] 1 (.dec 8)⟩
theorem s3881_positive_checked : check 269 s3881_positive_contract = true := by decide +kernel
def s3881_positive : CertifiedContract :=
  ⟨3881, 3882, 1, (.dec 8), s3881_positive_contract, 269, s3881_positive_checked⟩

def s3882_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, false, true, true, false, true], rootFrame [true, false, true, false, true, true, false, true, false, false] 0 .none⟩
theorem s3882_plain_checked : check 64 s3882_plain_contract = true := by decide +kernel
def s3882_plain : CertifiedContract :=
  ⟨3882, 3879, 0, .none, s3882_plain_contract, 64, s3882_plain_checked⟩

def s3883_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, true] 0 .none⟩
theorem s3883_plain_checked : check 87 s3883_plain_contract = true := by decide +kernel
def s3883_plain : CertifiedContract :=
  ⟨3883, 3910, 0, .none, s3883_plain_contract, 87, s3883_plain_checked⟩

def s3884_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, true, true, true, false, true, false, false] 0 .none⟩
theorem s3884_zero_checked : check 245 s3884_zero_contract = true := by decide +kernel
def s3884_zero : CertifiedContract :=
  ⟨3884, 3887, 0, .none, s3884_zero_contract, 245, s3884_zero_checked⟩

def s3884_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, true, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3884_positive_checked : check 251 s3884_positive_contract = true := by decide +kernel
def s3884_positive : CertifiedContract :=
  ⟨3884, 3885, 1, (.dec 2), s3884_positive_contract, 251, s3884_positive_checked⟩

def s3885_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, true, false, false, true, false], rootFrame [true, false, true, false, true, true, true, false, false, true, true] 0 (.inc 8)⟩
theorem s3885_plain_checked : check 264 s3885_plain_contract = true := by decide +kernel
def s3885_plain : CertifiedContract :=
  ⟨3885, 3886, 0, (.inc 8), s3885_plain_contract, 264, s3885_plain_checked⟩

def s3886_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, true, false, false, true, true], rootFrame [true, false, true, false, true, true, true, false, false, false] 0 .none⟩
theorem s3886_plain_checked : check 61 s3886_plain_contract = true := by decide +kernel
def s3886_plain : CertifiedContract :=
  ⟨3886, 3884, 0, .none, s3886_plain_contract, 61, s3886_plain_checked⟩

def s3887_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, true, true, true, false, true, false, false], rootFrame [true, false, true, false, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s3887_zero_checked : check 266 s3887_zero_contract = true := by decide +kernel
def s3887_zero : CertifiedContract :=
  ⟨3887, 3890, 0, .none, s3887_zero_contract, 266, s3887_zero_checked⟩

def s3887_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, true, true, true, false, true, false, false], rootFrame [true, false, true, false, true, true, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s3887_positive_checked : check 272 s3887_positive_contract = true := by decide +kernel
def s3887_positive : CertifiedContract :=
  ⟨3887, 3888, 1, (.dec 0), s3887_positive_contract, 272, s3887_positive_checked⟩

def nonterminal : Array CertifiedContract := #[
  s3841_zero,
  s3841_positive,
  s3842_plain,
  s3843_plain,
  s3844_zero,
  s3844_positive,
  s3845_plain,
  s3846_zero,
  s3846_positive,
  s3847_plain,
  s3848_zero,
  s3848_positive,
  s3849_plain,
  s3850_plain,
  s3851_plain,
  s3852_zero,
  s3852_positive,
  s3853_plain,
  s3854_plain,
  s3855_zero,
  s3855_positive,
  s3856_plain,
  s3857_plain,
  s3858_plain,
  s3859_zero,
  s3859_positive,
  s3860_plain,
  s3861_zero,
  s3861_positive,
  s3862_plain,
  s3863_plain,
  s3864_plain,
  s3865_zero,
  s3865_positive,
  s3866_plain,
  s3867_plain,
  s3868_plain,
  s3869_plain,
  s3870_plain,
  s3871_zero,
  s3871_positive,
  s3872_plain,
  s3873_plain,
  s3874_zero,
  s3874_positive,
  s3875_zero,
  s3875_positive,
  s3876_plain,
  s3877_plain,
  s3878_zero,
  s3878_positive,
  s3879_zero,
  s3879_positive,
  s3880_plain,
  s3881_zero,
  s3881_positive,
  s3882_plain,
  s3883_plain,
  s3884_zero,
  s3884_positive,
  s3885_plain,
  s3886_plain,
  s3887_zero,
  s3887_positive
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S078
