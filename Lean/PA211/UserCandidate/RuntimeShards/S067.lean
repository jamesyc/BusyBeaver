import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S067
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s3301_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3301_plain_checked : check 107 s3301_plain_contract = true := by decide +kernel
def s3301_plain : CertifiedContract :=
  ⟨3301, 3299, 0, .none, s3301_plain_contract, 107, s3301_plain_checked⟩

def s3302_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s3302_plain_checked : check 110 s3302_plain_contract = true := by decide +kernel
def s3302_plain : CertifiedContract :=
  ⟨3302, 3293, 0, .none, s3302_plain_contract, 110, s3302_plain_checked⟩

def s3303_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s3303_zero_checked : check 360 s3303_zero_contract = true := by decide +kernel
def s3303_zero : CertifiedContract :=
  ⟨3303, 3309, 0, .none, s3303_zero_contract, 360, s3303_zero_checked⟩

def s3303_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3303_positive_checked : check 360 s3303_positive_contract = true := by decide +kernel
def s3303_positive : CertifiedContract :=
  ⟨3303, 3304, 1, (.dec 5), s3303_positive_contract, 360, s3303_positive_checked⟩

def s3304_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3304_plain_checked : check 373 s3304_plain_contract = true := by decide +kernel
def s3304_plain : CertifiedContract :=
  ⟨3304, 3305, 0, (.inc 2), s3304_plain_contract, 373, s3304_plain_checked⟩

def s3305_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3305_plain_checked : check 376 s3305_plain_contract = true := by decide +kernel
def s3305_plain : CertifiedContract :=
  ⟨3305, 3306, 0, (.inc 2), s3305_plain_contract, 376, s3305_plain_checked⟩

def s3306_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3306_plain_checked : check 382 s3306_plain_contract = true := by decide +kernel
def s3306_plain : CertifiedContract :=
  ⟨3306, 3307, 0, (.inc 2), s3306_plain_contract, 382, s3306_plain_checked⟩

def s3307_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s3307_plain_checked : check 388 s3307_plain_contract = true := by decide +kernel
def s3307_plain : CertifiedContract :=
  ⟨3307, 3308, 0, (.inc 2), s3307_plain_contract, 388, s3307_plain_checked⟩

def s3308_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, true, false] 0 .none⟩
theorem s3308_plain_checked : check 95 s3308_plain_contract = true := by decide +kernel
def s3308_plain : CertifiedContract :=
  ⟨3308, 3303, 0, .none, s3308_plain_contract, 95, s3308_plain_checked⟩

def s3309_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, false, false] 0 .none⟩
theorem s3309_zero_checked : check 363 s3309_zero_contract = true := by decide +kernel
def s3309_zero : CertifiedContract :=
  ⟨3309, 3312, 0, .none, s3309_zero_contract, 363, s3309_zero_checked⟩

def s3309_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, false, true, false] 1 (.dec 2)⟩
theorem s3309_positive_checked : check 369 s3309_positive_contract = true := by decide +kernel
def s3309_positive : CertifiedContract :=
  ⟨3309, 3310, 1, (.dec 2), s3309_positive_contract, 369, s3309_positive_checked⟩

def s3310_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, false, true, true] 0 (.inc 8)⟩
theorem s3310_plain_checked : check 382 s3310_plain_contract = true := by decide +kernel
def s3310_plain : CertifiedContract :=
  ⟨3310, 3311, 0, (.inc 8), s3310_plain_contract, 382, s3310_plain_checked⟩

def s3311_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s3311_plain_checked : check 101 s3311_plain_contract = true := by decide +kernel
def s3311_plain : CertifiedContract :=
  ⟨3311, 3309, 0, .none, s3311_plain_contract, 101, s3311_plain_checked⟩

def s3312_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s3312_zero_checked : check 384 s3312_zero_contract = true := by decide +kernel
def s3312_zero : CertifiedContract :=
  ⟨3312, 3315, 0, .none, s3312_zero_contract, 384, s3312_zero_checked⟩

def s3312_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s3312_positive_checked : check 390 s3312_positive_contract = true := by decide +kernel
def s3312_positive : CertifiedContract :=
  ⟨3312, 3313, 1, (.dec 0), s3312_positive_contract, 390, s3312_positive_checked⟩

def s3313_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s3313_plain_checked : check 382 s3313_plain_contract = true := by decide +kernel
def s3313_plain : CertifiedContract :=
  ⟨3313, 3314, 0, (.inc 2), s3313_plain_contract, 382, s3313_plain_checked⟩

def s3314_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, false, false] 0 .none⟩
theorem s3314_plain_checked : check 104 s3314_plain_contract = true := by decide +kernel
def s3314_plain : CertifiedContract :=
  ⟨3314, 3312, 0, .none, s3314_plain_contract, 104, s3314_plain_checked⟩

def s3315_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3315_zero_checked : check 390 s3315_zero_contract = true := by decide +kernel
def s3315_zero : CertifiedContract :=
  ⟨3315, 3319, 0, .none, s3315_zero_contract, 390, s3315_zero_checked⟩

def s3315_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3315_positive_checked : check 396 s3315_positive_contract = true := by decide +kernel
def s3315_positive : CertifiedContract :=
  ⟨3315, 3316, 1, (.dec 2), s3315_positive_contract, 396, s3315_positive_checked⟩

def s3316_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3316_plain_checked : check 409 s3316_plain_contract = true := by decide +kernel
def s3316_plain : CertifiedContract :=
  ⟨3316, 3317, 0, (.inc 5), s3316_plain_contract, 409, s3316_plain_checked⟩

def s3317_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3317_plain_checked : check 436 s3317_plain_contract = true := by decide +kernel
def s3317_plain : CertifiedContract :=
  ⟨3317, 3318, 0, (.inc 8), s3317_plain_contract, 436, s3317_plain_checked⟩

def s3318_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s3318_plain_checked : check 119 s3318_plain_contract = true := by decide +kernel
def s3318_plain : CertifiedContract :=
  ⟨3318, 3315, 0, .none, s3318_plain_contract, 119, s3318_plain_checked⟩

def s3319_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s3319_zero_checked : check 411 s3319_zero_contract = true := by decide +kernel
def s3319_zero : CertifiedContract :=
  ⟨3319, 3325, 0, .none, s3319_zero_contract, 411, s3319_zero_checked⟩

def s3319_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3319_positive_checked : check 414 s3319_positive_contract = true := by decide +kernel
def s3319_positive : CertifiedContract :=
  ⟨3319, 3320, 1, (.dec 8), s3319_positive_contract, 414, s3319_positive_checked⟩

def s3320_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3320_plain_checked : check 409 s3320_plain_contract = true := by decide +kernel
def s3320_plain : CertifiedContract :=
  ⟨3320, 3321, 0, (.inc 5), s3320_plain_contract, 409, s3320_plain_checked⟩

def s3321_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s3321_zero_checked : check 429 s3321_zero_contract = true := by decide +kernel
def s3321_zero : CertifiedContract :=
  ⟨3321, 3324, 0, .none, s3321_zero_contract, 429, s3321_zero_checked⟩

def s3321_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3321_positive_checked : check 432 s3321_positive_contract = true := by decide +kernel
def s3321_positive : CertifiedContract :=
  ⟨3321, 3322, 1, (.dec 8), s3321_positive_contract, 432, s3321_positive_checked⟩

def s3322_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3322_plain_checked : check 427 s3322_plain_contract = true := by decide +kernel
def s3322_plain : CertifiedContract :=
  ⟨3322, 3323, 0, (.inc 2), s3322_plain_contract, 427, s3322_plain_checked⟩

def s3323_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3323_plain_checked : check 119 s3323_plain_contract = true := by decide +kernel
def s3323_plain : CertifiedContract :=
  ⟨3323, 3321, 0, .none, s3323_plain_contract, 119, s3323_plain_checked⟩

def s3324_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s3324_plain_checked : check 122 s3324_plain_contract = true := by decide +kernel
def s3324_plain : CertifiedContract :=
  ⟨3324, 3315, 0, .none, s3324_plain_contract, 122, s3324_plain_checked⟩

def s3325_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, true] 0 .none⟩
theorem s3325_zero_checked : check 399 s3325_zero_contract = true := by decide +kernel
def s3325_zero : CertifiedContract :=
  ⟨3325, 3328, 0, .none, s3325_zero_contract, 399, s3325_zero_checked⟩

def s3325_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s3325_positive_checked : check 396 s3325_positive_contract = true := by decide +kernel
def s3325_positive : CertifiedContract :=
  ⟨3325, 3326, 1, (.dec 5), s3325_positive_contract, 396, s3325_positive_checked⟩

def s3326_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s3326_plain_checked : check 409 s3326_plain_contract = true := by decide +kernel
def s3326_plain : CertifiedContract :=
  ⟨3326, 3327, 0, (.inc 0), s3326_plain_contract, 409, s3326_plain_checked⟩

def s3327_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s3327_plain_checked : check 110 s3327_plain_contract = true := by decide +kernel
def s3327_plain : CertifiedContract :=
  ⟨3327, 3325, 0, .none, s3327_plain_contract, 110, s3327_plain_checked⟩

def s3328_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, false] 0 (.inc 2)⟩
theorem s3328_plain_checked : check 349 s3328_plain_contract = true := by decide +kernel
def s3328_plain : CertifiedContract :=
  ⟨3328, 3329, 0, (.inc 2), s3328_plain_contract, 349, s3328_plain_checked⟩

def s3329_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3329_zero_checked : check 366 s3329_zero_contract = true := by decide +kernel
def s3329_zero : CertifiedContract :=
  ⟨3329, 3337, 0, .none, s3329_zero_contract, 366, s3329_zero_checked⟩

def s3329_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 0)⟩
theorem s3329_positive_checked : check 372 s3329_positive_contract = true := by decide +kernel
def s3329_positive : CertifiedContract :=
  ⟨3329, 3330, 1, (.dec 0), s3329_positive_contract, 372, s3329_positive_checked⟩

def s3330_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3330_plain_checked : check 382 s3330_plain_contract = true := by decide +kernel
def s3330_plain : CertifiedContract :=
  ⟨3330, 3331, 0, (.inc 5), s3330_plain_contract, 382, s3330_plain_checked⟩

def s3331_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3331_zero_checked : check 408 s3331_zero_contract = true := by decide +kernel
def s3331_zero : CertifiedContract :=
  ⟨3331, 3333, 0, .none, s3331_zero_contract, 408, s3331_zero_checked⟩

def s3331_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3331_positive_checked : check 414 s3331_positive_contract = true := by decide +kernel
def s3331_positive : CertifiedContract :=
  ⟨3331, 3332, 1, (.dec 8), s3331_positive_contract, 414, s3331_positive_checked⟩

def s3332_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, true, true, true] 0 .none⟩
theorem s3332_plain_checked : check 113 s3332_plain_contract = true := by decide +kernel
def s3332_plain : CertifiedContract :=
  ⟨3332, 3336, 0, .none, s3332_plain_contract, 113, s3332_plain_checked⟩

def s3333_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, true, true, true] 0 .none⟩
theorem s3333_zero_checked : check 420 s3333_zero_contract = true := by decide +kernel
def s3333_zero : CertifiedContract :=
  ⟨3333, 3336, 0, .none, s3333_zero_contract, 420, s3333_zero_checked⟩

def s3333_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3333_positive_checked : check 423 s3333_positive_contract = true := by decide +kernel
def s3333_positive : CertifiedContract :=
  ⟨3333, 3334, 1, (.dec 5), s3333_positive_contract, 423, s3333_positive_checked⟩

def s3334_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3334_plain_checked : check 427 s3334_plain_contract = true := by decide +kernel
def s3334_plain : CertifiedContract :=
  ⟨3334, 3335, 0, (.inc 8), s3334_plain_contract, 427, s3334_plain_checked⟩

def s3335_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3335_plain_checked : check 116 s3335_plain_contract = true := by decide +kernel
def s3335_plain : CertifiedContract :=
  ⟨3335, 3333, 0, .none, s3335_plain_contract, 116, s3335_plain_checked⟩

def s3336_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s3336_plain_checked : check 107 s3336_plain_contract = true := by decide +kernel
def s3336_plain : CertifiedContract :=
  ⟨3336, 3329, 0, .none, s3336_plain_contract, 107, s3336_plain_checked⟩

def s3337_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, false] 0 .none⟩
theorem s3337_zero_checked : check 366 s3337_zero_contract = true := by decide +kernel
def s3337_zero : CertifiedContract :=
  ⟨3337, 3340, 0, .none, s3337_zero_contract, 366, s3337_zero_checked⟩

def s3337_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3337_positive_checked : check 369 s3337_positive_contract = true := by decide +kernel
def s3337_positive : CertifiedContract :=
  ⟨3337, 3338, 1, (.dec 5), s3337_positive_contract, 369, s3337_positive_checked⟩

def s3338_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, true, true, true] 0 (.inc 0)⟩
theorem s3338_plain_checked : check 382 s3338_plain_contract = true := by decide +kernel
def s3338_plain : CertifiedContract :=
  ⟨3338, 3339, 0, (.inc 0), s3338_plain_contract, 382, s3338_plain_checked⟩

def s3339_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3339_plain_checked : check 101 s3339_plain_contract = true := by decide +kernel
def s3339_plain : CertifiedContract :=
  ⟨3339, 3337, 0, .none, s3339_plain_contract, 101, s3339_plain_checked⟩

def s3340_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, true, false] 0 .none⟩
theorem s3340_zero_checked : check 363 s3340_zero_contract = true := by decide +kernel
def s3340_zero : CertifiedContract :=
  ⟨3340, 3344, 0, .none, s3340_zero_contract, 363, s3340_zero_checked⟩

def s3340_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3340_positive_checked : check 369 s3340_positive_contract = true := by decide +kernel
def s3340_positive : CertifiedContract :=
  ⟨3340, 3341, 1, (.dec 2), s3340_positive_contract, 369, s3340_positive_checked⟩

def s3341_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3341_plain_checked : check 382 s3341_plain_contract = true := by decide +kernel
def s3341_plain : CertifiedContract :=
  ⟨3341, 3342, 0, (.inc 5), s3341_plain_contract, 382, s3341_plain_checked⟩

def s3342_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3342_plain_checked : check 409 s3342_plain_contract = true := by decide +kernel
def s3342_plain : CertifiedContract :=
  ⟨3342, 3343, 0, (.inc 8), s3342_plain_contract, 409, s3342_plain_checked⟩

def s3343_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, false] 0 .none⟩
theorem s3343_plain_checked : check 110 s3343_plain_contract = true := by decide +kernel
def s3343_plain : CertifiedContract :=
  ⟨3343, 3340, 0, .none, s3343_plain_contract, 110, s3343_plain_checked⟩

def s3344_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, true, false] 0 .none⟩
theorem s3344_zero_checked : check 384 s3344_zero_contract = true := by decide +kernel
def s3344_zero : CertifiedContract :=
  ⟨3344, 3350, 0, .none, s3344_zero_contract, 384, s3344_zero_checked⟩

def s3344_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3344_positive_checked : check 387 s3344_positive_contract = true := by decide +kernel
def s3344_positive : CertifiedContract :=
  ⟨3344, 3345, 1, (.dec 8), s3344_positive_contract, 387, s3344_positive_checked⟩

def s3345_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3345_plain_checked : check 382 s3345_plain_contract = true := by decide +kernel
def s3345_plain : CertifiedContract :=
  ⟨3345, 3346, 0, (.inc 5), s3345_plain_contract, 382, s3345_plain_checked⟩

def s3346_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, true, true, true] 0 .none⟩
theorem s3346_zero_checked : check 402 s3346_zero_contract = true := by decide +kernel
def s3346_zero : CertifiedContract :=
  ⟨3346, 3349, 0, .none, s3346_zero_contract, 402, s3346_zero_checked⟩

def s3346_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3346_positive_checked : check 405 s3346_positive_contract = true := by decide +kernel
def s3346_positive : CertifiedContract :=
  ⟨3346, 3347, 1, (.dec 8), s3346_positive_contract, 405, s3346_positive_checked⟩

def s3347_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3347_plain_checked : check 400 s3347_plain_contract = true := by decide +kernel
def s3347_plain : CertifiedContract :=
  ⟨3347, 3348, 0, (.inc 2), s3347_plain_contract, 400, s3347_plain_checked⟩

def s3348_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3348_plain_checked : check 110 s3348_plain_contract = true := by decide +kernel
def s3348_plain : CertifiedContract :=
  ⟨3348, 3346, 0, .none, s3348_plain_contract, 110, s3348_plain_checked⟩

def s3349_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, false, false, false] 0 .none⟩
theorem s3349_plain_checked : check 113 s3349_plain_contract = true := by decide +kernel
def s3349_plain : CertifiedContract :=
  ⟨3349, 3340, 0, .none, s3349_plain_contract, 113, s3349_plain_checked⟩

def s3350_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, false] 0 .none⟩
theorem s3350_zero_checked : check 375 s3350_zero_contract = true := by decide +kernel
def s3350_zero : CertifiedContract :=
  ⟨3350, 3356, 0, .none, s3350_zero_contract, 375, s3350_zero_checked⟩

end PA211.UserCandidate.RuntimeShards.S067
