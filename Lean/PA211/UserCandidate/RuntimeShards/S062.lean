module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S062
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s3055_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3055_plain_checked : check 418 s3055_plain_contract = true := by decide +kernel
def s3055_plain : CertifiedContract :=
  ⟨3055, 3056, 0, (.inc 2), s3055_plain_contract, 418, s3055_plain_checked⟩

def s3056_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3056_plain_checked : check 116 s3056_plain_contract = true := by decide +kernel
def s3056_plain : CertifiedContract :=
  ⟨3056, 3054, 0, .none, s3056_plain_contract, 116, s3056_plain_checked⟩

def s3057_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s3057_plain_checked : check 119 s3057_plain_contract = true := by decide +kernel
def s3057_plain : CertifiedContract :=
  ⟨3057, 3048, 0, .none, s3057_plain_contract, 119, s3057_plain_checked⟩

def s3058_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, false, false] 0 .none⟩
theorem s3058_zero_checked : check 390 s3058_zero_contract = true := by decide +kernel
def s3058_zero : CertifiedContract :=
  ⟨3058, 3061, 0, .none, s3058_zero_contract, 390, s3058_zero_checked⟩

def s3058_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s3058_positive_checked : check 387 s3058_positive_contract = true := by decide +kernel
def s3058_positive : CertifiedContract :=
  ⟨3058, 3059, 1, (.dec 5), s3058_positive_contract, 387, s3058_positive_checked⟩

def s3059_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s3059_plain_checked : check 400 s3059_plain_contract = true := by decide +kernel
def s3059_plain : CertifiedContract :=
  ⟨3059, 3060, 0, (.inc 0), s3059_plain_contract, 400, s3059_plain_checked⟩

def s3060_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, false, true, true, true, false] 0 .none⟩
theorem s3060_plain_checked : check 107 s3060_plain_contract = true := by decide +kernel
def s3060_plain : CertifiedContract :=
  ⟨3060, 3058, 0, .none, s3060_plain_contract, 107, s3060_plain_checked⟩

def s3061_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, true, false] 0 .none⟩
theorem s3061_zero_checked : check 354 s3061_zero_contract = true := by decide +kernel
def s3061_zero : CertifiedContract :=
  ⟨3061, 3065, 0, .none, s3061_zero_contract, 354, s3061_zero_checked⟩

def s3061_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, false, true, false] 1 (.dec 4)⟩
theorem s3061_positive_checked : check 360 s3061_positive_contract = true := by decide +kernel
def s3061_positive : CertifiedContract :=
  ⟨3061, 3062, 1, (.dec 4), s3061_positive_contract, 360, s3061_positive_checked⟩

def s3062_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s3062_plain_checked : check 373 s3062_plain_contract = true := by decide +kernel
def s3062_plain : CertifiedContract :=
  ⟨3062, 3063, 0, (.inc 2), s3062_plain_contract, 373, s3062_plain_checked⟩

def s3063_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3063_plain_checked : check 400 s3063_plain_contract = true := by decide +kernel
def s3063_plain : CertifiedContract :=
  ⟨3063, 3064, 0, (.inc 8), s3063_plain_contract, 400, s3063_plain_checked⟩

def s3064_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, false, false] 0 .none⟩
theorem s3064_plain_checked : check 107 s3064_plain_contract = true := by decide +kernel
def s3064_plain : CertifiedContract :=
  ⟨3064, 3061, 0, .none, s3064_plain_contract, 107, s3064_plain_checked⟩

def s3065_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s3065_zero_checked : check 360 s3065_zero_contract = true := by decide +kernel
def s3065_zero : CertifiedContract :=
  ⟨3065, 3068, 0, .none, s3065_zero_contract, 360, s3065_zero_checked⟩

def s3065_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s3065_positive_checked : check 360 s3065_positive_contract = true := by decide +kernel
def s3065_positive : CertifiedContract :=
  ⟨3065, 3066, 1, (.dec 8), s3065_positive_contract, 360, s3065_positive_checked⟩

def s3066_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, true, true, true] 0 (.inc 4)⟩
theorem s3066_plain_checked : check 364 s3066_plain_contract = true := by decide +kernel
def s3066_plain : CertifiedContract :=
  ⟨3066, 3067, 0, (.inc 4), s3066_plain_contract, 364, s3066_plain_checked⟩

def s3067_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, true, false] 0 .none⟩
theorem s3067_plain_checked : check 98 s3067_plain_contract = true := by decide +kernel
def s3067_plain : CertifiedContract :=
  ⟨3067, 3065, 0, .none, s3067_plain_contract, 98, s3067_plain_checked⟩

def s3068_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, false, false] 0 .none⟩
theorem s3068_zero_checked : check 354 s3068_zero_contract = true := by decide +kernel
def s3068_zero : CertifiedContract :=
  ⟨3068, 3071, 0, .none, s3068_zero_contract, 354, s3068_zero_checked⟩

def s3068_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3068_positive_checked : check 360 s3068_positive_contract = true := by decide +kernel
def s3068_positive : CertifiedContract :=
  ⟨3068, 3069, 1, (.dec 2), s3068_positive_contract, 360, s3068_positive_checked⟩

def s3069_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s3069_plain_checked : check 373 s3069_plain_contract = true := by decide +kernel
def s3069_plain : CertifiedContract :=
  ⟨3069, 3070, 0, (.inc 8), s3069_plain_contract, 373, s3069_plain_checked⟩

def s3070_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s3070_plain_checked : check 98 s3070_plain_contract = true := by decide +kernel
def s3070_plain : CertifiedContract :=
  ⟨3070, 3068, 0, .none, s3070_plain_contract, 98, s3070_plain_checked⟩

def s3071_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s3071_zero_checked : check 375 s3071_zero_contract = true := by decide +kernel
def s3071_zero : CertifiedContract :=
  ⟨3071, 3074, 0, .none, s3071_zero_contract, 375, s3071_zero_checked⟩

def s3071_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s3071_positive_checked : check 381 s3071_positive_contract = true := by decide +kernel
def s3071_positive : CertifiedContract :=
  ⟨3071, 3072, 1, (.dec 0), s3071_positive_contract, 381, s3071_positive_checked⟩

def s3072_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s3072_plain_checked : check 373 s3072_plain_contract = true := by decide +kernel
def s3072_plain : CertifiedContract :=
  ⟨3072, 3073, 0, (.inc 2), s3072_plain_contract, 373, s3072_plain_checked⟩

def s3073_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, false, false] 0 .none⟩
theorem s3073_plain_checked : check 101 s3073_plain_contract = true := by decide +kernel
def s3073_plain : CertifiedContract :=
  ⟨3073, 3071, 0, .none, s3073_plain_contract, 101, s3073_plain_checked⟩

def s3074_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3074_zero_checked : check 381 s3074_zero_contract = true := by decide +kernel
def s3074_zero : CertifiedContract :=
  ⟨3074, 3078, 0, .none, s3074_zero_contract, 381, s3074_zero_checked⟩

def s3074_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3074_positive_checked : check 387 s3074_positive_contract = true := by decide +kernel
def s3074_positive : CertifiedContract :=
  ⟨3074, 3075, 1, (.dec 2), s3074_positive_contract, 387, s3074_positive_checked⟩

def s3075_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3075_plain_checked : check 400 s3075_plain_contract = true := by decide +kernel
def s3075_plain : CertifiedContract :=
  ⟨3075, 3076, 0, (.inc 5), s3075_plain_contract, 400, s3075_plain_checked⟩

def s3076_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3076_plain_checked : check 427 s3076_plain_contract = true := by decide +kernel
def s3076_plain : CertifiedContract :=
  ⟨3076, 3077, 0, (.inc 8), s3076_plain_contract, 427, s3076_plain_checked⟩

def s3077_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s3077_plain_checked : check 116 s3077_plain_contract = true := by decide +kernel
def s3077_plain : CertifiedContract :=
  ⟨3077, 3074, 0, .none, s3077_plain_contract, 116, s3077_plain_checked⟩

def s3078_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s3078_zero_checked : check 402 s3078_zero_contract = true := by decide +kernel
def s3078_zero : CertifiedContract :=
  ⟨3078, 3084, 0, .none, s3078_zero_contract, 402, s3078_zero_checked⟩

def s3078_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3078_positive_checked : check 405 s3078_positive_contract = true := by decide +kernel
def s3078_positive : CertifiedContract :=
  ⟨3078, 3079, 1, (.dec 8), s3078_positive_contract, 405, s3078_positive_checked⟩

def s3079_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3079_plain_checked : check 400 s3079_plain_contract = true := by decide +kernel
def s3079_plain : CertifiedContract :=
  ⟨3079, 3080, 0, (.inc 5), s3079_plain_contract, 400, s3079_plain_checked⟩

def s3080_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s3080_zero_checked : check 420 s3080_zero_contract = true := by decide +kernel
def s3080_zero : CertifiedContract :=
  ⟨3080, 3083, 0, .none, s3080_zero_contract, 420, s3080_zero_checked⟩

def s3080_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3080_positive_checked : check 423 s3080_positive_contract = true := by decide +kernel
def s3080_positive : CertifiedContract :=
  ⟨3080, 3081, 1, (.dec 8), s3080_positive_contract, 423, s3080_positive_checked⟩

def s3081_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3081_plain_checked : check 418 s3081_plain_contract = true := by decide +kernel
def s3081_plain : CertifiedContract :=
  ⟨3081, 3082, 0, (.inc 2), s3081_plain_contract, 418, s3081_plain_checked⟩

def s3082_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3082_plain_checked : check 116 s3082_plain_contract = true := by decide +kernel
def s3082_plain : CertifiedContract :=
  ⟨3082, 3080, 0, .none, s3082_plain_contract, 116, s3082_plain_checked⟩

def s3083_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s3083_plain_checked : check 119 s3083_plain_contract = true := by decide +kernel
def s3083_plain : CertifiedContract :=
  ⟨3083, 3074, 0, .none, s3083_plain_contract, 119, s3083_plain_checked⟩

def s3084_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, false, false] 0 .none⟩
theorem s3084_zero_checked : check 390 s3084_zero_contract = true := by decide +kernel
def s3084_zero : CertifiedContract :=
  ⟨3084, 3087, 0, .none, s3084_zero_contract, 390, s3084_zero_checked⟩

def s3084_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s3084_positive_checked : check 387 s3084_positive_contract = true := by decide +kernel
def s3084_positive : CertifiedContract :=
  ⟨3084, 3085, 1, (.dec 5), s3084_positive_contract, 387, s3084_positive_checked⟩

def s3085_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s3085_plain_checked : check 400 s3085_plain_contract = true := by decide +kernel
def s3085_plain : CertifiedContract :=
  ⟨3085, 3086, 0, (.inc 0), s3085_plain_contract, 400, s3085_plain_checked⟩

def s3086_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s3086_plain_checked : check 107 s3086_plain_contract = true := by decide +kernel
def s3086_plain : CertifiedContract :=
  ⟨3086, 3084, 0, .none, s3086_plain_contract, 107, s3086_plain_checked⟩

def s3087_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s3087_zero_checked : check 354 s3087_zero_contract = true := by decide +kernel
def s3087_zero : CertifiedContract :=
  ⟨3087, 3091, 0, .none, s3087_zero_contract, 354, s3087_zero_checked⟩

def s3087_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s3087_positive_checked : check 360 s3087_positive_contract = true := by decide +kernel
def s3087_positive : CertifiedContract :=
  ⟨3087, 3088, 1, (.dec 7), s3087_positive_contract, 360, s3087_positive_checked⟩

def s3088_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s3088_plain_checked : check 364 s3088_plain_contract = true := by decide +kernel
def s3088_plain : CertifiedContract :=
  ⟨3088, 3089, 0, (.inc 2), s3088_plain_contract, 364, s3088_plain_checked⟩

def s3089_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3089_plain_checked : check 391 s3089_plain_contract = true := by decide +kernel
def s3089_plain : CertifiedContract :=
  ⟨3089, 3090, 0, (.inc 8), s3089_plain_contract, 391, s3089_plain_checked⟩

def s3090_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, false, false] 0 .none⟩
theorem s3090_plain_checked : check 104 s3090_plain_contract = true := by decide +kernel
def s3090_plain : CertifiedContract :=
  ⟨3090, 3087, 0, .none, s3090_plain_contract, 104, s3090_plain_checked⟩

def s3091_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, false] 0 .none⟩
theorem s3091_zero_checked : check 363 s3091_zero_contract = true := by decide +kernel
def s3091_zero : CertifiedContract :=
  ⟨3091, 3094, 0, .none, s3091_zero_contract, 363, s3091_zero_checked⟩

def s3091_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s3091_positive_checked : check 360 s3091_positive_contract = true := by decide +kernel
def s3091_positive : CertifiedContract :=
  ⟨3091, 3092, 1, (.dec 8), s3091_positive_contract, 360, s3091_positive_checked⟩

def s3092_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s3092_plain_checked : check 391 s3092_plain_contract = true := by decide +kernel
def s3092_plain : CertifiedContract :=
  ⟨3092, 3093, 0, (.inc 7), s3092_plain_contract, 391, s3092_plain_checked⟩

def s3093_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s3093_plain_checked : check 98 s3093_plain_contract = true := by decide +kernel
def s3093_plain : CertifiedContract :=
  ⟨3093, 3091, 0, .none, s3093_plain_contract, 98, s3093_plain_checked⟩

def s3094_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, true, false] 0 .none⟩
theorem s3094_zero_checked : check 366 s3094_zero_contract = true := by decide +kernel
def s3094_zero : CertifiedContract :=
  ⟨3094, 3102, 0, .none, s3094_zero_contract, 366, s3094_zero_checked⟩

def s3094_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s3094_positive_checked : check 372 s3094_positive_contract = true := by decide +kernel
def s3094_positive : CertifiedContract :=
  ⟨3094, 3095, 1, (.dec 0), s3094_positive_contract, 372, s3094_positive_checked⟩

def s3095_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3095_plain_checked : check 382 s3095_plain_contract = true := by decide +kernel
def s3095_plain : CertifiedContract :=
  ⟨3095, 3096, 0, (.inc 5), s3095_plain_contract, 382, s3095_plain_checked⟩

def s3096_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3096_zero_checked : check 408 s3096_zero_contract = true := by decide +kernel
def s3096_zero : CertifiedContract :=
  ⟨3096, 3098, 0, .none, s3096_zero_contract, 408, s3096_zero_checked⟩

def s3096_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3096_positive_checked : check 414 s3096_positive_contract = true := by decide +kernel
def s3096_positive : CertifiedContract :=
  ⟨3096, 3097, 1, (.dec 8), s3096_positive_contract, 414, s3096_positive_checked⟩

def s3097_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s3097_plain_checked : check 113 s3097_plain_contract = true := by decide +kernel
def s3097_plain : CertifiedContract :=
  ⟨3097, 3101, 0, .none, s3097_plain_contract, 113, s3097_plain_checked⟩

def s3098_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s3098_zero_checked : check 420 s3098_zero_contract = true := by decide +kernel
def s3098_zero : CertifiedContract :=
  ⟨3098, 3101, 0, .none, s3098_zero_contract, 420, s3098_zero_checked⟩

def s3098_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3098_positive_checked : check 423 s3098_positive_contract = true := by decide +kernel
def s3098_positive : CertifiedContract :=
  ⟨3098, 3099, 1, (.dec 5), s3098_positive_contract, 423, s3098_positive_checked⟩

def s3099_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3099_plain_checked : check 427 s3099_plain_contract = true := by decide +kernel
def s3099_plain : CertifiedContract :=
  ⟨3099, 3100, 0, (.inc 8), s3099_plain_contract, 427, s3099_plain_checked⟩

def s3100_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3100_plain_checked : check 116 s3100_plain_contract = true := by decide +kernel
def s3100_plain : CertifiedContract :=
  ⟨3100, 3098, 0, .none, s3100_plain_contract, 116, s3100_plain_checked⟩

def s3101_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, false] 0 .none⟩
theorem s3101_plain_checked : check 107 s3101_plain_contract = true := by decide +kernel
def s3101_plain : CertifiedContract :=
  ⟨3101, 3094, 0, .none, s3101_plain_contract, 107, s3101_plain_checked⟩

def s3102_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s3102_zero_checked : check 366 s3102_zero_contract = true := by decide +kernel
def s3102_zero : CertifiedContract :=
  ⟨3102, 3105, 0, .none, s3102_zero_contract, 366, s3102_zero_checked⟩

def s3102_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s3102_positive_checked : check 369 s3102_positive_contract = true := by decide +kernel
def s3102_positive : CertifiedContract :=
  ⟨3102, 3103, 1, (.dec 5), s3102_positive_contract, 369, s3102_positive_checked⟩

def s3103_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s3103_plain_checked : check 382 s3103_plain_contract = true := by decide +kernel
def s3103_plain : CertifiedContract :=
  ⟨3103, 3104, 0, (.inc 0), s3103_plain_contract, 382, s3103_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S062
