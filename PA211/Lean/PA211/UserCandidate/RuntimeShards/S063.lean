import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S063
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s3104_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, true, false] 0 .none⟩
theorem s3104_plain_checked : check 101 s3104_plain_contract = true := by decide +kernel
def s3104_plain : CertifiedContract :=
  ⟨3104, 3102, 0, .none, s3104_plain_contract, 101, s3104_plain_checked⟩

def s3105_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, true, false] 0 .none⟩
theorem s3105_zero_checked : check 363 s3105_zero_contract = true := by decide +kernel
def s3105_zero : CertifiedContract :=
  ⟨3105, 3109, 0, .none, s3105_zero_contract, 363, s3105_zero_checked⟩

def s3105_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3105_positive_checked : check 369 s3105_positive_contract = true := by decide +kernel
def s3105_positive : CertifiedContract :=
  ⟨3105, 3106, 1, (.dec 2), s3105_positive_contract, 369, s3105_positive_checked⟩

def s3106_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3106_plain_checked : check 382 s3106_plain_contract = true := by decide +kernel
def s3106_plain : CertifiedContract :=
  ⟨3106, 3107, 0, (.inc 5), s3106_plain_contract, 382, s3106_plain_checked⟩

def s3107_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3107_plain_checked : check 409 s3107_plain_contract = true := by decide +kernel
def s3107_plain : CertifiedContract :=
  ⟨3107, 3108, 0, (.inc 8), s3107_plain_contract, 409, s3107_plain_checked⟩

def s3108_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s3108_plain_checked : check 110 s3108_plain_contract = true := by decide +kernel
def s3108_plain : CertifiedContract :=
  ⟨3108, 3105, 0, .none, s3108_plain_contract, 110, s3108_plain_checked⟩

def s3109_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false] 0 .none⟩
theorem s3109_zero_checked : check 384 s3109_zero_contract = true := by decide +kernel
def s3109_zero : CertifiedContract :=
  ⟨3109, 3115, 0, .none, s3109_zero_contract, 384, s3109_zero_checked⟩

def s3109_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3109_positive_checked : check 387 s3109_positive_contract = true := by decide +kernel
def s3109_positive : CertifiedContract :=
  ⟨3109, 3110, 1, (.dec 8), s3109_positive_contract, 387, s3109_positive_checked⟩

def s3110_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3110_plain_checked : check 382 s3110_plain_contract = true := by decide +kernel
def s3110_plain : CertifiedContract :=
  ⟨3110, 3111, 0, (.inc 5), s3110_plain_contract, 382, s3110_plain_checked⟩

def s3111_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, true, true, true] 0 .none⟩
theorem s3111_zero_checked : check 402 s3111_zero_contract = true := by decide +kernel
def s3111_zero : CertifiedContract :=
  ⟨3111, 3114, 0, .none, s3111_zero_contract, 402, s3111_zero_checked⟩

def s3111_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3111_positive_checked : check 405 s3111_positive_contract = true := by decide +kernel
def s3111_positive : CertifiedContract :=
  ⟨3111, 3112, 1, (.dec 8), s3111_positive_contract, 405, s3111_positive_checked⟩

def s3112_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3112_plain_checked : check 400 s3112_plain_contract = true := by decide +kernel
def s3112_plain : CertifiedContract :=
  ⟨3112, 3113, 0, (.inc 2), s3112_plain_contract, 400, s3112_plain_checked⟩

def s3113_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3113_plain_checked : check 110 s3113_plain_contract = true := by decide +kernel
def s3113_plain : CertifiedContract :=
  ⟨3113, 3111, 0, .none, s3113_plain_contract, 110, s3113_plain_checked⟩

def s3114_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s3114_plain_checked : check 113 s3114_plain_contract = true := by decide +kernel
def s3114_plain : CertifiedContract :=
  ⟨3114, 3105, 0, .none, s3114_plain_contract, 113, s3114_plain_checked⟩

def s3115_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s3115_zero_checked : check 369 s3115_zero_contract = true := by decide +kernel
def s3115_zero : CertifiedContract :=
  ⟨3115, 3121, 0, .none, s3115_zero_contract, 369, s3115_zero_checked⟩

def s3115_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3115_positive_checked : check 369 s3115_positive_contract = true := by decide +kernel
def s3115_positive : CertifiedContract :=
  ⟨3115, 3116, 1, (.dec 5), s3115_positive_contract, 369, s3115_positive_checked⟩

def s3116_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3116_plain_checked : check 382 s3116_plain_contract = true := by decide +kernel
def s3116_plain : CertifiedContract :=
  ⟨3116, 3117, 0, (.inc 2), s3116_plain_contract, 382, s3116_plain_checked⟩

def s3117_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3117_plain_checked : check 385 s3117_plain_contract = true := by decide +kernel
def s3117_plain : CertifiedContract :=
  ⟨3117, 3118, 0, (.inc 2), s3117_plain_contract, 385, s3117_plain_checked⟩

def s3118_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3118_plain_checked : check 391 s3118_plain_contract = true := by decide +kernel
def s3118_plain : CertifiedContract :=
  ⟨3118, 3119, 0, (.inc 2), s3118_plain_contract, 391, s3118_plain_checked⟩

def s3119_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s3119_plain_checked : check 397 s3119_plain_contract = true := by decide +kernel
def s3119_plain : CertifiedContract :=
  ⟨3119, 3120, 0, (.inc 2), s3119_plain_contract, 397, s3119_plain_checked⟩

def s3120_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false] 0 .none⟩
theorem s3120_plain_checked : check 98 s3120_plain_contract = true := by decide +kernel
def s3120_plain : CertifiedContract :=
  ⟨3120, 3115, 0, .none, s3120_plain_contract, 98, s3120_plain_checked⟩

def s3121_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, false] 0 (.inc 2)⟩
theorem s3121_plain_checked : check 346 s3121_plain_contract = true := by decide +kernel
def s3121_plain : CertifiedContract :=
  ⟨3121, 3122, 0, (.inc 2), s3121_plain_contract, 346, s3121_plain_checked⟩

def s3122_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, true, false] 0 .none⟩
theorem s3122_zero_checked : check 357 s3122_zero_contract = true := by decide +kernel
def s3122_zero : CertifiedContract :=
  ⟨3122, 3130, 0, .none, s3122_zero_contract, 357, s3122_zero_checked⟩

def s3122_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s3122_positive_checked : check 363 s3122_positive_contract = true := by decide +kernel
def s3122_positive : CertifiedContract :=
  ⟨3122, 3123, 1, (.dec 0), s3122_positive_contract, 363, s3122_positive_checked⟩

def s3123_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3123_plain_checked : check 373 s3123_plain_contract = true := by decide +kernel
def s3123_plain : CertifiedContract :=
  ⟨3123, 3124, 0, (.inc 5), s3123_plain_contract, 373, s3123_plain_checked⟩

def s3124_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3124_zero_checked : check 399 s3124_zero_contract = true := by decide +kernel
def s3124_zero : CertifiedContract :=
  ⟨3124, 3126, 0, .none, s3124_zero_contract, 399, s3124_zero_checked⟩

def s3124_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3124_positive_checked : check 405 s3124_positive_contract = true := by decide +kernel
def s3124_positive : CertifiedContract :=
  ⟨3124, 3125, 1, (.dec 8), s3124_positive_contract, 405, s3124_positive_checked⟩

def s3125_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s3125_plain_checked : check 110 s3125_plain_contract = true := by decide +kernel
def s3125_plain : CertifiedContract :=
  ⟨3125, 3129, 0, .none, s3125_plain_contract, 110, s3125_plain_checked⟩

def s3126_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s3126_zero_checked : check 411 s3126_zero_contract = true := by decide +kernel
def s3126_zero : CertifiedContract :=
  ⟨3126, 3129, 0, .none, s3126_zero_contract, 411, s3126_zero_checked⟩

def s3126_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3126_positive_checked : check 414 s3126_positive_contract = true := by decide +kernel
def s3126_positive : CertifiedContract :=
  ⟨3126, 3127, 1, (.dec 5), s3126_positive_contract, 414, s3126_positive_checked⟩

def s3127_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3127_plain_checked : check 418 s3127_plain_contract = true := by decide +kernel
def s3127_plain : CertifiedContract :=
  ⟨3127, 3128, 0, (.inc 8), s3127_plain_contract, 418, s3127_plain_checked⟩

def s3128_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3128_plain_checked : check 113 s3128_plain_contract = true := by decide +kernel
def s3128_plain : CertifiedContract :=
  ⟨3128, 3126, 0, .none, s3128_plain_contract, 113, s3128_plain_checked⟩

def s3129_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, false] 0 .none⟩
theorem s3129_plain_checked : check 104 s3129_plain_contract = true := by decide +kernel
def s3129_plain : CertifiedContract :=
  ⟨3129, 3122, 0, .none, s3129_plain_contract, 104, s3129_plain_checked⟩

def s3130_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s3130_zero_checked : check 357 s3130_zero_contract = true := by decide +kernel
def s3130_zero : CertifiedContract :=
  ⟨3130, 3133, 0, .none, s3130_zero_contract, 357, s3130_zero_checked⟩

def s3130_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s3130_positive_checked : check 360 s3130_positive_contract = true := by decide +kernel
def s3130_positive : CertifiedContract :=
  ⟨3130, 3131, 1, (.dec 5), s3130_positive_contract, 360, s3130_positive_checked⟩

def s3131_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s3131_plain_checked : check 373 s3131_plain_contract = true := by decide +kernel
def s3131_plain : CertifiedContract :=
  ⟨3131, 3132, 0, (.inc 0), s3131_plain_contract, 373, s3131_plain_checked⟩

def s3132_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, true, false] 0 .none⟩
theorem s3132_plain_checked : check 98 s3132_plain_contract = true := by decide +kernel
def s3132_plain : CertifiedContract :=
  ⟨3132, 3130, 0, .none, s3132_plain_contract, 98, s3132_plain_checked⟩

def s3133_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, false] 0 .none⟩
theorem s3133_zero_checked : check 354 s3133_zero_contract = true := by decide +kernel
def s3133_zero : CertifiedContract :=
  ⟨3133, 3137, 0, .none, s3133_zero_contract, 354, s3133_zero_checked⟩

def s3133_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3133_positive_checked : check 360 s3133_positive_contract = true := by decide +kernel
def s3133_positive : CertifiedContract :=
  ⟨3133, 3134, 1, (.dec 2), s3133_positive_contract, 360, s3133_positive_checked⟩

def s3134_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3134_plain_checked : check 373 s3134_plain_contract = true := by decide +kernel
def s3134_plain : CertifiedContract :=
  ⟨3134, 3135, 0, (.inc 5), s3134_plain_contract, 373, s3134_plain_checked⟩

def s3135_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3135_plain_checked : check 400 s3135_plain_contract = true := by decide +kernel
def s3135_plain : CertifiedContract :=
  ⟨3135, 3136, 0, (.inc 8), s3135_plain_contract, 400, s3135_plain_checked⟩

def s3136_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s3136_plain_checked : check 107 s3136_plain_contract = true := by decide +kernel
def s3136_plain : CertifiedContract :=
  ⟨3136, 3133, 0, .none, s3136_plain_contract, 107, s3136_plain_checked⟩

def s3137_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, false] 0 .none⟩
theorem s3137_zero_checked : check 375 s3137_zero_contract = true := by decide +kernel
def s3137_zero : CertifiedContract :=
  ⟨3137, 3143, 0, .none, s3137_zero_contract, 375, s3137_zero_checked⟩

def s3137_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3137_positive_checked : check 378 s3137_positive_contract = true := by decide +kernel
def s3137_positive : CertifiedContract :=
  ⟨3137, 3138, 1, (.dec 8), s3137_positive_contract, 378, s3137_positive_checked⟩

def s3138_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3138_plain_checked : check 373 s3138_plain_contract = true := by decide +kernel
def s3138_plain : CertifiedContract :=
  ⟨3138, 3139, 0, (.inc 5), s3138_plain_contract, 373, s3138_plain_checked⟩

def s3139_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, true] 0 .none⟩
theorem s3139_zero_checked : check 393 s3139_zero_contract = true := by decide +kernel
def s3139_zero : CertifiedContract :=
  ⟨3139, 3142, 0, .none, s3139_zero_contract, 393, s3139_zero_checked⟩

def s3139_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3139_positive_checked : check 396 s3139_positive_contract = true := by decide +kernel
def s3139_positive : CertifiedContract :=
  ⟨3139, 3140, 1, (.dec 8), s3139_positive_contract, 396, s3139_positive_checked⟩

def s3140_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3140_plain_checked : check 391 s3140_plain_contract = true := by decide +kernel
def s3140_plain : CertifiedContract :=
  ⟨3140, 3141, 0, (.inc 2), s3140_plain_contract, 391, s3140_plain_checked⟩

def s3141_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3141_plain_checked : check 107 s3141_plain_contract = true := by decide +kernel
def s3141_plain : CertifiedContract :=
  ⟨3141, 3139, 0, .none, s3141_plain_contract, 107, s3141_plain_checked⟩

def s3142_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s3142_plain_checked : check 110 s3142_plain_contract = true := by decide +kernel
def s3142_plain : CertifiedContract :=
  ⟨3142, 3133, 0, .none, s3142_plain_contract, 110, s3142_plain_checked⟩

def s3143_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s3143_zero_checked : check 360 s3143_zero_contract = true := by decide +kernel
def s3143_zero : CertifiedContract :=
  ⟨3143, 3149, 0, .none, s3143_zero_contract, 360, s3143_zero_checked⟩

def s3143_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3143_positive_checked : check 360 s3143_positive_contract = true := by decide +kernel
def s3143_positive : CertifiedContract :=
  ⟨3143, 3144, 1, (.dec 5), s3143_positive_contract, 360, s3143_positive_checked⟩

def s3144_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3144_plain_checked : check 373 s3144_plain_contract = true := by decide +kernel
def s3144_plain : CertifiedContract :=
  ⟨3144, 3145, 0, (.inc 2), s3144_plain_contract, 373, s3144_plain_checked⟩

def s3145_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3145_plain_checked : check 376 s3145_plain_contract = true := by decide +kernel
def s3145_plain : CertifiedContract :=
  ⟨3145, 3146, 0, (.inc 2), s3145_plain_contract, 376, s3145_plain_checked⟩

def s3146_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3146_plain_checked : check 382 s3146_plain_contract = true := by decide +kernel
def s3146_plain : CertifiedContract :=
  ⟨3146, 3147, 0, (.inc 2), s3146_plain_contract, 382, s3146_plain_checked⟩

def s3147_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s3147_plain_checked : check 388 s3147_plain_contract = true := by decide +kernel
def s3147_plain : CertifiedContract :=
  ⟨3147, 3148, 0, (.inc 2), s3147_plain_contract, 388, s3147_plain_checked⟩

def s3148_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, false] 0 .none⟩
theorem s3148_plain_checked : check 95 s3148_plain_contract = true := by decide +kernel
def s3148_plain : CertifiedContract :=
  ⟨3148, 3143, 0, .none, s3148_plain_contract, 95, s3148_plain_checked⟩

def s3149_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, true, false] 0 .none⟩
theorem s3149_zero_checked : check 366 s3149_zero_contract = true := by decide +kernel
def s3149_zero : CertifiedContract :=
  ⟨3149, 3157, 0, .none, s3149_zero_contract, 366, s3149_zero_checked⟩

def s3149_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, false] 1 (.dec 0)⟩
theorem s3149_positive_checked : check 372 s3149_positive_contract = true := by decide +kernel
def s3149_positive : CertifiedContract :=
  ⟨3149, 3150, 1, (.dec 0), s3149_positive_contract, 372, s3149_positive_checked⟩

def s3150_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3150_plain_checked : check 382 s3150_plain_contract = true := by decide +kernel
def s3150_plain : CertifiedContract :=
  ⟨3150, 3151, 0, (.inc 5), s3150_plain_contract, 382, s3150_plain_checked⟩

def s3151_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3151_zero_checked : check 408 s3151_zero_contract = true := by decide +kernel
def s3151_zero : CertifiedContract :=
  ⟨3151, 3153, 0, .none, s3151_zero_contract, 408, s3151_zero_checked⟩

def s3151_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3151_positive_checked : check 414 s3151_positive_contract = true := by decide +kernel
def s3151_positive : CertifiedContract :=
  ⟨3151, 3152, 1, (.dec 8), s3151_positive_contract, 414, s3151_positive_checked⟩

def s3152_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, true] 0 .none⟩
theorem s3152_plain_checked : check 113 s3152_plain_contract = true := by decide +kernel
def s3152_plain : CertifiedContract :=
  ⟨3152, 3156, 0, .none, s3152_plain_contract, 113, s3152_plain_checked⟩

def s3153_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, true] 0 .none⟩
theorem s3153_zero_checked : check 420 s3153_zero_contract = true := by decide +kernel
def s3153_zero : CertifiedContract :=
  ⟨3153, 3156, 0, .none, s3153_zero_contract, 420, s3153_zero_checked⟩

end PA211.UserCandidate.RuntimeShards.S063
