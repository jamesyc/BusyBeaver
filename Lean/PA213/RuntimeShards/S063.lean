import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S063
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s3104_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s3104_plain_checked : check 97 s3104_plain_contract = true := by decide +kernel
def s3104_plain : CertifiedContract :=
  ⟨3104, 3102, 0, .none, s3104_plain_contract, 97, s3104_plain_checked⟩

def s3105_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s3105_zero_checked : check 353 s3105_zero_contract = true := by decide +kernel
def s3105_zero : CertifiedContract :=
  ⟨3105, 3109, 0, .none, s3105_zero_contract, 353, s3105_zero_checked⟩

def s3105_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3105_positive_checked : check 359 s3105_positive_contract = true := by decide +kernel
def s3105_positive : CertifiedContract :=
  ⟨3105, 3106, 1, (.dec 2), s3105_positive_contract, 359, s3105_positive_checked⟩

def s3106_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3106_plain_checked : check 372 s3106_plain_contract = true := by decide +kernel
def s3106_plain : CertifiedContract :=
  ⟨3106, 3107, 0, (.inc 5), s3106_plain_contract, 372, s3106_plain_checked⟩

def s3107_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3107_plain_checked : check 399 s3107_plain_contract = true := by decide +kernel
def s3107_plain : CertifiedContract :=
  ⟨3107, 3108, 0, (.inc 8), s3107_plain_contract, 399, s3107_plain_checked⟩

def s3108_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s3108_plain_checked : check 106 s3108_plain_contract = true := by decide +kernel
def s3108_plain : CertifiedContract :=
  ⟨3108, 3105, 0, .none, s3108_plain_contract, 106, s3108_plain_checked⟩

def s3109_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s3109_zero_checked : check 374 s3109_zero_contract = true := by decide +kernel
def s3109_zero : CertifiedContract :=
  ⟨3109, 3115, 0, .none, s3109_zero_contract, 374, s3109_zero_checked⟩

def s3109_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3109_positive_checked : check 377 s3109_positive_contract = true := by decide +kernel
def s3109_positive : CertifiedContract :=
  ⟨3109, 3110, 1, (.dec 8), s3109_positive_contract, 377, s3109_positive_checked⟩

def s3110_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3110_plain_checked : check 372 s3110_plain_contract = true := by decide +kernel
def s3110_plain : CertifiedContract :=
  ⟨3110, 3111, 0, (.inc 5), s3110_plain_contract, 372, s3110_plain_checked⟩

def s3111_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s3111_zero_checked : check 392 s3111_zero_contract = true := by decide +kernel
def s3111_zero : CertifiedContract :=
  ⟨3111, 3114, 0, .none, s3111_zero_contract, 392, s3111_zero_checked⟩

def s3111_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3111_positive_checked : check 395 s3111_positive_contract = true := by decide +kernel
def s3111_positive : CertifiedContract :=
  ⟨3111, 3112, 1, (.dec 8), s3111_positive_contract, 395, s3111_positive_checked⟩

def s3112_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3112_plain_checked : check 390 s3112_plain_contract = true := by decide +kernel
def s3112_plain : CertifiedContract :=
  ⟨3112, 3113, 0, (.inc 2), s3112_plain_contract, 390, s3112_plain_checked⟩

def s3113_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3113_plain_checked : check 106 s3113_plain_contract = true := by decide +kernel
def s3113_plain : CertifiedContract :=
  ⟨3113, 3111, 0, .none, s3113_plain_contract, 106, s3113_plain_checked⟩

def s3114_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s3114_plain_checked : check 109 s3114_plain_contract = true := by decide +kernel
def s3114_plain : CertifiedContract :=
  ⟨3114, 3105, 0, .none, s3114_plain_contract, 109, s3114_plain_checked⟩

def s3115_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true] 0 .none⟩
theorem s3115_zero_checked : check 359 s3115_zero_contract = true := by decide +kernel
def s3115_zero : CertifiedContract :=
  ⟨3115, 3121, 0, .none, s3115_zero_contract, 359, s3115_zero_checked⟩

def s3115_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3115_positive_checked : check 359 s3115_positive_contract = true := by decide +kernel
def s3115_positive : CertifiedContract :=
  ⟨3115, 3116, 1, (.dec 5), s3115_positive_contract, 359, s3115_positive_checked⟩

def s3116_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3116_plain_checked : check 372 s3116_plain_contract = true := by decide +kernel
def s3116_plain : CertifiedContract :=
  ⟨3116, 3117, 0, (.inc 2), s3116_plain_contract, 372, s3116_plain_checked⟩

def s3117_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3117_plain_checked : check 375 s3117_plain_contract = true := by decide +kernel
def s3117_plain : CertifiedContract :=
  ⟨3117, 3118, 0, (.inc 2), s3117_plain_contract, 375, s3117_plain_checked⟩

def s3118_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3118_plain_checked : check 372 s3118_plain_contract = true := by decide +kernel
def s3118_plain : CertifiedContract :=
  ⟨3118, 3119, 0, (.inc 2), s3118_plain_contract, 372, s3118_plain_checked⟩

def s3119_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s3119_plain_checked : check 378 s3119_plain_contract = true := by decide +kernel
def s3119_plain : CertifiedContract :=
  ⟨3119, 3120, 0, (.inc 2), s3119_plain_contract, 378, s3119_plain_checked⟩

def s3120_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s3120_plain_checked : check 94 s3120_plain_contract = true := by decide +kernel
def s3120_plain : CertifiedContract :=
  ⟨3120, 3115, 0, .none, s3120_plain_contract, 94, s3120_plain_checked⟩

def s3121_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, false] 0 (.inc 2)⟩
theorem s3121_plain_checked : check 333 s3121_plain_contract = true := by decide +kernel
def s3121_plain : CertifiedContract :=
  ⟨3121, 3122, 0, (.inc 2), s3121_plain_contract, 333, s3121_plain_checked⟩

def s3122_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, true, false] 0 .none⟩
theorem s3122_zero_checked : check 356 s3122_zero_contract = true := by decide +kernel
def s3122_zero : CertifiedContract :=
  ⟨3122, 3130, 0, .none, s3122_zero_contract, 356, s3122_zero_checked⟩

def s3122_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s3122_positive_checked : check 362 s3122_positive_contract = true := by decide +kernel
def s3122_positive : CertifiedContract :=
  ⟨3122, 3123, 1, (.dec 0), s3122_positive_contract, 362, s3122_positive_checked⟩

def s3123_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3123_plain_checked : check 372 s3123_plain_contract = true := by decide +kernel
def s3123_plain : CertifiedContract :=
  ⟨3123, 3124, 0, (.inc 5), s3123_plain_contract, 372, s3123_plain_checked⟩

def s3124_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3124_zero_checked : check 398 s3124_zero_contract = true := by decide +kernel
def s3124_zero : CertifiedContract :=
  ⟨3124, 3126, 0, .none, s3124_zero_contract, 398, s3124_zero_checked⟩

def s3124_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3124_positive_checked : check 404 s3124_positive_contract = true := by decide +kernel
def s3124_positive : CertifiedContract :=
  ⟨3124, 3125, 1, (.dec 8), s3124_positive_contract, 404, s3124_positive_checked⟩

def s3125_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s3125_plain_checked : check 109 s3125_plain_contract = true := by decide +kernel
def s3125_plain : CertifiedContract :=
  ⟨3125, 3129, 0, .none, s3125_plain_contract, 109, s3125_plain_checked⟩

def s3126_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s3126_zero_checked : check 410 s3126_zero_contract = true := by decide +kernel
def s3126_zero : CertifiedContract :=
  ⟨3126, 3129, 0, .none, s3126_zero_contract, 410, s3126_zero_checked⟩

def s3126_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3126_positive_checked : check 413 s3126_positive_contract = true := by decide +kernel
def s3126_positive : CertifiedContract :=
  ⟨3126, 3127, 1, (.dec 5), s3126_positive_contract, 413, s3126_positive_checked⟩

def s3127_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3127_plain_checked : check 417 s3127_plain_contract = true := by decide +kernel
def s3127_plain : CertifiedContract :=
  ⟨3127, 3128, 0, (.inc 8), s3127_plain_contract, 417, s3127_plain_checked⟩

def s3128_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3128_plain_checked : check 112 s3128_plain_contract = true := by decide +kernel
def s3128_plain : CertifiedContract :=
  ⟨3128, 3126, 0, .none, s3128_plain_contract, 112, s3128_plain_checked⟩

def s3129_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, false] 0 .none⟩
theorem s3129_plain_checked : check 103 s3129_plain_contract = true := by decide +kernel
def s3129_plain : CertifiedContract :=
  ⟨3129, 3122, 0, .none, s3129_plain_contract, 103, s3129_plain_checked⟩

def s3130_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s3130_zero_checked : check 356 s3130_zero_contract = true := by decide +kernel
def s3130_zero : CertifiedContract :=
  ⟨3130, 3133, 0, .none, s3130_zero_contract, 356, s3130_zero_checked⟩

def s3130_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s3130_positive_checked : check 359 s3130_positive_contract = true := by decide +kernel
def s3130_positive : CertifiedContract :=
  ⟨3130, 3131, 1, (.dec 5), s3130_positive_contract, 359, s3130_positive_checked⟩

def s3131_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s3131_plain_checked : check 372 s3131_plain_contract = true := by decide +kernel
def s3131_plain : CertifiedContract :=
  ⟨3131, 3132, 0, (.inc 0), s3131_plain_contract, 372, s3131_plain_checked⟩

def s3132_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, false, true, false] 0 .none⟩
theorem s3132_plain_checked : check 97 s3132_plain_contract = true := by decide +kernel
def s3132_plain : CertifiedContract :=
  ⟨3132, 3130, 0, .none, s3132_plain_contract, 97, s3132_plain_checked⟩

def s3133_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, false] 0 .none⟩
theorem s3133_zero_checked : check 353 s3133_zero_contract = true := by decide +kernel
def s3133_zero : CertifiedContract :=
  ⟨3133, 3137, 0, .none, s3133_zero_contract, 353, s3133_zero_checked⟩

def s3133_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3133_positive_checked : check 359 s3133_positive_contract = true := by decide +kernel
def s3133_positive : CertifiedContract :=
  ⟨3133, 3134, 1, (.dec 2), s3133_positive_contract, 359, s3133_positive_checked⟩

def s3134_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3134_plain_checked : check 372 s3134_plain_contract = true := by decide +kernel
def s3134_plain : CertifiedContract :=
  ⟨3134, 3135, 0, (.inc 5), s3134_plain_contract, 372, s3134_plain_checked⟩

def s3135_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3135_plain_checked : check 399 s3135_plain_contract = true := by decide +kernel
def s3135_plain : CertifiedContract :=
  ⟨3135, 3136, 0, (.inc 8), s3135_plain_contract, 399, s3135_plain_checked⟩

def s3136_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s3136_plain_checked : check 106 s3136_plain_contract = true := by decide +kernel
def s3136_plain : CertifiedContract :=
  ⟨3136, 3133, 0, .none, s3136_plain_contract, 106, s3136_plain_checked⟩

def s3137_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, false] 0 .none⟩
theorem s3137_zero_checked : check 374 s3137_zero_contract = true := by decide +kernel
def s3137_zero : CertifiedContract :=
  ⟨3137, 3143, 0, .none, s3137_zero_contract, 374, s3137_zero_checked⟩

def s3137_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3137_positive_checked : check 377 s3137_positive_contract = true := by decide +kernel
def s3137_positive : CertifiedContract :=
  ⟨3137, 3138, 1, (.dec 8), s3137_positive_contract, 377, s3137_positive_checked⟩

def s3138_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3138_plain_checked : check 372 s3138_plain_contract = true := by decide +kernel
def s3138_plain : CertifiedContract :=
  ⟨3138, 3139, 0, (.inc 5), s3138_plain_contract, 372, s3138_plain_checked⟩

def s3139_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, true] 0 .none⟩
theorem s3139_zero_checked : check 392 s3139_zero_contract = true := by decide +kernel
def s3139_zero : CertifiedContract :=
  ⟨3139, 3142, 0, .none, s3139_zero_contract, 392, s3139_zero_checked⟩

def s3139_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3139_positive_checked : check 395 s3139_positive_contract = true := by decide +kernel
def s3139_positive : CertifiedContract :=
  ⟨3139, 3140, 1, (.dec 8), s3139_positive_contract, 395, s3139_positive_checked⟩

def s3140_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3140_plain_checked : check 390 s3140_plain_contract = true := by decide +kernel
def s3140_plain : CertifiedContract :=
  ⟨3140, 3141, 0, (.inc 2), s3140_plain_contract, 390, s3140_plain_checked⟩

def s3141_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3141_plain_checked : check 106 s3141_plain_contract = true := by decide +kernel
def s3141_plain : CertifiedContract :=
  ⟨3141, 3139, 0, .none, s3141_plain_contract, 106, s3141_plain_checked⟩

def s3142_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s3142_plain_checked : check 109 s3142_plain_contract = true := by decide +kernel
def s3142_plain : CertifiedContract :=
  ⟨3142, 3133, 0, .none, s3142_plain_contract, 109, s3142_plain_checked⟩

def s3143_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s3143_zero_checked : check 359 s3143_zero_contract = true := by decide +kernel
def s3143_zero : CertifiedContract :=
  ⟨3143, 3149, 0, .none, s3143_zero_contract, 359, s3143_zero_checked⟩

def s3143_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3143_positive_checked : check 359 s3143_positive_contract = true := by decide +kernel
def s3143_positive : CertifiedContract :=
  ⟨3143, 3144, 1, (.dec 5), s3143_positive_contract, 359, s3143_positive_checked⟩

def s3144_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3144_plain_checked : check 372 s3144_plain_contract = true := by decide +kernel
def s3144_plain : CertifiedContract :=
  ⟨3144, 3145, 0, (.inc 2), s3144_plain_contract, 372, s3144_plain_checked⟩

def s3145_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3145_plain_checked : check 375 s3145_plain_contract = true := by decide +kernel
def s3145_plain : CertifiedContract :=
  ⟨3145, 3146, 0, (.inc 2), s3145_plain_contract, 375, s3145_plain_checked⟩

def s3146_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3146_plain_checked : check 372 s3146_plain_contract = true := by decide +kernel
def s3146_plain : CertifiedContract :=
  ⟨3146, 3147, 0, (.inc 2), s3146_plain_contract, 372, s3146_plain_checked⟩

def s3147_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s3147_plain_checked : check 378 s3147_plain_contract = true := by decide +kernel
def s3147_plain : CertifiedContract :=
  ⟨3147, 3148, 0, (.inc 2), s3147_plain_contract, 378, s3147_plain_checked⟩

def s3148_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, false, true, true, false] 0 .none⟩
theorem s3148_plain_checked : check 94 s3148_plain_contract = true := by decide +kernel
def s3148_plain : CertifiedContract :=
  ⟨3148, 3143, 0, .none, s3148_plain_contract, 94, s3148_plain_checked⟩

def s3149_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, true, false] 0 .none⟩
theorem s3149_zero_checked : check 365 s3149_zero_contract = true := by decide +kernel
def s3149_zero : CertifiedContract :=
  ⟨3149, 3157, 0, .none, s3149_zero_contract, 365, s3149_zero_checked⟩

def s3149_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, false] 1 (.dec 0)⟩
theorem s3149_positive_checked : check 371 s3149_positive_contract = true := by decide +kernel
def s3149_positive : CertifiedContract :=
  ⟨3149, 3150, 1, (.dec 0), s3149_positive_contract, 371, s3149_positive_checked⟩

def s3150_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3150_plain_checked : check 381 s3150_plain_contract = true := by decide +kernel
def s3150_plain : CertifiedContract :=
  ⟨3150, 3151, 0, (.inc 5), s3150_plain_contract, 381, s3150_plain_checked⟩

def s3151_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3151_zero_checked : check 407 s3151_zero_contract = true := by decide +kernel
def s3151_zero : CertifiedContract :=
  ⟨3151, 3153, 0, .none, s3151_zero_contract, 407, s3151_zero_checked⟩

def s3151_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3151_positive_checked : check 413 s3151_positive_contract = true := by decide +kernel
def s3151_positive : CertifiedContract :=
  ⟨3151, 3152, 1, (.dec 8), s3151_positive_contract, 413, s3151_positive_checked⟩

def s3152_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, true] 0 .none⟩
theorem s3152_plain_checked : check 112 s3152_plain_contract = true := by decide +kernel
def s3152_plain : CertifiedContract :=
  ⟨3152, 3156, 0, .none, s3152_plain_contract, 112, s3152_plain_checked⟩

def s3153_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, true] 0 .none⟩
theorem s3153_zero_checked : check 419 s3153_zero_contract = true := by decide +kernel
def s3153_zero : CertifiedContract :=
  ⟨3153, 3156, 0, .none, s3153_zero_contract, 419, s3153_zero_checked⟩

def nonterminal : Array CertifiedContract := #[
  s3104_plain,
  s3105_zero,
  s3105_positive,
  s3106_plain,
  s3107_plain,
  s3108_plain,
  s3109_zero,
  s3109_positive,
  s3110_plain,
  s3111_zero,
  s3111_positive,
  s3112_plain,
  s3113_plain,
  s3114_plain,
  s3115_zero,
  s3115_positive,
  s3116_plain,
  s3117_plain,
  s3118_plain,
  s3119_plain,
  s3120_plain,
  s3121_plain,
  s3122_zero,
  s3122_positive,
  s3123_plain,
  s3124_zero,
  s3124_positive,
  s3125_plain,
  s3126_zero,
  s3126_positive,
  s3127_plain,
  s3128_plain,
  s3129_plain,
  s3130_zero,
  s3130_positive,
  s3131_plain,
  s3132_plain,
  s3133_zero,
  s3133_positive,
  s3134_plain,
  s3135_plain,
  s3136_plain,
  s3137_zero,
  s3137_positive,
  s3138_plain,
  s3139_zero,
  s3139_positive,
  s3140_plain,
  s3141_plain,
  s3142_plain,
  s3143_zero,
  s3143_positive,
  s3144_plain,
  s3145_plain,
  s3146_plain,
  s3147_plain,
  s3148_plain,
  s3149_zero,
  s3149_positive,
  s3150_plain,
  s3151_zero,
  s3151_positive,
  s3152_plain,
  s3153_zero
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S063
