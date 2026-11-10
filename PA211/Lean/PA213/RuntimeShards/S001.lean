import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S001
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s0047_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s0047_plain_checked : check 82 s0047_plain_contract = true := by decide +kernel
def s0047_plain : CertifiedContract :=
  ⟨47, 44, 0, .none, s0047_plain_contract, 82, s0047_plain_checked⟩

def s0048_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s0048_zero_checked : check 287 s0048_zero_contract = true := by decide +kernel
def s0048_zero : CertifiedContract :=
  ⟨48, 51, 0, .none, s0048_zero_contract, 287, s0048_zero_checked⟩

def s0048_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s0048_positive_checked : check 287 s0048_positive_contract = true := by decide +kernel
def s0048_positive : CertifiedContract :=
  ⟨48, 49, 1, (.dec 8), s0048_positive_contract, 287, s0048_positive_checked⟩

def s0049_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, false, false, false, true, true, true, true] 0 (.inc 3)⟩
theorem s0049_plain_checked : check 303 s0049_plain_contract = true := by decide +kernel
def s0049_plain : CertifiedContract :=
  ⟨49, 50, 0, (.inc 3), s0049_plain_contract, 303, s0049_plain_checked⟩

def s0050_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s0050_plain_checked : check 73 s0050_plain_contract = true := by decide +kernel
def s0050_plain : CertifiedContract :=
  ⟨50, 48, 0, .none, s0050_plain_contract, 73, s0050_plain_checked⟩

def s0051_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s0051_zero_checked : check 281 s0051_zero_contract = true := by decide +kernel
def s0051_zero : CertifiedContract :=
  ⟨51, 54, 0, .none, s0051_zero_contract, 281, s0051_zero_checked⟩

def s0051_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0051_positive_checked : check 287 s0051_positive_contract = true := by decide +kernel
def s0051_positive : CertifiedContract :=
  ⟨51, 52, 1, (.dec 2), s0051_positive_contract, 287, s0051_positive_checked⟩

def s0052_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s0052_plain_checked : check 300 s0052_plain_contract = true := by decide +kernel
def s0052_plain : CertifiedContract :=
  ⟨52, 53, 0, (.inc 8), s0052_plain_contract, 300, s0052_plain_checked⟩

def s0053_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s0053_plain_checked : check 73 s0053_plain_contract = true := by decide +kernel
def s0053_plain : CertifiedContract :=
  ⟨53, 51, 0, .none, s0053_plain_contract, 73, s0053_plain_checked⟩

def s0054_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0054_zero_checked : check 302 s0054_zero_contract = true := by decide +kernel
def s0054_zero : CertifiedContract :=
  ⟨54, 57, 0, .none, s0054_zero_contract, 302, s0054_zero_checked⟩

def s0054_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0054_positive_checked : check 308 s0054_positive_contract = true := by decide +kernel
def s0054_positive : CertifiedContract :=
  ⟨54, 55, 1, (.dec 0), s0054_positive_contract, 308, s0054_positive_checked⟩

def s0055_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0055_plain_checked : check 300 s0055_plain_contract = true := by decide +kernel
def s0055_plain : CertifiedContract :=
  ⟨55, 56, 0, (.inc 2), s0055_plain_contract, 300, s0055_plain_checked⟩

def s0056_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s0056_plain_checked : check 76 s0056_plain_contract = true := by decide +kernel
def s0056_plain : CertifiedContract :=
  ⟨56, 54, 0, .none, s0056_plain_contract, 76, s0056_plain_checked⟩

def s0057_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0057_zero_checked : check 308 s0057_zero_contract = true := by decide +kernel
def s0057_zero : CertifiedContract :=
  ⟨57, 61, 0, .none, s0057_zero_contract, 308, s0057_zero_checked⟩

def s0057_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0057_positive_checked : check 314 s0057_positive_contract = true := by decide +kernel
def s0057_positive : CertifiedContract :=
  ⟨57, 58, 1, (.dec 2), s0057_positive_contract, 314, s0057_positive_checked⟩

def s0058_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0058_plain_checked : check 327 s0058_plain_contract = true := by decide +kernel
def s0058_plain : CertifiedContract :=
  ⟨58, 59, 0, (.inc 5), s0058_plain_contract, 327, s0058_plain_checked⟩

def s0059_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0059_plain_checked : check 354 s0059_plain_contract = true := by decide +kernel
def s0059_plain : CertifiedContract :=
  ⟨59, 60, 0, (.inc 8), s0059_plain_contract, 354, s0059_plain_checked⟩

def s0060_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0060_plain_checked : check 91 s0060_plain_contract = true := by decide +kernel
def s0060_plain : CertifiedContract :=
  ⟨60, 57, 0, .none, s0060_plain_contract, 91, s0060_plain_checked⟩

def s0061_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s0061_zero_checked : check 329 s0061_zero_contract = true := by decide +kernel
def s0061_zero : CertifiedContract :=
  ⟨61, 67, 0, .none, s0061_zero_contract, 329, s0061_zero_checked⟩

def s0061_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0061_positive_checked : check 332 s0061_positive_contract = true := by decide +kernel
def s0061_positive : CertifiedContract :=
  ⟨61, 62, 1, (.dec 8), s0061_positive_contract, 332, s0061_positive_checked⟩

def s0062_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0062_plain_checked : check 327 s0062_plain_contract = true := by decide +kernel
def s0062_plain : CertifiedContract :=
  ⟨62, 63, 0, (.inc 5), s0062_plain_contract, 327, s0062_plain_checked⟩

def s0063_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s0063_zero_checked : check 347 s0063_zero_contract = true := by decide +kernel
def s0063_zero : CertifiedContract :=
  ⟨63, 66, 0, .none, s0063_zero_contract, 347, s0063_zero_checked⟩

def s0063_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0063_positive_checked : check 350 s0063_positive_contract = true := by decide +kernel
def s0063_positive : CertifiedContract :=
  ⟨63, 64, 1, (.dec 8), s0063_positive_contract, 350, s0063_positive_checked⟩

def s0064_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0064_plain_checked : check 345 s0064_plain_contract = true := by decide +kernel
def s0064_plain : CertifiedContract :=
  ⟨64, 65, 0, (.inc 2), s0064_plain_contract, 345, s0064_plain_checked⟩

def s0065_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0065_plain_checked : check 91 s0065_plain_contract = true := by decide +kernel
def s0065_plain : CertifiedContract :=
  ⟨65, 63, 0, .none, s0065_plain_contract, 91, s0065_plain_checked⟩

def s0066_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0066_plain_checked : check 94 s0066_plain_contract = true := by decide +kernel
def s0066_plain : CertifiedContract :=
  ⟨66, 57, 0, .none, s0066_plain_contract, 94, s0066_plain_checked⟩

def s0067_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s0067_zero_checked : check 317 s0067_zero_contract = true := by decide +kernel
def s0067_zero : CertifiedContract :=
  ⟨67, 70, 0, .none, s0067_zero_contract, 317, s0067_zero_checked⟩

def s0067_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0067_positive_checked : check 314 s0067_positive_contract = true := by decide +kernel
def s0067_positive : CertifiedContract :=
  ⟨67, 68, 1, (.dec 5), s0067_positive_contract, 314, s0067_positive_checked⟩

def s0068_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0068_plain_checked : check 327 s0068_plain_contract = true := by decide +kernel
def s0068_plain : CertifiedContract :=
  ⟨68, 69, 0, (.inc 0), s0068_plain_contract, 327, s0068_plain_checked⟩

def s0069_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s0069_plain_checked : check 82 s0069_plain_contract = true := by decide +kernel
def s0069_plain : CertifiedContract :=
  ⟨69, 67, 0, .none, s0069_plain_contract, 82, s0069_plain_checked⟩

def s0070_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s0070_zero_checked : check 281 s0070_zero_contract = true := by decide +kernel
def s0070_zero : CertifiedContract :=
  ⟨70, 74, 0, .none, s0070_zero_contract, 281, s0070_zero_checked⟩

def s0070_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, false, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s0070_positive_checked : check 287 s0070_positive_contract = true := by decide +kernel
def s0070_positive : CertifiedContract :=
  ⟨70, 71, 1, (.dec 7), s0070_positive_contract, 287, s0070_positive_checked⟩

def s0071_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0071_plain_checked : check 291 s0071_plain_contract = true := by decide +kernel
def s0071_plain : CertifiedContract :=
  ⟨71, 72, 0, (.inc 2), s0071_plain_contract, 291, s0071_plain_checked⟩

def s0072_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0072_plain_checked : check 318 s0072_plain_contract = true := by decide +kernel
def s0072_plain : CertifiedContract :=
  ⟨72, 73, 0, (.inc 8), s0072_plain_contract, 318, s0072_plain_checked⟩

def s0073_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s0073_plain_checked : check 79 s0073_plain_contract = true := by decide +kernel
def s0073_plain : CertifiedContract :=
  ⟨73, 70, 0, .none, s0073_plain_contract, 79, s0073_plain_checked⟩

def s0074_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s0074_zero_checked : check 290 s0074_zero_contract = true := by decide +kernel
def s0074_zero : CertifiedContract :=
  ⟨74, 77, 0, .none, s0074_zero_contract, 290, s0074_zero_checked⟩

def s0074_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s0074_positive_checked : check 287 s0074_positive_contract = true := by decide +kernel
def s0074_positive : CertifiedContract :=
  ⟨74, 75, 1, (.dec 8), s0074_positive_contract, 287, s0074_positive_checked⟩

def s0075_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, false, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s0075_plain_checked : check 318 s0075_plain_contract = true := by decide +kernel
def s0075_plain : CertifiedContract :=
  ⟨75, 76, 0, (.inc 7), s0075_plain_contract, 318, s0075_plain_checked⟩

def s0076_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s0076_plain_checked : check 73 s0076_plain_contract = true := by decide +kernel
def s0076_plain : CertifiedContract :=
  ⟨76, 74, 0, .none, s0076_plain_contract, 73, s0076_plain_checked⟩

def s0077_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s0077_zero_checked : check 284 s0077_zero_contract = true := by decide +kernel
def s0077_zero : CertifiedContract :=
  ⟨77, 85, 0, .none, s0077_zero_contract, 284, s0077_zero_checked⟩

def s0077_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s0077_positive_checked : check 290 s0077_positive_contract = true := by decide +kernel
def s0077_positive : CertifiedContract :=
  ⟨77, 78, 1, (.dec 0), s0077_positive_contract, 290, s0077_positive_checked⟩

def s0078_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0078_plain_checked : check 300 s0078_plain_contract = true := by decide +kernel
def s0078_plain : CertifiedContract :=
  ⟨78, 79, 0, (.inc 5), s0078_plain_contract, 300, s0078_plain_checked⟩

def s0079_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0079_zero_checked : check 326 s0079_zero_contract = true := by decide +kernel
def s0079_zero : CertifiedContract :=
  ⟨79, 81, 0, .none, s0079_zero_contract, 326, s0079_zero_checked⟩

def s0079_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0079_positive_checked : check 332 s0079_positive_contract = true := by decide +kernel
def s0079_positive : CertifiedContract :=
  ⟨79, 80, 1, (.dec 8), s0079_positive_contract, 332, s0079_positive_checked⟩

def s0080_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s0080_plain_checked : check 85 s0080_plain_contract = true := by decide +kernel
def s0080_plain : CertifiedContract :=
  ⟨80, 84, 0, .none, s0080_plain_contract, 85, s0080_plain_checked⟩

def s0081_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s0081_zero_checked : check 338 s0081_zero_contract = true := by decide +kernel
def s0081_zero : CertifiedContract :=
  ⟨81, 84, 0, .none, s0081_zero_contract, 338, s0081_zero_checked⟩

def s0081_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0081_positive_checked : check 341 s0081_positive_contract = true := by decide +kernel
def s0081_positive : CertifiedContract :=
  ⟨81, 82, 1, (.dec 5), s0081_positive_contract, 341, s0081_positive_checked⟩

def s0082_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0082_plain_checked : check 345 s0082_plain_contract = true := by decide +kernel
def s0082_plain : CertifiedContract :=
  ⟨82, 83, 0, (.inc 8), s0082_plain_contract, 345, s0082_plain_checked⟩

def s0083_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0083_plain_checked : check 88 s0083_plain_contract = true := by decide +kernel
def s0083_plain : CertifiedContract :=
  ⟨83, 81, 0, .none, s0083_plain_contract, 88, s0083_plain_checked⟩

def s0084_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s0084_plain_checked : check 79 s0084_plain_contract = true := by decide +kernel
def s0084_plain : CertifiedContract :=
  ⟨84, 77, 0, .none, s0084_plain_contract, 79, s0084_plain_checked⟩

def s0085_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0085_zero_checked : check 284 s0085_zero_contract = true := by decide +kernel
def s0085_zero : CertifiedContract :=
  ⟨85, 88, 0, .none, s0085_zero_contract, 284, s0085_zero_checked⟩

def s0085_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0085_positive_checked : check 287 s0085_positive_contract = true := by decide +kernel
def s0085_positive : CertifiedContract :=
  ⟨85, 86, 1, (.dec 5), s0085_positive_contract, 287, s0085_positive_checked⟩

def s0086_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s0086_plain_checked : check 300 s0086_plain_contract = true := by decide +kernel
def s0086_plain : CertifiedContract :=
  ⟨86, 87, 0, (.inc 0), s0086_plain_contract, 300, s0086_plain_checked⟩

def s0087_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s0087_plain_checked : check 73 s0087_plain_contract = true := by decide +kernel
def s0087_plain : CertifiedContract :=
  ⟨87, 85, 0, .none, s0087_plain_contract, 73, s0087_plain_checked⟩

def s0088_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s0088_zero_checked : check 281 s0088_zero_contract = true := by decide +kernel
def s0088_zero : CertifiedContract :=
  ⟨88, 92, 0, .none, s0088_zero_contract, 281, s0088_zero_checked⟩

def s0088_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0088_positive_checked : check 287 s0088_positive_contract = true := by decide +kernel
def s0088_positive : CertifiedContract :=
  ⟨88, 89, 1, (.dec 2), s0088_positive_contract, 287, s0088_positive_checked⟩

def s0089_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0089_plain_checked : check 300 s0089_plain_contract = true := by decide +kernel
def s0089_plain : CertifiedContract :=
  ⟨89, 90, 0, (.inc 5), s0089_plain_contract, 300, s0089_plain_checked⟩

def s0090_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0090_plain_checked : check 327 s0090_plain_contract = true := by decide +kernel
def s0090_plain : CertifiedContract :=
  ⟨90, 91, 0, (.inc 8), s0090_plain_contract, 327, s0090_plain_checked⟩

def s0091_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0091_plain_checked : check 82 s0091_plain_contract = true := by decide +kernel
def s0091_plain : CertifiedContract :=
  ⟨91, 88, 0, .none, s0091_plain_contract, 82, s0091_plain_checked⟩

def s0092_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s0092_zero_checked : check 302 s0092_zero_contract = true := by decide +kernel
def s0092_zero : CertifiedContract :=
  ⟨92, 98, 0, .none, s0092_zero_contract, 302, s0092_zero_checked⟩

def s0092_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0092_positive_checked : check 305 s0092_positive_contract = true := by decide +kernel
def s0092_positive : CertifiedContract :=
  ⟨92, 93, 1, (.dec 8), s0092_positive_contract, 305, s0092_positive_checked⟩

def s0093_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0093_plain_checked : check 300 s0093_plain_contract = true := by decide +kernel
def s0093_plain : CertifiedContract :=
  ⟨93, 94, 0, (.inc 5), s0093_plain_contract, 300, s0093_plain_checked⟩

def s0094_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s0094_zero_checked : check 320 s0094_zero_contract = true := by decide +kernel
def s0094_zero : CertifiedContract :=
  ⟨94, 97, 0, .none, s0094_zero_contract, 320, s0094_zero_checked⟩

def s0094_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0094_positive_checked : check 323 s0094_positive_contract = true := by decide +kernel
def s0094_positive : CertifiedContract :=
  ⟨94, 95, 1, (.dec 8), s0094_positive_contract, 323, s0094_positive_checked⟩

def nonterminal : Array CertifiedContract := #[
  s0047_plain,
  s0048_zero,
  s0048_positive,
  s0049_plain,
  s0050_plain,
  s0051_zero,
  s0051_positive,
  s0052_plain,
  s0053_plain,
  s0054_zero,
  s0054_positive,
  s0055_plain,
  s0056_plain,
  s0057_zero,
  s0057_positive,
  s0058_plain,
  s0059_plain,
  s0060_plain,
  s0061_zero,
  s0061_positive,
  s0062_plain,
  s0063_zero,
  s0063_positive,
  s0064_plain,
  s0065_plain,
  s0066_plain,
  s0067_zero,
  s0067_positive,
  s0068_plain,
  s0069_plain,
  s0070_zero,
  s0070_positive,
  s0071_plain,
  s0072_plain,
  s0073_plain,
  s0074_zero,
  s0074_positive,
  s0075_plain,
  s0076_plain,
  s0077_zero,
  s0077_positive,
  s0078_plain,
  s0079_zero,
  s0079_positive,
  s0080_plain,
  s0081_zero,
  s0081_positive,
  s0082_plain,
  s0083_plain,
  s0084_plain,
  s0085_zero,
  s0085_positive,
  s0086_plain,
  s0087_plain,
  s0088_zero,
  s0088_positive,
  s0089_plain,
  s0090_plain,
  s0091_plain,
  s0092_zero,
  s0092_positive,
  s0093_plain,
  s0094_zero,
  s0094_positive
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S001
