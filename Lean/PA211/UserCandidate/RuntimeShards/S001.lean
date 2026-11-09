module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S001
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s0047_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s0047_plain_checked : check 83 s0047_plain_contract = true := by decide +kernel
def s0047_plain : CertifiedContract :=
  ⟨47, 44, 0, .none, s0047_plain_contract, 83, s0047_plain_checked⟩

def s0048_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s0048_zero_checked : check 288 s0048_zero_contract = true := by decide +kernel
def s0048_zero : CertifiedContract :=
  ⟨48, 51, 0, .none, s0048_zero_contract, 288, s0048_zero_checked⟩

def s0048_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s0048_positive_checked : check 288 s0048_positive_contract = true := by decide +kernel
def s0048_positive : CertifiedContract :=
  ⟨48, 49, 1, (.dec 8), s0048_positive_contract, 288, s0048_positive_checked⟩

def s0049_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, false, false, false, true, true, true, true] 0 (.inc 3)⟩
theorem s0049_plain_checked : check 304 s0049_plain_contract = true := by decide +kernel
def s0049_plain : CertifiedContract :=
  ⟨49, 50, 0, (.inc 3), s0049_plain_contract, 304, s0049_plain_checked⟩

def s0050_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s0050_plain_checked : check 74 s0050_plain_contract = true := by decide +kernel
def s0050_plain : CertifiedContract :=
  ⟨50, 48, 0, .none, s0050_plain_contract, 74, s0050_plain_checked⟩

def s0051_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s0051_zero_checked : check 282 s0051_zero_contract = true := by decide +kernel
def s0051_zero : CertifiedContract :=
  ⟨51, 54, 0, .none, s0051_zero_contract, 282, s0051_zero_checked⟩

def s0051_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0051_positive_checked : check 288 s0051_positive_contract = true := by decide +kernel
def s0051_positive : CertifiedContract :=
  ⟨51, 52, 1, (.dec 2), s0051_positive_contract, 288, s0051_positive_checked⟩

def s0052_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s0052_plain_checked : check 301 s0052_plain_contract = true := by decide +kernel
def s0052_plain : CertifiedContract :=
  ⟨52, 53, 0, (.inc 8), s0052_plain_contract, 301, s0052_plain_checked⟩

def s0053_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s0053_plain_checked : check 74 s0053_plain_contract = true := by decide +kernel
def s0053_plain : CertifiedContract :=
  ⟨53, 51, 0, .none, s0053_plain_contract, 74, s0053_plain_checked⟩

def s0054_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0054_zero_checked : check 303 s0054_zero_contract = true := by decide +kernel
def s0054_zero : CertifiedContract :=
  ⟨54, 57, 0, .none, s0054_zero_contract, 303, s0054_zero_checked⟩

def s0054_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0054_positive_checked : check 309 s0054_positive_contract = true := by decide +kernel
def s0054_positive : CertifiedContract :=
  ⟨54, 55, 1, (.dec 0), s0054_positive_contract, 309, s0054_positive_checked⟩

def s0055_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0055_plain_checked : check 301 s0055_plain_contract = true := by decide +kernel
def s0055_plain : CertifiedContract :=
  ⟨55, 56, 0, (.inc 2), s0055_plain_contract, 301, s0055_plain_checked⟩

def s0056_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s0056_plain_checked : check 77 s0056_plain_contract = true := by decide +kernel
def s0056_plain : CertifiedContract :=
  ⟨56, 54, 0, .none, s0056_plain_contract, 77, s0056_plain_checked⟩

def s0057_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0057_zero_checked : check 309 s0057_zero_contract = true := by decide +kernel
def s0057_zero : CertifiedContract :=
  ⟨57, 61, 0, .none, s0057_zero_contract, 309, s0057_zero_checked⟩

def s0057_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0057_positive_checked : check 315 s0057_positive_contract = true := by decide +kernel
def s0057_positive : CertifiedContract :=
  ⟨57, 58, 1, (.dec 2), s0057_positive_contract, 315, s0057_positive_checked⟩

def s0058_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0058_plain_checked : check 328 s0058_plain_contract = true := by decide +kernel
def s0058_plain : CertifiedContract :=
  ⟨58, 59, 0, (.inc 5), s0058_plain_contract, 328, s0058_plain_checked⟩

def s0059_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0059_plain_checked : check 355 s0059_plain_contract = true := by decide +kernel
def s0059_plain : CertifiedContract :=
  ⟨59, 60, 0, (.inc 8), s0059_plain_contract, 355, s0059_plain_checked⟩

def s0060_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0060_plain_checked : check 92 s0060_plain_contract = true := by decide +kernel
def s0060_plain : CertifiedContract :=
  ⟨60, 57, 0, .none, s0060_plain_contract, 92, s0060_plain_checked⟩

def s0061_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s0061_zero_checked : check 330 s0061_zero_contract = true := by decide +kernel
def s0061_zero : CertifiedContract :=
  ⟨61, 67, 0, .none, s0061_zero_contract, 330, s0061_zero_checked⟩

def s0061_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0061_positive_checked : check 333 s0061_positive_contract = true := by decide +kernel
def s0061_positive : CertifiedContract :=
  ⟨61, 62, 1, (.dec 8), s0061_positive_contract, 333, s0061_positive_checked⟩

def s0062_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0062_plain_checked : check 328 s0062_plain_contract = true := by decide +kernel
def s0062_plain : CertifiedContract :=
  ⟨62, 63, 0, (.inc 5), s0062_plain_contract, 328, s0062_plain_checked⟩

def s0063_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s0063_zero_checked : check 348 s0063_zero_contract = true := by decide +kernel
def s0063_zero : CertifiedContract :=
  ⟨63, 66, 0, .none, s0063_zero_contract, 348, s0063_zero_checked⟩

def s0063_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0063_positive_checked : check 351 s0063_positive_contract = true := by decide +kernel
def s0063_positive : CertifiedContract :=
  ⟨63, 64, 1, (.dec 8), s0063_positive_contract, 351, s0063_positive_checked⟩

def s0064_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0064_plain_checked : check 346 s0064_plain_contract = true := by decide +kernel
def s0064_plain : CertifiedContract :=
  ⟨64, 65, 0, (.inc 2), s0064_plain_contract, 346, s0064_plain_checked⟩

def s0065_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0065_plain_checked : check 92 s0065_plain_contract = true := by decide +kernel
def s0065_plain : CertifiedContract :=
  ⟨65, 63, 0, .none, s0065_plain_contract, 92, s0065_plain_checked⟩

def s0066_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0066_plain_checked : check 95 s0066_plain_contract = true := by decide +kernel
def s0066_plain : CertifiedContract :=
  ⟨66, 57, 0, .none, s0066_plain_contract, 95, s0066_plain_checked⟩

def s0067_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s0067_zero_checked : check 318 s0067_zero_contract = true := by decide +kernel
def s0067_zero : CertifiedContract :=
  ⟨67, 70, 0, .none, s0067_zero_contract, 318, s0067_zero_checked⟩

def s0067_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0067_positive_checked : check 315 s0067_positive_contract = true := by decide +kernel
def s0067_positive : CertifiedContract :=
  ⟨67, 68, 1, (.dec 5), s0067_positive_contract, 315, s0067_positive_checked⟩

def s0068_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0068_plain_checked : check 328 s0068_plain_contract = true := by decide +kernel
def s0068_plain : CertifiedContract :=
  ⟨68, 69, 0, (.inc 0), s0068_plain_contract, 328, s0068_plain_checked⟩

def s0069_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s0069_plain_checked : check 83 s0069_plain_contract = true := by decide +kernel
def s0069_plain : CertifiedContract :=
  ⟨69, 67, 0, .none, s0069_plain_contract, 83, s0069_plain_checked⟩

def s0070_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s0070_zero_checked : check 282 s0070_zero_contract = true := by decide +kernel
def s0070_zero : CertifiedContract :=
  ⟨70, 74, 0, .none, s0070_zero_contract, 282, s0070_zero_checked⟩

def s0070_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, false, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s0070_positive_checked : check 288 s0070_positive_contract = true := by decide +kernel
def s0070_positive : CertifiedContract :=
  ⟨70, 71, 1, (.dec 7), s0070_positive_contract, 288, s0070_positive_checked⟩

def s0071_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0071_plain_checked : check 292 s0071_plain_contract = true := by decide +kernel
def s0071_plain : CertifiedContract :=
  ⟨71, 72, 0, (.inc 2), s0071_plain_contract, 292, s0071_plain_checked⟩

def s0072_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0072_plain_checked : check 319 s0072_plain_contract = true := by decide +kernel
def s0072_plain : CertifiedContract :=
  ⟨72, 73, 0, (.inc 8), s0072_plain_contract, 319, s0072_plain_checked⟩

def s0073_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s0073_plain_checked : check 80 s0073_plain_contract = true := by decide +kernel
def s0073_plain : CertifiedContract :=
  ⟨73, 70, 0, .none, s0073_plain_contract, 80, s0073_plain_checked⟩

def s0074_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s0074_zero_checked : check 291 s0074_zero_contract = true := by decide +kernel
def s0074_zero : CertifiedContract :=
  ⟨74, 77, 0, .none, s0074_zero_contract, 291, s0074_zero_checked⟩

def s0074_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s0074_positive_checked : check 288 s0074_positive_contract = true := by decide +kernel
def s0074_positive : CertifiedContract :=
  ⟨74, 75, 1, (.dec 8), s0074_positive_contract, 288, s0074_positive_checked⟩

def s0075_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, false, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s0075_plain_checked : check 319 s0075_plain_contract = true := by decide +kernel
def s0075_plain : CertifiedContract :=
  ⟨75, 76, 0, (.inc 7), s0075_plain_contract, 319, s0075_plain_checked⟩

def s0076_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s0076_plain_checked : check 74 s0076_plain_contract = true := by decide +kernel
def s0076_plain : CertifiedContract :=
  ⟨76, 74, 0, .none, s0076_plain_contract, 74, s0076_plain_checked⟩

def s0077_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s0077_zero_checked : check 285 s0077_zero_contract = true := by decide +kernel
def s0077_zero : CertifiedContract :=
  ⟨77, 85, 0, .none, s0077_zero_contract, 285, s0077_zero_checked⟩

def s0077_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s0077_positive_checked : check 291 s0077_positive_contract = true := by decide +kernel
def s0077_positive : CertifiedContract :=
  ⟨77, 78, 1, (.dec 0), s0077_positive_contract, 291, s0077_positive_checked⟩

def s0078_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0078_plain_checked : check 301 s0078_plain_contract = true := by decide +kernel
def s0078_plain : CertifiedContract :=
  ⟨78, 79, 0, (.inc 5), s0078_plain_contract, 301, s0078_plain_checked⟩

def s0079_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0079_zero_checked : check 327 s0079_zero_contract = true := by decide +kernel
def s0079_zero : CertifiedContract :=
  ⟨79, 81, 0, .none, s0079_zero_contract, 327, s0079_zero_checked⟩

def s0079_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0079_positive_checked : check 333 s0079_positive_contract = true := by decide +kernel
def s0079_positive : CertifiedContract :=
  ⟨79, 80, 1, (.dec 8), s0079_positive_contract, 333, s0079_positive_checked⟩

def s0080_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s0080_plain_checked : check 86 s0080_plain_contract = true := by decide +kernel
def s0080_plain : CertifiedContract :=
  ⟨80, 84, 0, .none, s0080_plain_contract, 86, s0080_plain_checked⟩

def s0081_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s0081_zero_checked : check 339 s0081_zero_contract = true := by decide +kernel
def s0081_zero : CertifiedContract :=
  ⟨81, 84, 0, .none, s0081_zero_contract, 339, s0081_zero_checked⟩

def s0081_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0081_positive_checked : check 342 s0081_positive_contract = true := by decide +kernel
def s0081_positive : CertifiedContract :=
  ⟨81, 82, 1, (.dec 5), s0081_positive_contract, 342, s0081_positive_checked⟩

def s0082_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0082_plain_checked : check 346 s0082_plain_contract = true := by decide +kernel
def s0082_plain : CertifiedContract :=
  ⟨82, 83, 0, (.inc 8), s0082_plain_contract, 346, s0082_plain_checked⟩

def s0083_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0083_plain_checked : check 89 s0083_plain_contract = true := by decide +kernel
def s0083_plain : CertifiedContract :=
  ⟨83, 81, 0, .none, s0083_plain_contract, 89, s0083_plain_checked⟩

def s0084_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s0084_plain_checked : check 80 s0084_plain_contract = true := by decide +kernel
def s0084_plain : CertifiedContract :=
  ⟨84, 77, 0, .none, s0084_plain_contract, 80, s0084_plain_checked⟩

def s0085_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0085_zero_checked : check 285 s0085_zero_contract = true := by decide +kernel
def s0085_zero : CertifiedContract :=
  ⟨85, 88, 0, .none, s0085_zero_contract, 285, s0085_zero_checked⟩

def s0085_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0085_positive_checked : check 288 s0085_positive_contract = true := by decide +kernel
def s0085_positive : CertifiedContract :=
  ⟨85, 86, 1, (.dec 5), s0085_positive_contract, 288, s0085_positive_checked⟩

def s0086_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s0086_plain_checked : check 301 s0086_plain_contract = true := by decide +kernel
def s0086_plain : CertifiedContract :=
  ⟨86, 87, 0, (.inc 0), s0086_plain_contract, 301, s0086_plain_checked⟩

def s0087_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s0087_plain_checked : check 74 s0087_plain_contract = true := by decide +kernel
def s0087_plain : CertifiedContract :=
  ⟨87, 85, 0, .none, s0087_plain_contract, 74, s0087_plain_checked⟩

def s0088_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s0088_zero_checked : check 282 s0088_zero_contract = true := by decide +kernel
def s0088_zero : CertifiedContract :=
  ⟨88, 92, 0, .none, s0088_zero_contract, 282, s0088_zero_checked⟩

def s0088_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0088_positive_checked : check 288 s0088_positive_contract = true := by decide +kernel
def s0088_positive : CertifiedContract :=
  ⟨88, 89, 1, (.dec 2), s0088_positive_contract, 288, s0088_positive_checked⟩

def s0089_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0089_plain_checked : check 301 s0089_plain_contract = true := by decide +kernel
def s0089_plain : CertifiedContract :=
  ⟨89, 90, 0, (.inc 5), s0089_plain_contract, 301, s0089_plain_checked⟩

def s0090_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0090_plain_checked : check 328 s0090_plain_contract = true := by decide +kernel
def s0090_plain : CertifiedContract :=
  ⟨90, 91, 0, (.inc 8), s0090_plain_contract, 328, s0090_plain_checked⟩

def s0091_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0091_plain_checked : check 83 s0091_plain_contract = true := by decide +kernel
def s0091_plain : CertifiedContract :=
  ⟨91, 88, 0, .none, s0091_plain_contract, 83, s0091_plain_checked⟩

def s0092_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s0092_zero_checked : check 303 s0092_zero_contract = true := by decide +kernel
def s0092_zero : CertifiedContract :=
  ⟨92, 98, 0, .none, s0092_zero_contract, 303, s0092_zero_checked⟩

def s0092_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0092_positive_checked : check 306 s0092_positive_contract = true := by decide +kernel
def s0092_positive : CertifiedContract :=
  ⟨92, 93, 1, (.dec 8), s0092_positive_contract, 306, s0092_positive_checked⟩

def s0093_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0093_plain_checked : check 301 s0093_plain_contract = true := by decide +kernel
def s0093_plain : CertifiedContract :=
  ⟨93, 94, 0, (.inc 5), s0093_plain_contract, 301, s0093_plain_checked⟩

def s0094_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s0094_zero_checked : check 321 s0094_zero_contract = true := by decide +kernel
def s0094_zero : CertifiedContract :=
  ⟨94, 97, 0, .none, s0094_zero_contract, 321, s0094_zero_checked⟩

def s0094_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0094_positive_checked : check 324 s0094_positive_contract = true := by decide +kernel
def s0094_positive : CertifiedContract :=
  ⟨94, 95, 1, (.dec 8), s0094_positive_contract, 324, s0094_positive_checked⟩

end PA211.UserCandidate.RuntimeShards.S001
