import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S041
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s2019_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2019_plain_checked : check 391 s2019_plain_contract = true := by decide +kernel
def s2019_plain : CertifiedContract :=
  ⟨2019, 2020, 0, (.inc 5), s2019_plain_contract, 391, s2019_plain_checked⟩

def s2020_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2020_plain_checked : check 418 s2020_plain_contract = true := by decide +kernel
def s2020_plain : CertifiedContract :=
  ⟨2020, 2021, 0, (.inc 8), s2020_plain_contract, 418, s2020_plain_checked⟩

def s2021_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s2021_plain_checked : check 113 s2021_plain_contract = true := by decide +kernel
def s2021_plain : CertifiedContract :=
  ⟨2021, 2018, 0, .none, s2021_plain_contract, 113, s2021_plain_checked⟩

def s2022_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s2022_zero_checked : check 393 s2022_zero_contract = true := by decide +kernel
def s2022_zero : CertifiedContract :=
  ⟨2022, 2028, 0, .none, s2022_zero_contract, 393, s2022_zero_checked⟩

def s2022_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2022_positive_checked : check 396 s2022_positive_contract = true := by decide +kernel
def s2022_positive : CertifiedContract :=
  ⟨2022, 2023, 1, (.dec 8), s2022_positive_contract, 396, s2022_positive_checked⟩

def s2023_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2023_plain_checked : check 391 s2023_plain_contract = true := by decide +kernel
def s2023_plain : CertifiedContract :=
  ⟨2023, 2024, 0, (.inc 5), s2023_plain_contract, 391, s2023_plain_checked⟩

def s2024_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, true] 0 .none⟩
theorem s2024_zero_checked : check 411 s2024_zero_contract = true := by decide +kernel
def s2024_zero : CertifiedContract :=
  ⟨2024, 2027, 0, .none, s2024_zero_contract, 411, s2024_zero_checked⟩

def s2024_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2024_positive_checked : check 414 s2024_positive_contract = true := by decide +kernel
def s2024_positive : CertifiedContract :=
  ⟨2024, 2025, 1, (.dec 8), s2024_positive_contract, 414, s2024_positive_checked⟩

def s2025_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2025_plain_checked : check 409 s2025_plain_contract = true := by decide +kernel
def s2025_plain : CertifiedContract :=
  ⟨2025, 2026, 0, (.inc 2), s2025_plain_contract, 409, s2025_plain_checked⟩

def s2026_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2026_plain_checked : check 113 s2026_plain_contract = true := by decide +kernel
def s2026_plain : CertifiedContract :=
  ⟨2026, 2024, 0, .none, s2026_plain_contract, 113, s2026_plain_checked⟩

def s2027_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s2027_plain_checked : check 116 s2027_plain_contract = true := by decide +kernel
def s2027_plain : CertifiedContract :=
  ⟨2027, 2018, 0, .none, s2027_plain_contract, 116, s2027_plain_checked⟩

def s2028_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s2028_zero_checked : check 378 s2028_zero_contract = true := by decide +kernel
def s2028_zero : CertifiedContract :=
  ⟨2028, 2034, 0, .none, s2028_zero_contract, 378, s2028_zero_checked⟩

def s2028_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2028_positive_checked : check 378 s2028_positive_contract = true := by decide +kernel
def s2028_positive : CertifiedContract :=
  ⟨2028, 2029, 1, (.dec 5), s2028_positive_contract, 378, s2028_positive_checked⟩

def s2029_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2029_plain_checked : check 391 s2029_plain_contract = true := by decide +kernel
def s2029_plain : CertifiedContract :=
  ⟨2029, 2030, 0, (.inc 2), s2029_plain_contract, 391, s2029_plain_checked⟩

def s2030_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2030_plain_checked : check 394 s2030_plain_contract = true := by decide +kernel
def s2030_plain : CertifiedContract :=
  ⟨2030, 2031, 0, (.inc 2), s2030_plain_contract, 394, s2030_plain_checked⟩

def s2031_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2031_plain_checked : check 400 s2031_plain_contract = true := by decide +kernel
def s2031_plain : CertifiedContract :=
  ⟨2031, 2032, 0, (.inc 2), s2031_plain_contract, 400, s2031_plain_checked⟩

def s2032_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s2032_plain_checked : check 406 s2032_plain_contract = true := by decide +kernel
def s2032_plain : CertifiedContract :=
  ⟨2032, 2033, 0, (.inc 2), s2032_plain_contract, 406, s2032_plain_checked⟩

def s2033_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s2033_plain_checked : check 101 s2033_plain_contract = true := by decide +kernel
def s2033_plain : CertifiedContract :=
  ⟨2033, 2028, 0, .none, s2033_plain_contract, 101, s2033_plain_checked⟩

def s2034_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, true, false] 0 .none⟩
theorem s2034_zero_checked : check 384 s2034_zero_contract = true := by decide +kernel
def s2034_zero : CertifiedContract :=
  ⟨2034, 2042, 0, .none, s2034_zero_contract, 384, s2034_zero_checked⟩

def s2034_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, false] 1 (.dec 0)⟩
theorem s2034_positive_checked : check 390 s2034_positive_contract = true := by decide +kernel
def s2034_positive : CertifiedContract :=
  ⟨2034, 2035, 1, (.dec 0), s2034_positive_contract, 390, s2034_positive_checked⟩

def s2035_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2035_plain_checked : check 400 s2035_plain_contract = true := by decide +kernel
def s2035_plain : CertifiedContract :=
  ⟨2035, 2036, 0, (.inc 5), s2035_plain_contract, 400, s2035_plain_checked⟩

def s2036_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s2036_zero_checked : check 426 s2036_zero_contract = true := by decide +kernel
def s2036_zero : CertifiedContract :=
  ⟨2036, 2038, 0, .none, s2036_zero_contract, 426, s2036_zero_checked⟩

def s2036_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2036_positive_checked : check 432 s2036_positive_contract = true := by decide +kernel
def s2036_positive : CertifiedContract :=
  ⟨2036, 2037, 1, (.dec 8), s2036_positive_contract, 432, s2036_positive_checked⟩

def s2037_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, true] 0 .none⟩
theorem s2037_plain_checked : check 119 s2037_plain_contract = true := by decide +kernel
def s2037_plain : CertifiedContract :=
  ⟨2037, 2041, 0, .none, s2037_plain_contract, 119, s2037_plain_checked⟩

def s2038_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, true] 0 .none⟩
theorem s2038_zero_checked : check 438 s2038_zero_contract = true := by decide +kernel
def s2038_zero : CertifiedContract :=
  ⟨2038, 2041, 0, .none, s2038_zero_contract, 438, s2038_zero_checked⟩

def s2038_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2038_positive_checked : check 441 s2038_positive_contract = true := by decide +kernel
def s2038_positive : CertifiedContract :=
  ⟨2038, 2039, 1, (.dec 5), s2038_positive_contract, 441, s2038_positive_checked⟩

def s2039_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2039_plain_checked : check 445 s2039_plain_contract = true := by decide +kernel
def s2039_plain : CertifiedContract :=
  ⟨2039, 2040, 0, (.inc 8), s2039_plain_contract, 445, s2039_plain_checked⟩

def s2040_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s2040_plain_checked : check 122 s2040_plain_contract = true := by decide +kernel
def s2040_plain : CertifiedContract :=
  ⟨2040, 2038, 0, .none, s2040_plain_contract, 122, s2040_plain_checked⟩

def s2041_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s2041_plain_checked : check 113 s2041_plain_contract = true := by decide +kernel
def s2041_plain : CertifiedContract :=
  ⟨2041, 2034, 0, .none, s2041_plain_contract, 113, s2041_plain_checked⟩

def s2042_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s2042_zero_checked : check 384 s2042_zero_contract = true := by decide +kernel
def s2042_zero : CertifiedContract :=
  ⟨2042, 2045, 0, .none, s2042_zero_contract, 384, s2042_zero_checked⟩

def s2042_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2042_positive_checked : check 387 s2042_positive_contract = true := by decide +kernel
def s2042_positive : CertifiedContract :=
  ⟨2042, 2043, 1, (.dec 5), s2042_positive_contract, 387, s2042_positive_checked⟩

def s2043_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, true, true, true] 0 (.inc 0)⟩
theorem s2043_plain_checked : check 400 s2043_plain_contract = true := by decide +kernel
def s2043_plain : CertifiedContract :=
  ⟨2043, 2044, 0, (.inc 0), s2043_plain_contract, 400, s2043_plain_checked⟩

def s2044_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, true, false] 0 .none⟩
theorem s2044_plain_checked : check 107 s2044_plain_contract = true := by decide +kernel
def s2044_plain : CertifiedContract :=
  ⟨2044, 2042, 0, .none, s2044_plain_contract, 107, s2044_plain_checked⟩

def s2045_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s2045_zero_checked : check 381 s2045_zero_contract = true := by decide +kernel
def s2045_zero : CertifiedContract :=
  ⟨2045, 2049, 0, .none, s2045_zero_contract, 381, s2045_zero_checked⟩

def s2045_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2045_positive_checked : check 387 s2045_positive_contract = true := by decide +kernel
def s2045_positive : CertifiedContract :=
  ⟨2045, 2046, 1, (.dec 2), s2045_positive_contract, 387, s2045_positive_checked⟩

def s2046_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2046_plain_checked : check 400 s2046_plain_contract = true := by decide +kernel
def s2046_plain : CertifiedContract :=
  ⟨2046, 2047, 0, (.inc 5), s2046_plain_contract, 400, s2046_plain_checked⟩

def s2047_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2047_plain_checked : check 427 s2047_plain_contract = true := by decide +kernel
def s2047_plain : CertifiedContract :=
  ⟨2047, 2048, 0, (.inc 8), s2047_plain_contract, 427, s2047_plain_checked⟩

def s2048_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s2048_plain_checked : check 116 s2048_plain_contract = true := by decide +kernel
def s2048_plain : CertifiedContract :=
  ⟨2048, 2045, 0, .none, s2048_plain_contract, 116, s2048_plain_checked⟩

def s2049_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s2049_zero_checked : check 402 s2049_zero_contract = true := by decide +kernel
def s2049_zero : CertifiedContract :=
  ⟨2049, 2055, 0, .none, s2049_zero_contract, 402, s2049_zero_checked⟩

def s2049_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2049_positive_checked : check 405 s2049_positive_contract = true := by decide +kernel
def s2049_positive : CertifiedContract :=
  ⟨2049, 2050, 1, (.dec 8), s2049_positive_contract, 405, s2049_positive_checked⟩

def s2050_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2050_plain_checked : check 400 s2050_plain_contract = true := by decide +kernel
def s2050_plain : CertifiedContract :=
  ⟨2050, 2051, 0, (.inc 5), s2050_plain_contract, 400, s2050_plain_checked⟩

def s2051_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s2051_zero_checked : check 420 s2051_zero_contract = true := by decide +kernel
def s2051_zero : CertifiedContract :=
  ⟨2051, 2054, 0, .none, s2051_zero_contract, 420, s2051_zero_checked⟩

def s2051_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2051_positive_checked : check 423 s2051_positive_contract = true := by decide +kernel
def s2051_positive : CertifiedContract :=
  ⟨2051, 2052, 1, (.dec 8), s2051_positive_contract, 423, s2051_positive_checked⟩

def s2052_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2052_plain_checked : check 418 s2052_plain_contract = true := by decide +kernel
def s2052_plain : CertifiedContract :=
  ⟨2052, 2053, 0, (.inc 2), s2052_plain_contract, 418, s2052_plain_checked⟩

def s2053_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2053_plain_checked : check 116 s2053_plain_contract = true := by decide +kernel
def s2053_plain : CertifiedContract :=
  ⟨2053, 2051, 0, .none, s2053_plain_contract, 116, s2053_plain_checked⟩

def s2054_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s2054_plain_checked : check 119 s2054_plain_contract = true := by decide +kernel
def s2054_plain : CertifiedContract :=
  ⟨2054, 2045, 0, .none, s2054_plain_contract, 119, s2054_plain_checked⟩

def s2055_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s2055_zero_checked : check 390 s2055_zero_contract = true := by decide +kernel
def s2055_zero : CertifiedContract :=
  ⟨2055, 2061, 0, .none, s2055_zero_contract, 390, s2055_zero_checked⟩

def s2055_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2055_positive_checked : check 387 s2055_positive_contract = true := by decide +kernel
def s2055_positive : CertifiedContract :=
  ⟨2055, 2056, 1, (.dec 5), s2055_positive_contract, 387, s2055_positive_checked⟩

def s2056_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2056_plain_checked : check 400 s2056_plain_contract = true := by decide +kernel
def s2056_plain : CertifiedContract :=
  ⟨2056, 2057, 0, (.inc 2), s2056_plain_contract, 400, s2056_plain_checked⟩

def s2057_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2057_plain_checked : check 403 s2057_plain_contract = true := by decide +kernel
def s2057_plain : CertifiedContract :=
  ⟨2057, 2058, 0, (.inc 2), s2057_plain_contract, 403, s2057_plain_checked⟩

def s2058_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2058_plain_checked : check 409 s2058_plain_contract = true := by decide +kernel
def s2058_plain : CertifiedContract :=
  ⟨2058, 2059, 0, (.inc 2), s2058_plain_contract, 409, s2058_plain_checked⟩

def s2059_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, true, true] 0 (.inc 2)⟩
theorem s2059_plain_checked : check 415 s2059_plain_contract = true := by decide +kernel
def s2059_plain : CertifiedContract :=
  ⟨2059, 2060, 0, (.inc 2), s2059_plain_contract, 415, s2059_plain_checked⟩

def s2060_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s2060_plain_checked : check 104 s2060_plain_contract = true := by decide +kernel
def s2060_plain : CertifiedContract :=
  ⟨2060, 2055, 0, .none, s2060_plain_contract, 104, s2060_plain_checked⟩

def s2061_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s2061_zero_checked : check 345 s2061_zero_contract = true := by decide +kernel
def s2061_zero : CertifiedContract :=
  ⟨2061, 2064, 0, .none, s2061_zero_contract, 345, s2061_zero_checked⟩

def s2061_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2061_positive_checked : check 351 s2061_positive_contract = true := by decide +kernel
def s2061_positive : CertifiedContract :=
  ⟨2061, 2062, 1, (.dec 2), s2061_positive_contract, 351, s2061_positive_checked⟩

def s2062_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s2062_plain_checked : check 364 s2062_plain_contract = true := by decide +kernel
def s2062_plain : CertifiedContract :=
  ⟨2062, 2063, 0, (.inc 8), s2062_plain_contract, 364, s2062_plain_checked⟩

def s2063_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s2063_plain_checked : check 95 s2063_plain_contract = true := by decide +kernel
def s2063_plain : CertifiedContract :=
  ⟨2063, 2061, 0, .none, s2063_plain_contract, 95, s2063_plain_checked⟩

def s2064_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2064_zero_checked : check 366 s2064_zero_contract = true := by decide +kernel
def s2064_zero : CertifiedContract :=
  ⟨2064, 2067, 0, .none, s2064_zero_contract, 366, s2064_zero_checked⟩

def s2064_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2064_positive_checked : check 372 s2064_positive_contract = true := by decide +kernel
def s2064_positive : CertifiedContract :=
  ⟨2064, 2065, 1, (.dec 0), s2064_positive_contract, 372, s2064_positive_checked⟩

def s2065_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2065_plain_checked : check 364 s2065_plain_contract = true := by decide +kernel
def s2065_plain : CertifiedContract :=
  ⟨2065, 2066, 0, (.inc 2), s2065_plain_contract, 364, s2065_plain_checked⟩

def s2066_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s2066_plain_checked : check 98 s2066_plain_contract = true := by decide +kernel
def s2066_plain : CertifiedContract :=
  ⟨2066, 2064, 0, .none, s2066_plain_contract, 98, s2066_plain_checked⟩

def s2067_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2067_zero_checked : check 372 s2067_zero_contract = true := by decide +kernel
def s2067_zero : CertifiedContract :=
  ⟨2067, 2071, 0, .none, s2067_zero_contract, 372, s2067_zero_checked⟩

def s2067_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2067_positive_checked : check 378 s2067_positive_contract = true := by decide +kernel
def s2067_positive : CertifiedContract :=
  ⟨2067, 2068, 1, (.dec 2), s2067_positive_contract, 378, s2067_positive_checked⟩

def s2068_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2068_plain_checked : check 391 s2068_plain_contract = true := by decide +kernel
def s2068_plain : CertifiedContract :=
  ⟨2068, 2069, 0, (.inc 5), s2068_plain_contract, 391, s2068_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S041
