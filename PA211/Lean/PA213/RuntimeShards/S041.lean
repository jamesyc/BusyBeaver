import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S041
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s2019_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2019_plain_checked : check 390 s2019_plain_contract = true := by decide +kernel
def s2019_plain : CertifiedContract :=
  ⟨2019, 2020, 0, (.inc 5), s2019_plain_contract, 390, s2019_plain_checked⟩

def s2020_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2020_plain_checked : check 417 s2020_plain_contract = true := by decide +kernel
def s2020_plain : CertifiedContract :=
  ⟨2020, 2021, 0, (.inc 8), s2020_plain_contract, 417, s2020_plain_checked⟩

def s2021_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s2021_plain_checked : check 112 s2021_plain_contract = true := by decide +kernel
def s2021_plain : CertifiedContract :=
  ⟨2021, 2018, 0, .none, s2021_plain_contract, 112, s2021_plain_checked⟩

def s2022_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s2022_zero_checked : check 392 s2022_zero_contract = true := by decide +kernel
def s2022_zero : CertifiedContract :=
  ⟨2022, 2028, 0, .none, s2022_zero_contract, 392, s2022_zero_checked⟩

def s2022_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2022_positive_checked : check 395 s2022_positive_contract = true := by decide +kernel
def s2022_positive : CertifiedContract :=
  ⟨2022, 2023, 1, (.dec 8), s2022_positive_contract, 395, s2022_positive_checked⟩

def s2023_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2023_plain_checked : check 390 s2023_plain_contract = true := by decide +kernel
def s2023_plain : CertifiedContract :=
  ⟨2023, 2024, 0, (.inc 5), s2023_plain_contract, 390, s2023_plain_checked⟩

def s2024_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, true] 0 .none⟩
theorem s2024_zero_checked : check 410 s2024_zero_contract = true := by decide +kernel
def s2024_zero : CertifiedContract :=
  ⟨2024, 2027, 0, .none, s2024_zero_contract, 410, s2024_zero_checked⟩

def s2024_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2024_positive_checked : check 413 s2024_positive_contract = true := by decide +kernel
def s2024_positive : CertifiedContract :=
  ⟨2024, 2025, 1, (.dec 8), s2024_positive_contract, 413, s2024_positive_checked⟩

def s2025_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2025_plain_checked : check 408 s2025_plain_contract = true := by decide +kernel
def s2025_plain : CertifiedContract :=
  ⟨2025, 2026, 0, (.inc 2), s2025_plain_contract, 408, s2025_plain_checked⟩

def s2026_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2026_plain_checked : check 112 s2026_plain_contract = true := by decide +kernel
def s2026_plain : CertifiedContract :=
  ⟨2026, 2024, 0, .none, s2026_plain_contract, 112, s2026_plain_checked⟩

def s2027_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s2027_plain_checked : check 115 s2027_plain_contract = true := by decide +kernel
def s2027_plain : CertifiedContract :=
  ⟨2027, 2018, 0, .none, s2027_plain_contract, 115, s2027_plain_checked⟩

def s2028_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s2028_zero_checked : check 377 s2028_zero_contract = true := by decide +kernel
def s2028_zero : CertifiedContract :=
  ⟨2028, 2034, 0, .none, s2028_zero_contract, 377, s2028_zero_checked⟩

def s2028_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2028_positive_checked : check 377 s2028_positive_contract = true := by decide +kernel
def s2028_positive : CertifiedContract :=
  ⟨2028, 2029, 1, (.dec 5), s2028_positive_contract, 377, s2028_positive_checked⟩

def s2029_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2029_plain_checked : check 390 s2029_plain_contract = true := by decide +kernel
def s2029_plain : CertifiedContract :=
  ⟨2029, 2030, 0, (.inc 2), s2029_plain_contract, 390, s2029_plain_checked⟩

def s2030_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2030_plain_checked : check 393 s2030_plain_contract = true := by decide +kernel
def s2030_plain : CertifiedContract :=
  ⟨2030, 2031, 0, (.inc 2), s2030_plain_contract, 393, s2030_plain_checked⟩

def s2031_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2031_plain_checked : check 390 s2031_plain_contract = true := by decide +kernel
def s2031_plain : CertifiedContract :=
  ⟨2031, 2032, 0, (.inc 2), s2031_plain_contract, 390, s2031_plain_checked⟩

def s2032_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s2032_plain_checked : check 396 s2032_plain_contract = true := by decide +kernel
def s2032_plain : CertifiedContract :=
  ⟨2032, 2033, 0, (.inc 2), s2032_plain_contract, 396, s2032_plain_checked⟩

def s2033_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s2033_plain_checked : check 100 s2033_plain_contract = true := by decide +kernel
def s2033_plain : CertifiedContract :=
  ⟨2033, 2028, 0, .none, s2033_plain_contract, 100, s2033_plain_checked⟩

def s2034_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, true, false] 0 .none⟩
theorem s2034_zero_checked : check 383 s2034_zero_contract = true := by decide +kernel
def s2034_zero : CertifiedContract :=
  ⟨2034, 2042, 0, .none, s2034_zero_contract, 383, s2034_zero_checked⟩

def s2034_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, false] 1 (.dec 0)⟩
theorem s2034_positive_checked : check 389 s2034_positive_contract = true := by decide +kernel
def s2034_positive : CertifiedContract :=
  ⟨2034, 2035, 1, (.dec 0), s2034_positive_contract, 389, s2034_positive_checked⟩

def s2035_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2035_plain_checked : check 399 s2035_plain_contract = true := by decide +kernel
def s2035_plain : CertifiedContract :=
  ⟨2035, 2036, 0, (.inc 5), s2035_plain_contract, 399, s2035_plain_checked⟩

def s2036_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s2036_zero_checked : check 425 s2036_zero_contract = true := by decide +kernel
def s2036_zero : CertifiedContract :=
  ⟨2036, 2038, 0, .none, s2036_zero_contract, 425, s2036_zero_checked⟩

def s2036_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2036_positive_checked : check 431 s2036_positive_contract = true := by decide +kernel
def s2036_positive : CertifiedContract :=
  ⟨2036, 2037, 1, (.dec 8), s2036_positive_contract, 431, s2036_positive_checked⟩

def s2037_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, true] 0 .none⟩
theorem s2037_plain_checked : check 118 s2037_plain_contract = true := by decide +kernel
def s2037_plain : CertifiedContract :=
  ⟨2037, 2041, 0, .none, s2037_plain_contract, 118, s2037_plain_checked⟩

def s2038_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, true] 0 .none⟩
theorem s2038_zero_checked : check 437 s2038_zero_contract = true := by decide +kernel
def s2038_zero : CertifiedContract :=
  ⟨2038, 2041, 0, .none, s2038_zero_contract, 437, s2038_zero_checked⟩

def s2038_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2038_positive_checked : check 440 s2038_positive_contract = true := by decide +kernel
def s2038_positive : CertifiedContract :=
  ⟨2038, 2039, 1, (.dec 5), s2038_positive_contract, 440, s2038_positive_checked⟩

def s2039_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2039_plain_checked : check 444 s2039_plain_contract = true := by decide +kernel
def s2039_plain : CertifiedContract :=
  ⟨2039, 2040, 0, (.inc 8), s2039_plain_contract, 444, s2039_plain_checked⟩

def s2040_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s2040_plain_checked : check 121 s2040_plain_contract = true := by decide +kernel
def s2040_plain : CertifiedContract :=
  ⟨2040, 2038, 0, .none, s2040_plain_contract, 121, s2040_plain_checked⟩

def s2041_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s2041_plain_checked : check 112 s2041_plain_contract = true := by decide +kernel
def s2041_plain : CertifiedContract :=
  ⟨2041, 2034, 0, .none, s2041_plain_contract, 112, s2041_plain_checked⟩

def s2042_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s2042_zero_checked : check 383 s2042_zero_contract = true := by decide +kernel
def s2042_zero : CertifiedContract :=
  ⟨2042, 2045, 0, .none, s2042_zero_contract, 383, s2042_zero_checked⟩

def s2042_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2042_positive_checked : check 386 s2042_positive_contract = true := by decide +kernel
def s2042_positive : CertifiedContract :=
  ⟨2042, 2043, 1, (.dec 5), s2042_positive_contract, 386, s2042_positive_checked⟩

def s2043_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, true, true, true] 0 (.inc 0)⟩
theorem s2043_plain_checked : check 399 s2043_plain_contract = true := by decide +kernel
def s2043_plain : CertifiedContract :=
  ⟨2043, 2044, 0, (.inc 0), s2043_plain_contract, 399, s2043_plain_checked⟩

def s2044_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, false, true, false] 0 .none⟩
theorem s2044_plain_checked : check 106 s2044_plain_contract = true := by decide +kernel
def s2044_plain : CertifiedContract :=
  ⟨2044, 2042, 0, .none, s2044_plain_contract, 106, s2044_plain_checked⟩

def s2045_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s2045_zero_checked : check 380 s2045_zero_contract = true := by decide +kernel
def s2045_zero : CertifiedContract :=
  ⟨2045, 2049, 0, .none, s2045_zero_contract, 380, s2045_zero_checked⟩

def s2045_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2045_positive_checked : check 386 s2045_positive_contract = true := by decide +kernel
def s2045_positive : CertifiedContract :=
  ⟨2045, 2046, 1, (.dec 2), s2045_positive_contract, 386, s2045_positive_checked⟩

def s2046_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2046_plain_checked : check 399 s2046_plain_contract = true := by decide +kernel
def s2046_plain : CertifiedContract :=
  ⟨2046, 2047, 0, (.inc 5), s2046_plain_contract, 399, s2046_plain_checked⟩

def s2047_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2047_plain_checked : check 426 s2047_plain_contract = true := by decide +kernel
def s2047_plain : CertifiedContract :=
  ⟨2047, 2048, 0, (.inc 8), s2047_plain_contract, 426, s2047_plain_checked⟩

def s2048_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s2048_plain_checked : check 115 s2048_plain_contract = true := by decide +kernel
def s2048_plain : CertifiedContract :=
  ⟨2048, 2045, 0, .none, s2048_plain_contract, 115, s2048_plain_checked⟩

def s2049_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s2049_zero_checked : check 401 s2049_zero_contract = true := by decide +kernel
def s2049_zero : CertifiedContract :=
  ⟨2049, 2055, 0, .none, s2049_zero_contract, 401, s2049_zero_checked⟩

def s2049_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2049_positive_checked : check 404 s2049_positive_contract = true := by decide +kernel
def s2049_positive : CertifiedContract :=
  ⟨2049, 2050, 1, (.dec 8), s2049_positive_contract, 404, s2049_positive_checked⟩

def s2050_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2050_plain_checked : check 399 s2050_plain_contract = true := by decide +kernel
def s2050_plain : CertifiedContract :=
  ⟨2050, 2051, 0, (.inc 5), s2050_plain_contract, 399, s2050_plain_checked⟩

def s2051_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s2051_zero_checked : check 419 s2051_zero_contract = true := by decide +kernel
def s2051_zero : CertifiedContract :=
  ⟨2051, 2054, 0, .none, s2051_zero_contract, 419, s2051_zero_checked⟩

def s2051_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2051_positive_checked : check 422 s2051_positive_contract = true := by decide +kernel
def s2051_positive : CertifiedContract :=
  ⟨2051, 2052, 1, (.dec 8), s2051_positive_contract, 422, s2051_positive_checked⟩

def s2052_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2052_plain_checked : check 417 s2052_plain_contract = true := by decide +kernel
def s2052_plain : CertifiedContract :=
  ⟨2052, 2053, 0, (.inc 2), s2052_plain_contract, 417, s2052_plain_checked⟩

def s2053_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2053_plain_checked : check 115 s2053_plain_contract = true := by decide +kernel
def s2053_plain : CertifiedContract :=
  ⟨2053, 2051, 0, .none, s2053_plain_contract, 115, s2053_plain_checked⟩

def s2054_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s2054_plain_checked : check 118 s2054_plain_contract = true := by decide +kernel
def s2054_plain : CertifiedContract :=
  ⟨2054, 2045, 0, .none, s2054_plain_contract, 118, s2054_plain_checked⟩

def s2055_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s2055_zero_checked : check 389 s2055_zero_contract = true := by decide +kernel
def s2055_zero : CertifiedContract :=
  ⟨2055, 2061, 0, .none, s2055_zero_contract, 389, s2055_zero_checked⟩

def s2055_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2055_positive_checked : check 386 s2055_positive_contract = true := by decide +kernel
def s2055_positive : CertifiedContract :=
  ⟨2055, 2056, 1, (.dec 5), s2055_positive_contract, 386, s2055_positive_checked⟩

def s2056_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2056_plain_checked : check 399 s2056_plain_contract = true := by decide +kernel
def s2056_plain : CertifiedContract :=
  ⟨2056, 2057, 0, (.inc 2), s2056_plain_contract, 399, s2056_plain_checked⟩

def s2057_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2057_plain_checked : check 402 s2057_plain_contract = true := by decide +kernel
def s2057_plain : CertifiedContract :=
  ⟨2057, 2058, 0, (.inc 2), s2057_plain_contract, 402, s2057_plain_checked⟩

def s2058_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2058_plain_checked : check 399 s2058_plain_contract = true := by decide +kernel
def s2058_plain : CertifiedContract :=
  ⟨2058, 2059, 0, (.inc 2), s2058_plain_contract, 399, s2058_plain_checked⟩

def s2059_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, true, true] 0 (.inc 2)⟩
theorem s2059_plain_checked : check 405 s2059_plain_contract = true := by decide +kernel
def s2059_plain : CertifiedContract :=
  ⟨2059, 2060, 0, (.inc 2), s2059_plain_contract, 405, s2059_plain_checked⟩

def s2060_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s2060_plain_checked : check 103 s2060_plain_contract = true := by decide +kernel
def s2060_plain : CertifiedContract :=
  ⟨2060, 2055, 0, .none, s2060_plain_contract, 103, s2060_plain_checked⟩

def s2061_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s2061_zero_checked : check 344 s2061_zero_contract = true := by decide +kernel
def s2061_zero : CertifiedContract :=
  ⟨2061, 2064, 0, .none, s2061_zero_contract, 344, s2061_zero_checked⟩

def s2061_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2061_positive_checked : check 350 s2061_positive_contract = true := by decide +kernel
def s2061_positive : CertifiedContract :=
  ⟨2061, 2062, 1, (.dec 2), s2061_positive_contract, 350, s2061_positive_checked⟩

def s2062_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s2062_plain_checked : check 363 s2062_plain_contract = true := by decide +kernel
def s2062_plain : CertifiedContract :=
  ⟨2062, 2063, 0, (.inc 8), s2062_plain_contract, 363, s2062_plain_checked⟩

def s2063_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s2063_plain_checked : check 94 s2063_plain_contract = true := by decide +kernel
def s2063_plain : CertifiedContract :=
  ⟨2063, 2061, 0, .none, s2063_plain_contract, 94, s2063_plain_checked⟩

def s2064_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2064_zero_checked : check 365 s2064_zero_contract = true := by decide +kernel
def s2064_zero : CertifiedContract :=
  ⟨2064, 2067, 0, .none, s2064_zero_contract, 365, s2064_zero_checked⟩

def s2064_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2064_positive_checked : check 371 s2064_positive_contract = true := by decide +kernel
def s2064_positive : CertifiedContract :=
  ⟨2064, 2065, 1, (.dec 0), s2064_positive_contract, 371, s2064_positive_checked⟩

def s2065_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2065_plain_checked : check 363 s2065_plain_contract = true := by decide +kernel
def s2065_plain : CertifiedContract :=
  ⟨2065, 2066, 0, (.inc 2), s2065_plain_contract, 363, s2065_plain_checked⟩

def s2066_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s2066_plain_checked : check 97 s2066_plain_contract = true := by decide +kernel
def s2066_plain : CertifiedContract :=
  ⟨2066, 2064, 0, .none, s2066_plain_contract, 97, s2066_plain_checked⟩

def s2067_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2067_zero_checked : check 371 s2067_zero_contract = true := by decide +kernel
def s2067_zero : CertifiedContract :=
  ⟨2067, 2071, 0, .none, s2067_zero_contract, 371, s2067_zero_checked⟩

def s2067_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2067_positive_checked : check 377 s2067_positive_contract = true := by decide +kernel
def s2067_positive : CertifiedContract :=
  ⟨2067, 2068, 1, (.dec 2), s2067_positive_contract, 377, s2067_positive_checked⟩

def s2068_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2068_plain_checked : check 390 s2068_plain_contract = true := by decide +kernel
def s2068_plain : CertifiedContract :=
  ⟨2068, 2069, 0, (.inc 5), s2068_plain_contract, 390, s2068_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s2019_plain,
  s2020_plain,
  s2021_plain,
  s2022_zero,
  s2022_positive,
  s2023_plain,
  s2024_zero,
  s2024_positive,
  s2025_plain,
  s2026_plain,
  s2027_plain,
  s2028_zero,
  s2028_positive,
  s2029_plain,
  s2030_plain,
  s2031_plain,
  s2032_plain,
  s2033_plain,
  s2034_zero,
  s2034_positive,
  s2035_plain,
  s2036_zero,
  s2036_positive,
  s2037_plain,
  s2038_zero,
  s2038_positive,
  s2039_plain,
  s2040_plain,
  s2041_plain,
  s2042_zero,
  s2042_positive,
  s2043_plain,
  s2044_plain,
  s2045_zero,
  s2045_positive,
  s2046_plain,
  s2047_plain,
  s2048_plain,
  s2049_zero,
  s2049_positive,
  s2050_plain,
  s2051_zero,
  s2051_positive,
  s2052_plain,
  s2053_plain,
  s2054_plain,
  s2055_zero,
  s2055_positive,
  s2056_plain,
  s2057_plain,
  s2058_plain,
  s2059_plain,
  s2060_plain,
  s2061_zero,
  s2061_positive,
  s2062_plain,
  s2063_plain,
  s2064_zero,
  s2064_positive,
  s2065_plain,
  s2066_plain,
  s2067_zero,
  s2067_positive,
  s2068_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S041
