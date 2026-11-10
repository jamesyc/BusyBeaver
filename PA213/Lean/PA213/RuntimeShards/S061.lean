import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S061
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s3005_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3005_positive_checked : check 404 s3005_positive_contract = true := by decide +kernel
def s3005_positive : CertifiedContract :=
  ⟨3005, 3006, 1, (.dec 8), s3005_positive_contract, 404, s3005_positive_checked⟩

def s3006_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3006_plain_checked : check 399 s3006_plain_contract = true := by decide +kernel
def s3006_plain : CertifiedContract :=
  ⟨3006, 3007, 0, (.inc 2), s3006_plain_contract, 399, s3006_plain_checked⟩

def s3007_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3007_plain_checked : check 109 s3007_plain_contract = true := by decide +kernel
def s3007_plain : CertifiedContract :=
  ⟨3007, 3005, 0, .none, s3007_plain_contract, 109, s3007_plain_checked⟩

def s3008_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s3008_plain_checked : check 112 s3008_plain_contract = true := by decide +kernel
def s3008_plain : CertifiedContract :=
  ⟨3008, 2999, 0, .none, s3008_plain_contract, 112, s3008_plain_checked⟩

def s3009_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, true] 0 .none⟩
theorem s3009_zero_checked : check 368 s3009_zero_contract = true := by decide +kernel
def s3009_zero : CertifiedContract :=
  ⟨3009, 3015, 0, .none, s3009_zero_contract, 368, s3009_zero_checked⟩

def s3009_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3009_positive_checked : check 368 s3009_positive_contract = true := by decide +kernel
def s3009_positive : CertifiedContract :=
  ⟨3009, 3010, 1, (.dec 5), s3009_positive_contract, 368, s3009_positive_checked⟩

def s3010_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3010_plain_checked : check 381 s3010_plain_contract = true := by decide +kernel
def s3010_plain : CertifiedContract :=
  ⟨3010, 3011, 0, (.inc 2), s3010_plain_contract, 381, s3010_plain_checked⟩

def s3011_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3011_plain_checked : check 384 s3011_plain_contract = true := by decide +kernel
def s3011_plain : CertifiedContract :=
  ⟨3011, 3012, 0, (.inc 2), s3011_plain_contract, 384, s3011_plain_checked⟩

def s3012_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3012_plain_checked : check 381 s3012_plain_contract = true := by decide +kernel
def s3012_plain : CertifiedContract :=
  ⟨3012, 3013, 0, (.inc 2), s3012_plain_contract, 381, s3012_plain_checked⟩

def s3013_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s3013_plain_checked : check 387 s3013_plain_contract = true := by decide +kernel
def s3013_plain : CertifiedContract :=
  ⟨3013, 3014, 0, (.inc 2), s3013_plain_contract, 387, s3013_plain_checked⟩

def s3014_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s3014_plain_checked : check 97 s3014_plain_contract = true := by decide +kernel
def s3014_plain : CertifiedContract :=
  ⟨3014, 3009, 0, .none, s3014_plain_contract, 97, s3014_plain_checked⟩

def s3015_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, false, false] 0 (.inc 2)⟩
theorem s3015_plain_checked : check 342 s3015_plain_contract = true := by decide +kernel
def s3015_plain : CertifiedContract :=
  ⟨3015, 3016, 0, (.inc 2), s3015_plain_contract, 342, s3015_plain_checked⟩

def s3016_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, false, false] 0 .none⟩
theorem s3016_zero_checked : check 335 s3016_zero_contract = true := by decide +kernel
def s3016_zero : CertifiedContract :=
  ⟨3016, 3019, 0, .none, s3016_zero_contract, 335, s3016_zero_checked⟩

def s3016_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3016_positive_checked : check 341 s3016_positive_contract = true := by decide +kernel
def s3016_positive : CertifiedContract :=
  ⟨3016, 3017, 1, (.dec 2), s3016_positive_contract, 341, s3016_positive_checked⟩

def s3017_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, false, true, true] 0 (.inc 8)⟩
theorem s3017_plain_checked : check 354 s3017_plain_contract = true := by decide +kernel
def s3017_plain : CertifiedContract :=
  ⟨3017, 3018, 0, (.inc 8), s3017_plain_contract, 354, s3017_plain_checked⟩

def s3018_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s3018_plain_checked : check 91 s3018_plain_contract = true := by decide +kernel
def s3018_plain : CertifiedContract :=
  ⟨3018, 3016, 0, .none, s3018_plain_contract, 91, s3018_plain_checked⟩

def s3019_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s3019_zero_checked : check 356 s3019_zero_contract = true := by decide +kernel
def s3019_zero : CertifiedContract :=
  ⟨3019, 3022, 0, .none, s3019_zero_contract, 356, s3019_zero_checked⟩

def s3019_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s3019_positive_checked : check 362 s3019_positive_contract = true := by decide +kernel
def s3019_positive : CertifiedContract :=
  ⟨3019, 3020, 1, (.dec 0), s3019_positive_contract, 362, s3019_positive_checked⟩

def s3020_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s3020_plain_checked : check 354 s3020_plain_contract = true := by decide +kernel
def s3020_plain : CertifiedContract :=
  ⟨3020, 3021, 0, (.inc 2), s3020_plain_contract, 354, s3020_plain_checked⟩

def s3021_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, false, false] 0 .none⟩
theorem s3021_plain_checked : check 94 s3021_plain_contract = true := by decide +kernel
def s3021_plain : CertifiedContract :=
  ⟨3021, 3019, 0, .none, s3021_plain_contract, 94, s3021_plain_checked⟩

def s3022_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3022_zero_checked : check 362 s3022_zero_contract = true := by decide +kernel
def s3022_zero : CertifiedContract :=
  ⟨3022, 3026, 0, .none, s3022_zero_contract, 362, s3022_zero_checked⟩

def s3022_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3022_positive_checked : check 368 s3022_positive_contract = true := by decide +kernel
def s3022_positive : CertifiedContract :=
  ⟨3022, 3023, 1, (.dec 2), s3022_positive_contract, 368, s3022_positive_checked⟩

def s3023_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3023_plain_checked : check 381 s3023_plain_contract = true := by decide +kernel
def s3023_plain : CertifiedContract :=
  ⟨3023, 3024, 0, (.inc 5), s3023_plain_contract, 381, s3023_plain_checked⟩

def s3024_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3024_plain_checked : check 408 s3024_plain_contract = true := by decide +kernel
def s3024_plain : CertifiedContract :=
  ⟨3024, 3025, 0, (.inc 8), s3024_plain_contract, 408, s3024_plain_checked⟩

def s3025_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s3025_plain_checked : check 109 s3025_plain_contract = true := by decide +kernel
def s3025_plain : CertifiedContract :=
  ⟨3025, 3022, 0, .none, s3025_plain_contract, 109, s3025_plain_checked⟩

def s3026_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s3026_zero_checked : check 383 s3026_zero_contract = true := by decide +kernel
def s3026_zero : CertifiedContract :=
  ⟨3026, 3032, 0, .none, s3026_zero_contract, 383, s3026_zero_checked⟩

def s3026_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3026_positive_checked : check 386 s3026_positive_contract = true := by decide +kernel
def s3026_positive : CertifiedContract :=
  ⟨3026, 3027, 1, (.dec 8), s3026_positive_contract, 386, s3026_positive_checked⟩

def s3027_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3027_plain_checked : check 381 s3027_plain_contract = true := by decide +kernel
def s3027_plain : CertifiedContract :=
  ⟨3027, 3028, 0, (.inc 5), s3027_plain_contract, 381, s3027_plain_checked⟩

def s3028_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s3028_zero_checked : check 401 s3028_zero_contract = true := by decide +kernel
def s3028_zero : CertifiedContract :=
  ⟨3028, 3031, 0, .none, s3028_zero_contract, 401, s3028_zero_checked⟩

def s3028_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3028_positive_checked : check 404 s3028_positive_contract = true := by decide +kernel
def s3028_positive : CertifiedContract :=
  ⟨3028, 3029, 1, (.dec 8), s3028_positive_contract, 404, s3028_positive_checked⟩

def s3029_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3029_plain_checked : check 399 s3029_plain_contract = true := by decide +kernel
def s3029_plain : CertifiedContract :=
  ⟨3029, 3030, 0, (.inc 2), s3029_plain_contract, 399, s3029_plain_checked⟩

def s3030_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3030_plain_checked : check 109 s3030_plain_contract = true := by decide +kernel
def s3030_plain : CertifiedContract :=
  ⟨3030, 3028, 0, .none, s3030_plain_contract, 109, s3030_plain_checked⟩

def s3031_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s3031_plain_checked : check 112 s3031_plain_contract = true := by decide +kernel
def s3031_plain : CertifiedContract :=
  ⟨3031, 3022, 0, .none, s3031_plain_contract, 112, s3031_plain_checked⟩

def s3032_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, true, false, false] 0 .none⟩
theorem s3032_zero_checked : check 371 s3032_zero_contract = true := by decide +kernel
def s3032_zero : CertifiedContract :=
  ⟨3032, 3035, 0, .none, s3032_zero_contract, 371, s3032_zero_checked⟩

def s3032_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s3032_positive_checked : check 368 s3032_positive_contract = true := by decide +kernel
def s3032_positive : CertifiedContract :=
  ⟨3032, 3033, 1, (.dec 5), s3032_positive_contract, 368, s3032_positive_checked⟩

def s3033_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s3033_plain_checked : check 381 s3033_plain_contract = true := by decide +kernel
def s3033_plain : CertifiedContract :=
  ⟨3033, 3034, 0, (.inc 0), s3033_plain_contract, 381, s3033_plain_checked⟩

def s3034_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s3034_plain_checked : check 100 s3034_plain_contract = true := by decide +kernel
def s3034_plain : CertifiedContract :=
  ⟨3034, 3032, 0, .none, s3034_plain_contract, 100, s3034_plain_checked⟩

def s3035_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, true, true, false] 0 .none⟩
theorem s3035_zero_checked : check 335 s3035_zero_contract = true := by decide +kernel
def s3035_zero : CertifiedContract :=
  ⟨3035, 3039, 0, .none, s3035_zero_contract, 335, s3035_zero_checked⟩

def s3035_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, true, false, true, false] 1 (.dec 4)⟩
theorem s3035_positive_checked : check 341 s3035_positive_contract = true := by decide +kernel
def s3035_positive : CertifiedContract :=
  ⟨3035, 3036, 1, (.dec 4), s3035_positive_contract, 341, s3035_positive_checked⟩

def s3036_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s3036_plain_checked : check 354 s3036_plain_contract = true := by decide +kernel
def s3036_plain : CertifiedContract :=
  ⟨3036, 3037, 0, (.inc 2), s3036_plain_contract, 354, s3036_plain_checked⟩

def s3037_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3037_plain_checked : check 381 s3037_plain_contract = true := by decide +kernel
def s3037_plain : CertifiedContract :=
  ⟨3037, 3038, 0, (.inc 8), s3037_plain_contract, 381, s3037_plain_checked⟩

def s3038_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, true, false, false] 0 .none⟩
theorem s3038_plain_checked : check 100 s3038_plain_contract = true := by decide +kernel
def s3038_plain : CertifiedContract :=
  ⟨3038, 3035, 0, .none, s3038_plain_contract, 100, s3038_plain_checked⟩

def s3039_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s3039_zero_checked : check 347 s3039_zero_contract = true := by decide +kernel
def s3039_zero : CertifiedContract :=
  ⟨3039, 3042, 0, .none, s3039_zero_contract, 347, s3039_zero_checked⟩

def s3039_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, true, true, true, false] 1 (.dec 8)⟩
theorem s3039_positive_checked : check 341 s3039_positive_contract = true := by decide +kernel
def s3039_positive : CertifiedContract :=
  ⟨3039, 3040, 1, (.dec 8), s3039_positive_contract, 341, s3039_positive_checked⟩

def s3040_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, true, true, true, true] 0 (.inc 4)⟩
theorem s3040_plain_checked : check 345 s3040_plain_contract = true := by decide +kernel
def s3040_plain : CertifiedContract :=
  ⟨3040, 3041, 0, (.inc 4), s3040_plain_contract, 345, s3040_plain_checked⟩

def s3041_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, true, true, false] 0 .none⟩
theorem s3041_plain_checked : check 91 s3041_plain_contract = true := by decide +kernel
def s3041_plain : CertifiedContract :=
  ⟨3041, 3039, 0, .none, s3041_plain_contract, 91, s3041_plain_checked⟩

def s3042_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s3042_zero_checked : check 344 s3042_zero_contract = true := by decide +kernel
def s3042_zero : CertifiedContract :=
  ⟨3042, 3045, 0, .none, s3042_zero_contract, 344, s3042_zero_checked⟩

def s3042_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s3042_positive_checked : check 350 s3042_positive_contract = true := by decide +kernel
def s3042_positive : CertifiedContract :=
  ⟨3042, 3043, 1, (.dec 2), s3042_positive_contract, 350, s3042_positive_checked⟩

def s3043_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s3043_plain_checked : check 363 s3043_plain_contract = true := by decide +kernel
def s3043_plain : CertifiedContract :=
  ⟨3043, 3044, 0, (.inc 8), s3043_plain_contract, 363, s3043_plain_checked⟩

def s3044_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s3044_plain_checked : check 94 s3044_plain_contract = true := by decide +kernel
def s3044_plain : CertifiedContract :=
  ⟨3044, 3042, 0, .none, s3044_plain_contract, 94, s3044_plain_checked⟩

def s3045_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s3045_zero_checked : check 365 s3045_zero_contract = true := by decide +kernel
def s3045_zero : CertifiedContract :=
  ⟨3045, 3048, 0, .none, s3045_zero_contract, 365, s3045_zero_checked⟩

def s3045_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s3045_positive_checked : check 371 s3045_positive_contract = true := by decide +kernel
def s3045_positive : CertifiedContract :=
  ⟨3045, 3046, 1, (.dec 0), s3045_positive_contract, 371, s3045_positive_checked⟩

def s3046_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s3046_plain_checked : check 363 s3046_plain_contract = true := by decide +kernel
def s3046_plain : CertifiedContract :=
  ⟨3046, 3047, 0, (.inc 2), s3046_plain_contract, 363, s3046_plain_checked⟩

def s3047_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s3047_plain_checked : check 97 s3047_plain_contract = true := by decide +kernel
def s3047_plain : CertifiedContract :=
  ⟨3047, 3045, 0, .none, s3047_plain_contract, 97, s3047_plain_checked⟩

def s3048_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3048_zero_checked : check 371 s3048_zero_contract = true := by decide +kernel
def s3048_zero : CertifiedContract :=
  ⟨3048, 3052, 0, .none, s3048_zero_contract, 371, s3048_zero_checked⟩

def s3048_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3048_positive_checked : check 377 s3048_positive_contract = true := by decide +kernel
def s3048_positive : CertifiedContract :=
  ⟨3048, 3049, 1, (.dec 2), s3048_positive_contract, 377, s3048_positive_checked⟩

def s3049_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3049_plain_checked : check 390 s3049_plain_contract = true := by decide +kernel
def s3049_plain : CertifiedContract :=
  ⟨3049, 3050, 0, (.inc 5), s3049_plain_contract, 390, s3049_plain_checked⟩

def s3050_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3050_plain_checked : check 417 s3050_plain_contract = true := by decide +kernel
def s3050_plain : CertifiedContract :=
  ⟨3050, 3051, 0, (.inc 8), s3050_plain_contract, 417, s3050_plain_checked⟩

def s3051_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s3051_plain_checked : check 112 s3051_plain_contract = true := by decide +kernel
def s3051_plain : CertifiedContract :=
  ⟨3051, 3048, 0, .none, s3051_plain_contract, 112, s3051_plain_checked⟩

def s3052_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s3052_zero_checked : check 392 s3052_zero_contract = true := by decide +kernel
def s3052_zero : CertifiedContract :=
  ⟨3052, 3058, 0, .none, s3052_zero_contract, 392, s3052_zero_checked⟩

def s3052_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3052_positive_checked : check 395 s3052_positive_contract = true := by decide +kernel
def s3052_positive : CertifiedContract :=
  ⟨3052, 3053, 1, (.dec 8), s3052_positive_contract, 395, s3052_positive_checked⟩

def s3053_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3053_plain_checked : check 390 s3053_plain_contract = true := by decide +kernel
def s3053_plain : CertifiedContract :=
  ⟨3053, 3054, 0, (.inc 5), s3053_plain_contract, 390, s3053_plain_checked⟩

def s3054_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s3054_zero_checked : check 410 s3054_zero_contract = true := by decide +kernel
def s3054_zero : CertifiedContract :=
  ⟨3054, 3057, 0, .none, s3054_zero_contract, 410, s3054_zero_checked⟩

def s3054_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3054_positive_checked : check 413 s3054_positive_contract = true := by decide +kernel
def s3054_positive : CertifiedContract :=
  ⟨3054, 3055, 1, (.dec 8), s3054_positive_contract, 413, s3054_positive_checked⟩

def nonterminal : Array CertifiedContract := #[
  s3005_positive,
  s3006_plain,
  s3007_plain,
  s3008_plain,
  s3009_zero,
  s3009_positive,
  s3010_plain,
  s3011_plain,
  s3012_plain,
  s3013_plain,
  s3014_plain,
  s3015_plain,
  s3016_zero,
  s3016_positive,
  s3017_plain,
  s3018_plain,
  s3019_zero,
  s3019_positive,
  s3020_plain,
  s3021_plain,
  s3022_zero,
  s3022_positive,
  s3023_plain,
  s3024_plain,
  s3025_plain,
  s3026_zero,
  s3026_positive,
  s3027_plain,
  s3028_zero,
  s3028_positive,
  s3029_plain,
  s3030_plain,
  s3031_plain,
  s3032_zero,
  s3032_positive,
  s3033_plain,
  s3034_plain,
  s3035_zero,
  s3035_positive,
  s3036_plain,
  s3037_plain,
  s3038_plain,
  s3039_zero,
  s3039_positive,
  s3040_plain,
  s3041_plain,
  s3042_zero,
  s3042_positive,
  s3043_plain,
  s3044_plain,
  s3045_zero,
  s3045_positive,
  s3046_plain,
  s3047_plain,
  s3048_zero,
  s3048_positive,
  s3049_plain,
  s3050_plain,
  s3051_plain,
  s3052_zero,
  s3052_positive,
  s3053_plain,
  s3054_zero,
  s3054_positive
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S061
