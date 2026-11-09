module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S059
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s2908_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, true, true, true] 0 (.inc 4)⟩
theorem s2908_plain_checked : check 346 s2908_plain_contract = true := by decide +kernel
def s2908_plain : CertifiedContract :=
  ⟨2908, 2909, 0, (.inc 4), s2908_plain_contract, 346, s2908_plain_checked⟩

def s2909_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s2909_plain_checked : check 92 s2909_plain_contract = true := by decide +kernel
def s2909_plain : CertifiedContract :=
  ⟨2909, 2907, 0, .none, s2909_plain_contract, 92, s2909_plain_checked⟩

def s2910_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s2910_zero_checked : check 336 s2910_zero_contract = true := by decide +kernel
def s2910_zero : CertifiedContract :=
  ⟨2910, 2913, 0, .none, s2910_zero_contract, 336, s2910_zero_checked⟩

def s2910_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2910_positive_checked : check 342 s2910_positive_contract = true := by decide +kernel
def s2910_positive : CertifiedContract :=
  ⟨2910, 2911, 1, (.dec 2), s2910_positive_contract, 342, s2910_positive_checked⟩

def s2911_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s2911_plain_checked : check 355 s2911_plain_contract = true := by decide +kernel
def s2911_plain : CertifiedContract :=
  ⟨2911, 2912, 0, (.inc 8), s2911_plain_contract, 355, s2911_plain_checked⟩

def s2912_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s2912_plain_checked : check 92 s2912_plain_contract = true := by decide +kernel
def s2912_plain : CertifiedContract :=
  ⟨2912, 2910, 0, .none, s2912_plain_contract, 92, s2912_plain_checked⟩

def s2913_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2913_zero_checked : check 357 s2913_zero_contract = true := by decide +kernel
def s2913_zero : CertifiedContract :=
  ⟨2913, 2916, 0, .none, s2913_zero_contract, 357, s2913_zero_checked⟩

def s2913_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2913_positive_checked : check 363 s2913_positive_contract = true := by decide +kernel
def s2913_positive : CertifiedContract :=
  ⟨2913, 2914, 1, (.dec 0), s2913_positive_contract, 363, s2913_positive_checked⟩

def s2914_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2914_plain_checked : check 355 s2914_plain_contract = true := by decide +kernel
def s2914_plain : CertifiedContract :=
  ⟨2914, 2915, 0, (.inc 2), s2914_plain_contract, 355, s2914_plain_checked⟩

def s2915_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s2915_plain_checked : check 95 s2915_plain_contract = true := by decide +kernel
def s2915_plain : CertifiedContract :=
  ⟨2915, 2913, 0, .none, s2915_plain_contract, 95, s2915_plain_checked⟩

def s2916_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2916_zero_checked : check 363 s2916_zero_contract = true := by decide +kernel
def s2916_zero : CertifiedContract :=
  ⟨2916, 2920, 0, .none, s2916_zero_contract, 363, s2916_zero_checked⟩

def s2916_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2916_positive_checked : check 369 s2916_positive_contract = true := by decide +kernel
def s2916_positive : CertifiedContract :=
  ⟨2916, 2917, 1, (.dec 2), s2916_positive_contract, 369, s2916_positive_checked⟩

def s2917_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2917_plain_checked : check 382 s2917_plain_contract = true := by decide +kernel
def s2917_plain : CertifiedContract :=
  ⟨2917, 2918, 0, (.inc 5), s2917_plain_contract, 382, s2917_plain_checked⟩

def s2918_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2918_plain_checked : check 409 s2918_plain_contract = true := by decide +kernel
def s2918_plain : CertifiedContract :=
  ⟨2918, 2919, 0, (.inc 8), s2918_plain_contract, 409, s2918_plain_checked⟩

def s2919_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2919_plain_checked : check 110 s2919_plain_contract = true := by decide +kernel
def s2919_plain : CertifiedContract :=
  ⟨2919, 2916, 0, .none, s2919_plain_contract, 110, s2919_plain_checked⟩

def s2920_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s2920_zero_checked : check 384 s2920_zero_contract = true := by decide +kernel
def s2920_zero : CertifiedContract :=
  ⟨2920, 2926, 0, .none, s2920_zero_contract, 384, s2920_zero_checked⟩

def s2920_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2920_positive_checked : check 387 s2920_positive_contract = true := by decide +kernel
def s2920_positive : CertifiedContract :=
  ⟨2920, 2921, 1, (.dec 8), s2920_positive_contract, 387, s2920_positive_checked⟩

def s2921_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2921_plain_checked : check 382 s2921_plain_contract = true := by decide +kernel
def s2921_plain : CertifiedContract :=
  ⟨2921, 2922, 0, (.inc 5), s2921_plain_contract, 382, s2921_plain_checked⟩

def s2922_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s2922_zero_checked : check 402 s2922_zero_contract = true := by decide +kernel
def s2922_zero : CertifiedContract :=
  ⟨2922, 2925, 0, .none, s2922_zero_contract, 402, s2922_zero_checked⟩

def s2922_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2922_positive_checked : check 405 s2922_positive_contract = true := by decide +kernel
def s2922_positive : CertifiedContract :=
  ⟨2922, 2923, 1, (.dec 8), s2922_positive_contract, 405, s2922_positive_checked⟩

def s2923_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2923_plain_checked : check 400 s2923_plain_contract = true := by decide +kernel
def s2923_plain : CertifiedContract :=
  ⟨2923, 2924, 0, (.inc 2), s2923_plain_contract, 400, s2923_plain_checked⟩

def s2924_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2924_plain_checked : check 110 s2924_plain_contract = true := by decide +kernel
def s2924_plain : CertifiedContract :=
  ⟨2924, 2922, 0, .none, s2924_plain_contract, 110, s2924_plain_checked⟩

def s2925_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2925_plain_checked : check 113 s2925_plain_contract = true := by decide +kernel
def s2925_plain : CertifiedContract :=
  ⟨2925, 2916, 0, .none, s2925_plain_contract, 113, s2925_plain_checked⟩

def s2926_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s2926_zero_checked : check 372 s2926_zero_contract = true := by decide +kernel
def s2926_zero : CertifiedContract :=
  ⟨2926, 2929, 0, .none, s2926_zero_contract, 372, s2926_zero_checked⟩

def s2926_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2926_positive_checked : check 369 s2926_positive_contract = true := by decide +kernel
def s2926_positive : CertifiedContract :=
  ⟨2926, 2927, 1, (.dec 5), s2926_positive_contract, 369, s2926_positive_checked⟩

def s2927_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2927_plain_checked : check 382 s2927_plain_contract = true := by decide +kernel
def s2927_plain : CertifiedContract :=
  ⟨2927, 2928, 0, (.inc 0), s2927_plain_contract, 382, s2927_plain_checked⟩

def s2928_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s2928_plain_checked : check 101 s2928_plain_contract = true := by decide +kernel
def s2928_plain : CertifiedContract :=
  ⟨2928, 2926, 0, .none, s2928_plain_contract, 101, s2928_plain_checked⟩

def s2929_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s2929_zero_checked : check 336 s2929_zero_contract = true := by decide +kernel
def s2929_zero : CertifiedContract :=
  ⟨2929, 2933, 0, .none, s2929_zero_contract, 336, s2929_zero_checked⟩

def s2929_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s2929_positive_checked : check 342 s2929_positive_contract = true := by decide +kernel
def s2929_positive : CertifiedContract :=
  ⟨2929, 2930, 1, (.dec 7), s2929_positive_contract, 342, s2929_positive_checked⟩

def s2930_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2930_plain_checked : check 346 s2930_plain_contract = true := by decide +kernel
def s2930_plain : CertifiedContract :=
  ⟨2930, 2931, 0, (.inc 2), s2930_plain_contract, 346, s2930_plain_checked⟩

def s2931_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2931_plain_checked : check 373 s2931_plain_contract = true := by decide +kernel
def s2931_plain : CertifiedContract :=
  ⟨2931, 2932, 0, (.inc 8), s2931_plain_contract, 373, s2931_plain_checked⟩

def s2932_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s2932_plain_checked : check 98 s2932_plain_contract = true := by decide +kernel
def s2932_plain : CertifiedContract :=
  ⟨2932, 2929, 0, .none, s2932_plain_contract, 98, s2932_plain_checked⟩

def s2933_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, false, false] 0 .none⟩
theorem s2933_zero_checked : check 345 s2933_zero_contract = true := by decide +kernel
def s2933_zero : CertifiedContract :=
  ⟨2933, 2936, 0, .none, s2933_zero_contract, 345, s2933_zero_checked⟩

def s2933_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s2933_positive_checked : check 342 s2933_positive_contract = true := by decide +kernel
def s2933_positive : CertifiedContract :=
  ⟨2933, 2934, 1, (.dec 8), s2933_positive_contract, 342, s2933_positive_checked⟩

def s2934_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s2934_plain_checked : check 373 s2934_plain_contract = true := by decide +kernel
def s2934_plain : CertifiedContract :=
  ⟨2934, 2935, 0, (.inc 7), s2934_plain_contract, 373, s2934_plain_checked⟩

def s2935_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s2935_plain_checked : check 92 s2935_plain_contract = true := by decide +kernel
def s2935_plain : CertifiedContract :=
  ⟨2935, 2933, 0, .none, s2935_plain_contract, 92, s2935_plain_checked⟩

def s2936_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s2936_zero_checked : check 345 s2936_zero_contract = true := by decide +kernel
def s2936_zero : CertifiedContract :=
  ⟨2936, 2939, 0, .none, s2936_zero_contract, 345, s2936_zero_checked⟩

def s2936_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s2936_positive_checked : check 351 s2936_positive_contract = true := by decide +kernel
def s2936_positive : CertifiedContract :=
  ⟨2936, 2937, 1, (.dec 2), s2936_positive_contract, 351, s2936_positive_checked⟩

def s2937_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s2937_plain_checked : check 364 s2937_plain_contract = true := by decide +kernel
def s2937_plain : CertifiedContract :=
  ⟨2937, 2938, 0, (.inc 8), s2937_plain_contract, 364, s2937_plain_checked⟩

def s2938_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, false, false] 0 .none⟩
theorem s2938_plain_checked : check 95 s2938_plain_contract = true := by decide +kernel
def s2938_plain : CertifiedContract :=
  ⟨2938, 2936, 0, .none, s2938_plain_contract, 95, s2938_plain_checked⟩

def s2939_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2939_zero_checked : check 366 s2939_zero_contract = true := by decide +kernel
def s2939_zero : CertifiedContract :=
  ⟨2939, 2942, 0, .none, s2939_zero_contract, 366, s2939_zero_checked⟩

def s2939_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2939_positive_checked : check 372 s2939_positive_contract = true := by decide +kernel
def s2939_positive : CertifiedContract :=
  ⟨2939, 2940, 1, (.dec 0), s2939_positive_contract, 372, s2939_positive_checked⟩

def s2940_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2940_plain_checked : check 364 s2940_plain_contract = true := by decide +kernel
def s2940_plain : CertifiedContract :=
  ⟨2940, 2941, 0, (.inc 2), s2940_plain_contract, 364, s2940_plain_checked⟩

def s2941_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s2941_plain_checked : check 98 s2941_plain_contract = true := by decide +kernel
def s2941_plain : CertifiedContract :=
  ⟨2941, 2939, 0, .none, s2941_plain_contract, 98, s2941_plain_checked⟩

def s2942_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2942_zero_checked : check 372 s2942_zero_contract = true := by decide +kernel
def s2942_zero : CertifiedContract :=
  ⟨2942, 2946, 0, .none, s2942_zero_contract, 372, s2942_zero_checked⟩

def s2942_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2942_positive_checked : check 378 s2942_positive_contract = true := by decide +kernel
def s2942_positive : CertifiedContract :=
  ⟨2942, 2943, 1, (.dec 2), s2942_positive_contract, 378, s2942_positive_checked⟩

def s2943_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2943_plain_checked : check 391 s2943_plain_contract = true := by decide +kernel
def s2943_plain : CertifiedContract :=
  ⟨2943, 2944, 0, (.inc 5), s2943_plain_contract, 391, s2943_plain_checked⟩

def s2944_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2944_plain_checked : check 418 s2944_plain_contract = true := by decide +kernel
def s2944_plain : CertifiedContract :=
  ⟨2944, 2945, 0, (.inc 8), s2944_plain_contract, 418, s2944_plain_checked⟩

def s2945_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2945_plain_checked : check 113 s2945_plain_contract = true := by decide +kernel
def s2945_plain : CertifiedContract :=
  ⟨2945, 2942, 0, .none, s2945_plain_contract, 113, s2945_plain_checked⟩

def s2946_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, true, false] 0 .none⟩
theorem s2946_zero_checked : check 393 s2946_zero_contract = true := by decide +kernel
def s2946_zero : CertifiedContract :=
  ⟨2946, 2952, 0, .none, s2946_zero_contract, 393, s2946_zero_checked⟩

def s2946_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2946_positive_checked : check 396 s2946_positive_contract = true := by decide +kernel
def s2946_positive : CertifiedContract :=
  ⟨2946, 2947, 1, (.dec 8), s2946_positive_contract, 396, s2946_positive_checked⟩

def s2947_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2947_plain_checked : check 391 s2947_plain_contract = true := by decide +kernel
def s2947_plain : CertifiedContract :=
  ⟨2947, 2948, 0, (.inc 5), s2947_plain_contract, 391, s2947_plain_checked⟩

def s2948_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s2948_zero_checked : check 411 s2948_zero_contract = true := by decide +kernel
def s2948_zero : CertifiedContract :=
  ⟨2948, 2951, 0, .none, s2948_zero_contract, 411, s2948_zero_checked⟩

def s2948_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2948_positive_checked : check 414 s2948_positive_contract = true := by decide +kernel
def s2948_positive : CertifiedContract :=
  ⟨2948, 2949, 1, (.dec 8), s2948_positive_contract, 414, s2948_positive_checked⟩

def s2949_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2949_plain_checked : check 409 s2949_plain_contract = true := by decide +kernel
def s2949_plain : CertifiedContract :=
  ⟨2949, 2950, 0, (.inc 2), s2949_plain_contract, 409, s2949_plain_checked⟩

def s2950_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2950_plain_checked : check 113 s2950_plain_contract = true := by decide +kernel
def s2950_plain : CertifiedContract :=
  ⟨2950, 2948, 0, .none, s2950_plain_contract, 113, s2950_plain_checked⟩

def s2951_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2951_plain_checked : check 116 s2951_plain_contract = true := by decide +kernel
def s2951_plain : CertifiedContract :=
  ⟨2951, 2942, 0, .none, s2951_plain_contract, 116, s2951_plain_checked⟩

def s2952_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false] 0 .none⟩
theorem s2952_zero_checked : check 381 s2952_zero_contract = true := by decide +kernel
def s2952_zero : CertifiedContract :=
  ⟨2952, 2955, 0, .none, s2952_zero_contract, 381, s2952_zero_checked⟩

def s2952_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2952_positive_checked : check 378 s2952_positive_contract = true := by decide +kernel
def s2952_positive : CertifiedContract :=
  ⟨2952, 2953, 1, (.dec 5), s2952_positive_contract, 378, s2952_positive_checked⟩

def s2953_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2953_plain_checked : check 391 s2953_plain_contract = true := by decide +kernel
def s2953_plain : CertifiedContract :=
  ⟨2953, 2954, 0, (.inc 0), s2953_plain_contract, 391, s2953_plain_checked⟩

def s2954_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, true, false] 0 .none⟩
theorem s2954_plain_checked : check 104 s2954_plain_contract = true := by decide +kernel
def s2954_plain : CertifiedContract :=
  ⟨2954, 2952, 0, .none, s2954_plain_contract, 104, s2954_plain_checked⟩

def s2955_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, false] 0 .none⟩
theorem s2955_zero_checked : check 345 s2955_zero_contract = true := by decide +kernel
def s2955_zero : CertifiedContract :=
  ⟨2955, 2959, 0, .none, s2955_zero_contract, 345, s2955_zero_checked⟩

def s2955_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, false] 1 (.dec 3)⟩
theorem s2955_positive_checked : check 351 s2955_positive_contract = true := by decide +kernel
def s2955_positive : CertifiedContract :=
  ⟨2955, 2956, 1, (.dec 3), s2955_positive_contract, 351, s2955_positive_checked⟩

def s2956_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2956_plain_checked : check 364 s2956_plain_contract = true := by decide +kernel
def s2956_plain : CertifiedContract :=
  ⟨2956, 2957, 0, (.inc 2), s2956_plain_contract, 364, s2956_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S059
