module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S060
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s2957_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2957_plain_checked : check 399 s2957_plain_contract = true := by decide +kernel
def s2957_plain : CertifiedContract :=
  ⟨2957, 2958, 0, (.inc 8), s2957_plain_contract, 399, s2957_plain_checked⟩

def s2958_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s2958_plain_checked : check 106 s2958_plain_contract = true := by decide +kernel
def s2958_plain : CertifiedContract :=
  ⟨2958, 2955, 0, .none, s2958_plain_contract, 106, s2958_plain_checked⟩

def s2959_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s2959_zero_checked : check 359 s2959_zero_contract = true := by decide +kernel
def s2959_zero : CertifiedContract :=
  ⟨2959, 2962, 0, .none, s2959_zero_contract, 359, s2959_zero_checked⟩

def s2959_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s2959_positive_checked : check 359 s2959_positive_contract = true := by decide +kernel
def s2959_positive : CertifiedContract :=
  ⟨2959, 2960, 1, (.dec 8), s2959_positive_contract, 359, s2959_positive_checked⟩

def s2960_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, true, true] 0 (.inc 3)⟩
theorem s2960_plain_checked : check 375 s2960_plain_contract = true := by decide +kernel
def s2960_plain : CertifiedContract :=
  ⟨2960, 2961, 0, (.inc 3), s2960_plain_contract, 375, s2960_plain_checked⟩

def s2961_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s2961_plain_checked : check 97 s2961_plain_contract = true := by decide +kernel
def s2961_plain : CertifiedContract :=
  ⟨2961, 2959, 0, .none, s2961_plain_contract, 97, s2961_plain_checked⟩

def s2962_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s2962_zero_checked : check 353 s2962_zero_contract = true := by decide +kernel
def s2962_zero : CertifiedContract :=
  ⟨2962, 2965, 0, .none, s2962_zero_contract, 353, s2962_zero_checked⟩

def s2962_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2962_positive_checked : check 359 s2962_positive_contract = true := by decide +kernel
def s2962_positive : CertifiedContract :=
  ⟨2962, 2963, 1, (.dec 2), s2962_positive_contract, 359, s2962_positive_checked⟩

def s2963_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s2963_plain_checked : check 372 s2963_plain_contract = true := by decide +kernel
def s2963_plain : CertifiedContract :=
  ⟨2963, 2964, 0, (.inc 8), s2963_plain_contract, 372, s2963_plain_checked⟩

def s2964_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s2964_plain_checked : check 97 s2964_plain_contract = true := by decide +kernel
def s2964_plain : CertifiedContract :=
  ⟨2964, 2962, 0, .none, s2964_plain_contract, 97, s2964_plain_checked⟩

def s2965_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2965_zero_checked : check 374 s2965_zero_contract = true := by decide +kernel
def s2965_zero : CertifiedContract :=
  ⟨2965, 2968, 0, .none, s2965_zero_contract, 374, s2965_zero_checked⟩

def s2965_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2965_positive_checked : check 380 s2965_positive_contract = true := by decide +kernel
def s2965_positive : CertifiedContract :=
  ⟨2965, 2966, 1, (.dec 0), s2965_positive_contract, 380, s2965_positive_checked⟩

def s2966_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2966_plain_checked : check 372 s2966_plain_contract = true := by decide +kernel
def s2966_plain : CertifiedContract :=
  ⟨2966, 2967, 0, (.inc 2), s2966_plain_contract, 372, s2966_plain_checked⟩

def s2967_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s2967_plain_checked : check 100 s2967_plain_contract = true := by decide +kernel
def s2967_plain : CertifiedContract :=
  ⟨2967, 2965, 0, .none, s2967_plain_contract, 100, s2967_plain_checked⟩

def s2968_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2968_zero_checked : check 380 s2968_zero_contract = true := by decide +kernel
def s2968_zero : CertifiedContract :=
  ⟨2968, 2972, 0, .none, s2968_zero_contract, 380, s2968_zero_checked⟩

def s2968_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2968_positive_checked : check 386 s2968_positive_contract = true := by decide +kernel
def s2968_positive : CertifiedContract :=
  ⟨2968, 2969, 1, (.dec 2), s2968_positive_contract, 386, s2968_positive_checked⟩

def s2969_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2969_plain_checked : check 399 s2969_plain_contract = true := by decide +kernel
def s2969_plain : CertifiedContract :=
  ⟨2969, 2970, 0, (.inc 5), s2969_plain_contract, 399, s2969_plain_checked⟩

def s2970_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2970_plain_checked : check 426 s2970_plain_contract = true := by decide +kernel
def s2970_plain : CertifiedContract :=
  ⟨2970, 2971, 0, (.inc 8), s2970_plain_contract, 426, s2970_plain_checked⟩

def s2971_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2971_plain_checked : check 115 s2971_plain_contract = true := by decide +kernel
def s2971_plain : CertifiedContract :=
  ⟨2971, 2968, 0, .none, s2971_plain_contract, 115, s2971_plain_checked⟩

def s2972_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s2972_zero_checked : check 401 s2972_zero_contract = true := by decide +kernel
def s2972_zero : CertifiedContract :=
  ⟨2972, 2978, 0, .none, s2972_zero_contract, 401, s2972_zero_checked⟩

def s2972_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2972_positive_checked : check 404 s2972_positive_contract = true := by decide +kernel
def s2972_positive : CertifiedContract :=
  ⟨2972, 2973, 1, (.dec 8), s2972_positive_contract, 404, s2972_positive_checked⟩

def s2973_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2973_plain_checked : check 399 s2973_plain_contract = true := by decide +kernel
def s2973_plain : CertifiedContract :=
  ⟨2973, 2974, 0, (.inc 5), s2973_plain_contract, 399, s2973_plain_checked⟩

def s2974_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s2974_zero_checked : check 419 s2974_zero_contract = true := by decide +kernel
def s2974_zero : CertifiedContract :=
  ⟨2974, 2977, 0, .none, s2974_zero_contract, 419, s2974_zero_checked⟩

def s2974_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2974_positive_checked : check 422 s2974_positive_contract = true := by decide +kernel
def s2974_positive : CertifiedContract :=
  ⟨2974, 2975, 1, (.dec 8), s2974_positive_contract, 422, s2974_positive_checked⟩

def s2975_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2975_plain_checked : check 417 s2975_plain_contract = true := by decide +kernel
def s2975_plain : CertifiedContract :=
  ⟨2975, 2976, 0, (.inc 2), s2975_plain_contract, 417, s2975_plain_checked⟩

def s2976_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2976_plain_checked : check 115 s2976_plain_contract = true := by decide +kernel
def s2976_plain : CertifiedContract :=
  ⟨2976, 2974, 0, .none, s2976_plain_contract, 115, s2976_plain_checked⟩

def s2977_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2977_plain_checked : check 118 s2977_plain_contract = true := by decide +kernel
def s2977_plain : CertifiedContract :=
  ⟨2977, 2968, 0, .none, s2977_plain_contract, 118, s2977_plain_checked⟩

def s2978_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s2978_zero_checked : check 389 s2978_zero_contract = true := by decide +kernel
def s2978_zero : CertifiedContract :=
  ⟨2978, 2981, 0, .none, s2978_zero_contract, 389, s2978_zero_checked⟩

def s2978_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2978_positive_checked : check 386 s2978_positive_contract = true := by decide +kernel
def s2978_positive : CertifiedContract :=
  ⟨2978, 2979, 1, (.dec 5), s2978_positive_contract, 386, s2978_positive_checked⟩

def s2979_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2979_plain_checked : check 399 s2979_plain_contract = true := by decide +kernel
def s2979_plain : CertifiedContract :=
  ⟨2979, 2980, 0, (.inc 0), s2979_plain_contract, 399, s2979_plain_checked⟩

def s2980_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s2980_plain_checked : check 106 s2980_plain_contract = true := by decide +kernel
def s2980_plain : CertifiedContract :=
  ⟨2980, 2978, 0, .none, s2980_plain_contract, 106, s2980_plain_checked⟩

def s2981_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s2981_zero_checked : check 353 s2981_zero_contract = true := by decide +kernel
def s2981_zero : CertifiedContract :=
  ⟨2981, 2985, 0, .none, s2981_zero_contract, 353, s2981_zero_checked⟩

def s2981_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s2981_positive_checked : check 359 s2981_positive_contract = true := by decide +kernel
def s2981_positive : CertifiedContract :=
  ⟨2981, 2982, 1, (.dec 7), s2981_positive_contract, 359, s2981_positive_checked⟩

def s2982_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2982_plain_checked : check 363 s2982_plain_contract = true := by decide +kernel
def s2982_plain : CertifiedContract :=
  ⟨2982, 2983, 0, (.inc 2), s2982_plain_contract, 363, s2982_plain_checked⟩

def s2983_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2983_plain_checked : check 390 s2983_plain_contract = true := by decide +kernel
def s2983_plain : CertifiedContract :=
  ⟨2983, 2984, 0, (.inc 8), s2983_plain_contract, 390, s2983_plain_checked⟩

def s2984_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s2984_plain_checked : check 103 s2984_plain_contract = true := by decide +kernel
def s2984_plain : CertifiedContract :=
  ⟨2984, 2981, 0, .none, s2984_plain_contract, 103, s2984_plain_checked⟩

def s2985_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s2985_zero_checked : check 362 s2985_zero_contract = true := by decide +kernel
def s2985_zero : CertifiedContract :=
  ⟨2985, 2988, 0, .none, s2985_zero_contract, 362, s2985_zero_checked⟩

def s2985_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s2985_positive_checked : check 359 s2985_positive_contract = true := by decide +kernel
def s2985_positive : CertifiedContract :=
  ⟨2985, 2986, 1, (.dec 8), s2985_positive_contract, 359, s2985_positive_checked⟩

def s2986_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s2986_plain_checked : check 390 s2986_plain_contract = true := by decide +kernel
def s2986_plain : CertifiedContract :=
  ⟨2986, 2987, 0, (.inc 7), s2986_plain_contract, 390, s2986_plain_checked⟩

def s2987_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s2987_plain_checked : check 97 s2987_plain_contract = true := by decide +kernel
def s2987_plain : CertifiedContract :=
  ⟨2987, 2985, 0, .none, s2987_plain_contract, 97, s2987_plain_checked⟩

def s2988_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s2988_zero_checked : check 365 s2988_zero_contract = true := by decide +kernel
def s2988_zero : CertifiedContract :=
  ⟨2988, 2996, 0, .none, s2988_zero_contract, 365, s2988_zero_checked⟩

def s2988_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s2988_positive_checked : check 371 s2988_positive_contract = true := by decide +kernel
def s2988_positive : CertifiedContract :=
  ⟨2988, 2989, 1, (.dec 0), s2988_positive_contract, 371, s2988_positive_checked⟩

def s2989_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2989_plain_checked : check 381 s2989_plain_contract = true := by decide +kernel
def s2989_plain : CertifiedContract :=
  ⟨2989, 2990, 0, (.inc 5), s2989_plain_contract, 381, s2989_plain_checked⟩

def s2990_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2990_zero_checked : check 407 s2990_zero_contract = true := by decide +kernel
def s2990_zero : CertifiedContract :=
  ⟨2990, 2992, 0, .none, s2990_zero_contract, 407, s2990_zero_checked⟩

def s2990_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2990_positive_checked : check 413 s2990_positive_contract = true := by decide +kernel
def s2990_positive : CertifiedContract :=
  ⟨2990, 2991, 1, (.dec 8), s2990_positive_contract, 413, s2990_positive_checked⟩

def s2991_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s2991_plain_checked : check 112 s2991_plain_contract = true := by decide +kernel
def s2991_plain : CertifiedContract :=
  ⟨2991, 2995, 0, .none, s2991_plain_contract, 112, s2991_plain_checked⟩

def s2992_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s2992_zero_checked : check 419 s2992_zero_contract = true := by decide +kernel
def s2992_zero : CertifiedContract :=
  ⟨2992, 2995, 0, .none, s2992_zero_contract, 419, s2992_zero_checked⟩

def s2992_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2992_positive_checked : check 422 s2992_positive_contract = true := by decide +kernel
def s2992_positive : CertifiedContract :=
  ⟨2992, 2993, 1, (.dec 5), s2992_positive_contract, 422, s2992_positive_checked⟩

def s2993_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2993_plain_checked : check 426 s2993_plain_contract = true := by decide +kernel
def s2993_plain : CertifiedContract :=
  ⟨2993, 2994, 0, (.inc 8), s2993_plain_contract, 426, s2993_plain_checked⟩

def s2994_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2994_plain_checked : check 115 s2994_plain_contract = true := by decide +kernel
def s2994_plain : CertifiedContract :=
  ⟨2994, 2992, 0, .none, s2994_plain_contract, 115, s2994_plain_checked⟩

def s2995_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s2995_plain_checked : check 106 s2995_plain_contract = true := by decide +kernel
def s2995_plain : CertifiedContract :=
  ⟨2995, 2988, 0, .none, s2995_plain_contract, 106, s2995_plain_checked⟩

def s2996_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2996_zero_checked : check 365 s2996_zero_contract = true := by decide +kernel
def s2996_zero : CertifiedContract :=
  ⟨2996, 2999, 0, .none, s2996_zero_contract, 365, s2996_zero_checked⟩

def s2996_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s2996_positive_checked : check 368 s2996_positive_contract = true := by decide +kernel
def s2996_positive : CertifiedContract :=
  ⟨2996, 2997, 1, (.dec 5), s2996_positive_contract, 368, s2996_positive_checked⟩

def s2997_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s2997_plain_checked : check 381 s2997_plain_contract = true := by decide +kernel
def s2997_plain : CertifiedContract :=
  ⟨2997, 2998, 0, (.inc 0), s2997_plain_contract, 381, s2997_plain_checked⟩

def s2998_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s2998_plain_checked : check 100 s2998_plain_contract = true := by decide +kernel
def s2998_plain : CertifiedContract :=
  ⟨2998, 2996, 0, .none, s2998_plain_contract, 100, s2998_plain_checked⟩

def s2999_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s2999_zero_checked : check 362 s2999_zero_contract = true := by decide +kernel
def s2999_zero : CertifiedContract :=
  ⟨2999, 3003, 0, .none, s2999_zero_contract, 362, s2999_zero_checked⟩

def s2999_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2999_positive_checked : check 368 s2999_positive_contract = true := by decide +kernel
def s2999_positive : CertifiedContract :=
  ⟨2999, 3000, 1, (.dec 2), s2999_positive_contract, 368, s2999_positive_checked⟩

def s3000_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3000_plain_checked : check 381 s3000_plain_contract = true := by decide +kernel
def s3000_plain : CertifiedContract :=
  ⟨3000, 3001, 0, (.inc 5), s3000_plain_contract, 381, s3000_plain_checked⟩

def s3001_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3001_plain_checked : check 408 s3001_plain_contract = true := by decide +kernel
def s3001_plain : CertifiedContract :=
  ⟨3001, 3002, 0, (.inc 8), s3001_plain_contract, 408, s3001_plain_checked⟩

def s3002_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s3002_plain_checked : check 109 s3002_plain_contract = true := by decide +kernel
def s3002_plain : CertifiedContract :=
  ⟨3002, 2999, 0, .none, s3002_plain_contract, 109, s3002_plain_checked⟩

def s3003_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s3003_zero_checked : check 383 s3003_zero_contract = true := by decide +kernel
def s3003_zero : CertifiedContract :=
  ⟨3003, 3009, 0, .none, s3003_zero_contract, 383, s3003_zero_checked⟩

def s3003_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3003_positive_checked : check 386 s3003_positive_contract = true := by decide +kernel
def s3003_positive : CertifiedContract :=
  ⟨3003, 3004, 1, (.dec 8), s3003_positive_contract, 386, s3003_positive_checked⟩

def s3004_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3004_plain_checked : check 381 s3004_plain_contract = true := by decide +kernel
def s3004_plain : CertifiedContract :=
  ⟨3004, 3005, 0, (.inc 5), s3004_plain_contract, 381, s3004_plain_checked⟩

def s3005_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s3005_zero_checked : check 401 s3005_zero_contract = true := by decide +kernel
def s3005_zero : CertifiedContract :=
  ⟨3005, 3008, 0, .none, s3005_zero_contract, 401, s3005_zero_checked⟩

def nonterminal : Array CertifiedContract := #[
  s2957_plain,
  s2958_plain,
  s2959_zero,
  s2959_positive,
  s2960_plain,
  s2961_plain,
  s2962_zero,
  s2962_positive,
  s2963_plain,
  s2964_plain,
  s2965_zero,
  s2965_positive,
  s2966_plain,
  s2967_plain,
  s2968_zero,
  s2968_positive,
  s2969_plain,
  s2970_plain,
  s2971_plain,
  s2972_zero,
  s2972_positive,
  s2973_plain,
  s2974_zero,
  s2974_positive,
  s2975_plain,
  s2976_plain,
  s2977_plain,
  s2978_zero,
  s2978_positive,
  s2979_plain,
  s2980_plain,
  s2981_zero,
  s2981_positive,
  s2982_plain,
  s2983_plain,
  s2984_plain,
  s2985_zero,
  s2985_positive,
  s2986_plain,
  s2987_plain,
  s2988_zero,
  s2988_positive,
  s2989_plain,
  s2990_zero,
  s2990_positive,
  s2991_plain,
  s2992_zero,
  s2992_positive,
  s2993_plain,
  s2994_plain,
  s2995_plain,
  s2996_zero,
  s2996_positive,
  s2997_plain,
  s2998_plain,
  s2999_zero,
  s2999_positive,
  s3000_plain,
  s3001_plain,
  s3002_plain,
  s3003_zero,
  s3003_positive,
  s3004_plain,
  s3005_zero
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S060
