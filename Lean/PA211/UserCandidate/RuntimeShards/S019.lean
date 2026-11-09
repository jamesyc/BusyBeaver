module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S019
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s0933_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0933_plain_checked : check 346 s0933_plain_contract = true := by decide +kernel
def s0933_plain : CertifiedContract :=
  ⟨933, 934, 0, (.inc 2), s0933_plain_contract, 346, s0933_plain_checked⟩

def s0934_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0934_plain_checked : check 373 s0934_plain_contract = true := by decide +kernel
def s0934_plain : CertifiedContract :=
  ⟨934, 935, 0, (.inc 8), s0934_plain_contract, 373, s0934_plain_checked⟩

def s0935_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s0935_plain_checked : check 98 s0935_plain_contract = true := by decide +kernel
def s0935_plain : CertifiedContract :=
  ⟨935, 932, 0, .none, s0935_plain_contract, 98, s0935_plain_checked⟩

def s0936_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0936_zero_checked : check 333 s0936_zero_contract = true := by decide +kernel
def s0936_zero : CertifiedContract :=
  ⟨936, 939, 0, .none, s0936_zero_contract, 333, s0936_zero_checked⟩

def s0936_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s0936_positive_checked : check 333 s0936_positive_contract = true := by decide +kernel
def s0936_positive : CertifiedContract :=
  ⟨936, 937, 1, (.dec 8), s0936_positive_contract, 333, s0936_positive_checked⟩

def s0937_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, true, true, true] 0 (.inc 3)⟩
theorem s0937_plain_checked : check 349 s0937_plain_contract = true := by decide +kernel
def s0937_plain : CertifiedContract :=
  ⟨937, 938, 0, (.inc 3), s0937_plain_contract, 349, s0937_plain_checked⟩

def s0938_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s0938_plain_checked : check 89 s0938_plain_contract = true := by decide +kernel
def s0938_plain : CertifiedContract :=
  ⟨938, 936, 0, .none, s0938_plain_contract, 89, s0938_plain_checked⟩

def s0939_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s0939_zero_checked : check 327 s0939_zero_contract = true := by decide +kernel
def s0939_zero : CertifiedContract :=
  ⟨939, 942, 0, .none, s0939_zero_contract, 327, s0939_zero_checked⟩

def s0939_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0939_positive_checked : check 333 s0939_positive_contract = true := by decide +kernel
def s0939_positive : CertifiedContract :=
  ⟨939, 940, 1, (.dec 2), s0939_positive_contract, 333, s0939_positive_checked⟩

def s0940_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s0940_plain_checked : check 346 s0940_plain_contract = true := by decide +kernel
def s0940_plain : CertifiedContract :=
  ⟨940, 941, 0, (.inc 8), s0940_plain_contract, 346, s0940_plain_checked⟩

def s0941_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0941_plain_checked : check 89 s0941_plain_contract = true := by decide +kernel
def s0941_plain : CertifiedContract :=
  ⟨941, 939, 0, .none, s0941_plain_contract, 89, s0941_plain_checked⟩

def s0942_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0942_zero_checked : check 348 s0942_zero_contract = true := by decide +kernel
def s0942_zero : CertifiedContract :=
  ⟨942, 945, 0, .none, s0942_zero_contract, 348, s0942_zero_checked⟩

def s0942_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0942_positive_checked : check 354 s0942_positive_contract = true := by decide +kernel
def s0942_positive : CertifiedContract :=
  ⟨942, 943, 1, (.dec 0), s0942_positive_contract, 354, s0942_positive_checked⟩

def s0943_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0943_plain_checked : check 346 s0943_plain_contract = true := by decide +kernel
def s0943_plain : CertifiedContract :=
  ⟨943, 944, 0, (.inc 2), s0943_plain_contract, 346, s0943_plain_checked⟩

def s0944_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s0944_plain_checked : check 92 s0944_plain_contract = true := by decide +kernel
def s0944_plain : CertifiedContract :=
  ⟨944, 942, 0, .none, s0944_plain_contract, 92, s0944_plain_checked⟩

def s0945_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0945_zero_checked : check 354 s0945_zero_contract = true := by decide +kernel
def s0945_zero : CertifiedContract :=
  ⟨945, 949, 0, .none, s0945_zero_contract, 354, s0945_zero_checked⟩

def s0945_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0945_positive_checked : check 360 s0945_positive_contract = true := by decide +kernel
def s0945_positive : CertifiedContract :=
  ⟨945, 946, 1, (.dec 2), s0945_positive_contract, 360, s0945_positive_checked⟩

def s0946_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0946_plain_checked : check 373 s0946_plain_contract = true := by decide +kernel
def s0946_plain : CertifiedContract :=
  ⟨946, 947, 0, (.inc 5), s0946_plain_contract, 373, s0946_plain_checked⟩

def s0947_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0947_plain_checked : check 400 s0947_plain_contract = true := by decide +kernel
def s0947_plain : CertifiedContract :=
  ⟨947, 948, 0, (.inc 8), s0947_plain_contract, 400, s0947_plain_checked⟩

def s0948_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0948_plain_checked : check 107 s0948_plain_contract = true := by decide +kernel
def s0948_plain : CertifiedContract :=
  ⟨948, 945, 0, .none, s0948_plain_contract, 107, s0948_plain_checked⟩

def s0949_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s0949_zero_checked : check 375 s0949_zero_contract = true := by decide +kernel
def s0949_zero : CertifiedContract :=
  ⟨949, 955, 0, .none, s0949_zero_contract, 375, s0949_zero_checked⟩

def s0949_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0949_positive_checked : check 378 s0949_positive_contract = true := by decide +kernel
def s0949_positive : CertifiedContract :=
  ⟨949, 950, 1, (.dec 8), s0949_positive_contract, 378, s0949_positive_checked⟩

def s0950_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0950_plain_checked : check 373 s0950_plain_contract = true := by decide +kernel
def s0950_plain : CertifiedContract :=
  ⟨950, 951, 0, (.inc 5), s0950_plain_contract, 373, s0950_plain_checked⟩

def s0951_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s0951_zero_checked : check 393 s0951_zero_contract = true := by decide +kernel
def s0951_zero : CertifiedContract :=
  ⟨951, 954, 0, .none, s0951_zero_contract, 393, s0951_zero_checked⟩

def s0951_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0951_positive_checked : check 396 s0951_positive_contract = true := by decide +kernel
def s0951_positive : CertifiedContract :=
  ⟨951, 952, 1, (.dec 8), s0951_positive_contract, 396, s0951_positive_checked⟩

def s0952_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0952_plain_checked : check 391 s0952_plain_contract = true := by decide +kernel
def s0952_plain : CertifiedContract :=
  ⟨952, 953, 0, (.inc 2), s0952_plain_contract, 391, s0952_plain_checked⟩

def s0953_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0953_plain_checked : check 107 s0953_plain_contract = true := by decide +kernel
def s0953_plain : CertifiedContract :=
  ⟨953, 951, 0, .none, s0953_plain_contract, 107, s0953_plain_checked⟩

def s0954_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0954_plain_checked : check 110 s0954_plain_contract = true := by decide +kernel
def s0954_plain : CertifiedContract :=
  ⟨954, 945, 0, .none, s0954_plain_contract, 110, s0954_plain_checked⟩

def s0955_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s0955_zero_checked : check 363 s0955_zero_contract = true := by decide +kernel
def s0955_zero : CertifiedContract :=
  ⟨955, 958, 0, .none, s0955_zero_contract, 363, s0955_zero_checked⟩

def s0955_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0955_positive_checked : check 360 s0955_positive_contract = true := by decide +kernel
def s0955_positive : CertifiedContract :=
  ⟨955, 956, 1, (.dec 5), s0955_positive_contract, 360, s0955_positive_checked⟩

def s0956_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0956_plain_checked : check 373 s0956_plain_contract = true := by decide +kernel
def s0956_plain : CertifiedContract :=
  ⟨956, 957, 0, (.inc 0), s0956_plain_contract, 373, s0956_plain_checked⟩

def s0957_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s0957_plain_checked : check 98 s0957_plain_contract = true := by decide +kernel
def s0957_plain : CertifiedContract :=
  ⟨957, 955, 0, .none, s0957_plain_contract, 98, s0957_plain_checked⟩

def s0958_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s0958_zero_checked : check 327 s0958_zero_contract = true := by decide +kernel
def s0958_zero : CertifiedContract :=
  ⟨958, 962, 0, .none, s0958_zero_contract, 327, s0958_zero_checked⟩

def s0958_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, false] 1 (.dec 4)⟩
theorem s0958_positive_checked : check 333 s0958_positive_contract = true := by decide +kernel
def s0958_positive : CertifiedContract :=
  ⟨958, 959, 1, (.dec 4), s0958_positive_contract, 333, s0958_positive_checked⟩

def s0959_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0959_plain_checked : check 346 s0959_plain_contract = true := by decide +kernel
def s0959_plain : CertifiedContract :=
  ⟨959, 960, 0, (.inc 2), s0959_plain_contract, 346, s0959_plain_checked⟩

def s0960_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0960_plain_checked : check 373 s0960_plain_contract = true := by decide +kernel
def s0960_plain : CertifiedContract :=
  ⟨960, 961, 0, (.inc 8), s0960_plain_contract, 373, s0960_plain_checked⟩

def s0961_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s0961_plain_checked : check 98 s0961_plain_contract = true := by decide +kernel
def s0961_plain : CertifiedContract :=
  ⟨961, 958, 0, .none, s0961_plain_contract, 98, s0961_plain_checked⟩

def s0962_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s0962_zero_checked : check 336 s0962_zero_contract = true := by decide +kernel
def s0962_zero : CertifiedContract :=
  ⟨962, 965, 0, .none, s0962_zero_contract, 336, s0962_zero_checked⟩

def s0962_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s0962_positive_checked : check 333 s0962_positive_contract = true := by decide +kernel
def s0962_positive : CertifiedContract :=
  ⟨962, 963, 1, (.dec 8), s0962_positive_contract, 333, s0962_positive_checked⟩

def s0963_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, true, true, true] 0 (.inc 4)⟩
theorem s0963_plain_checked : check 337 s0963_plain_contract = true := by decide +kernel
def s0963_plain : CertifiedContract :=
  ⟨963, 964, 0, (.inc 4), s0963_plain_contract, 337, s0963_plain_checked⟩

def s0964_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s0964_plain_checked : check 89 s0964_plain_contract = true := by decide +kernel
def s0964_plain : CertifiedContract :=
  ⟨964, 962, 0, .none, s0964_plain_contract, 89, s0964_plain_checked⟩

def s0965_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s0965_zero_checked : check 339 s0965_zero_contract = true := by decide +kernel
def s0965_zero : CertifiedContract :=
  ⟨965, 973, 0, .none, s0965_zero_contract, 339, s0965_zero_checked⟩

def s0965_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s0965_positive_checked : check 345 s0965_positive_contract = true := by decide +kernel
def s0965_positive : CertifiedContract :=
  ⟨965, 966, 1, (.dec 0), s0965_positive_contract, 345, s0965_positive_checked⟩

def s0966_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0966_plain_checked : check 355 s0966_plain_contract = true := by decide +kernel
def s0966_plain : CertifiedContract :=
  ⟨966, 967, 0, (.inc 5), s0966_plain_contract, 355, s0966_plain_checked⟩

def s0967_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0967_zero_checked : check 381 s0967_zero_contract = true := by decide +kernel
def s0967_zero : CertifiedContract :=
  ⟨967, 969, 0, .none, s0967_zero_contract, 381, s0967_zero_checked⟩

def s0967_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0967_positive_checked : check 387 s0967_positive_contract = true := by decide +kernel
def s0967_positive : CertifiedContract :=
  ⟨967, 968, 1, (.dec 8), s0967_positive_contract, 387, s0967_positive_checked⟩

def s0968_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s0968_plain_checked : check 104 s0968_plain_contract = true := by decide +kernel
def s0968_plain : CertifiedContract :=
  ⟨968, 972, 0, .none, s0968_plain_contract, 104, s0968_plain_checked⟩

def s0969_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s0969_zero_checked : check 393 s0969_zero_contract = true := by decide +kernel
def s0969_zero : CertifiedContract :=
  ⟨969, 972, 0, .none, s0969_zero_contract, 393, s0969_zero_checked⟩

def s0969_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0969_positive_checked : check 396 s0969_positive_contract = true := by decide +kernel
def s0969_positive : CertifiedContract :=
  ⟨969, 970, 1, (.dec 5), s0969_positive_contract, 396, s0969_positive_checked⟩

def s0970_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0970_plain_checked : check 400 s0970_plain_contract = true := by decide +kernel
def s0970_plain : CertifiedContract :=
  ⟨970, 971, 0, (.inc 8), s0970_plain_contract, 400, s0970_plain_checked⟩

def s0971_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0971_plain_checked : check 107 s0971_plain_contract = true := by decide +kernel
def s0971_plain : CertifiedContract :=
  ⟨971, 969, 0, .none, s0971_plain_contract, 107, s0971_plain_checked⟩

def s0972_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s0972_plain_checked : check 98 s0972_plain_contract = true := by decide +kernel
def s0972_plain : CertifiedContract :=
  ⟨972, 965, 0, .none, s0972_plain_contract, 98, s0972_plain_checked⟩

def s0973_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0973_zero_checked : check 339 s0973_zero_contract = true := by decide +kernel
def s0973_zero : CertifiedContract :=
  ⟨973, 976, 0, .none, s0973_zero_contract, 339, s0973_zero_checked⟩

def s0973_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0973_positive_checked : check 342 s0973_positive_contract = true := by decide +kernel
def s0973_positive : CertifiedContract :=
  ⟨973, 974, 1, (.dec 5), s0973_positive_contract, 342, s0973_positive_checked⟩

def s0974_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s0974_plain_checked : check 355 s0974_plain_contract = true := by decide +kernel
def s0974_plain : CertifiedContract :=
  ⟨974, 975, 0, (.inc 0), s0974_plain_contract, 355, s0974_plain_checked⟩

def s0975_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s0975_plain_checked : check 92 s0975_plain_contract = true := by decide +kernel
def s0975_plain : CertifiedContract :=
  ⟨975, 973, 0, .none, s0975_plain_contract, 92, s0975_plain_checked⟩

def s0976_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s0976_zero_checked : check 336 s0976_zero_contract = true := by decide +kernel
def s0976_zero : CertifiedContract :=
  ⟨976, 980, 0, .none, s0976_zero_contract, 336, s0976_zero_checked⟩

def s0976_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0976_positive_checked : check 342 s0976_positive_contract = true := by decide +kernel
def s0976_positive : CertifiedContract :=
  ⟨976, 977, 1, (.dec 2), s0976_positive_contract, 342, s0976_positive_checked⟩

def s0977_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0977_plain_checked : check 355 s0977_plain_contract = true := by decide +kernel
def s0977_plain : CertifiedContract :=
  ⟨977, 978, 0, (.inc 5), s0977_plain_contract, 355, s0977_plain_checked⟩

def s0978_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0978_plain_checked : check 382 s0978_plain_contract = true := by decide +kernel
def s0978_plain : CertifiedContract :=
  ⟨978, 979, 0, (.inc 8), s0978_plain_contract, 382, s0978_plain_checked⟩

def s0979_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0979_plain_checked : check 101 s0979_plain_contract = true := by decide +kernel
def s0979_plain : CertifiedContract :=
  ⟨979, 976, 0, .none, s0979_plain_contract, 101, s0979_plain_checked⟩

def s0980_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s0980_zero_checked : check 357 s0980_zero_contract = true := by decide +kernel
def s0980_zero : CertifiedContract :=
  ⟨980, 986, 0, .none, s0980_zero_contract, 357, s0980_zero_checked⟩

def s0980_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0980_positive_checked : check 360 s0980_positive_contract = true := by decide +kernel
def s0980_positive : CertifiedContract :=
  ⟨980, 981, 1, (.dec 8), s0980_positive_contract, 360, s0980_positive_checked⟩

def s0981_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0981_plain_checked : check 355 s0981_plain_contract = true := by decide +kernel
def s0981_plain : CertifiedContract :=
  ⟨981, 982, 0, (.inc 5), s0981_plain_contract, 355, s0981_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S019
