import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S079
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s3888_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, true, true, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s3888_plain_checked : check 264 s3888_plain_contract = true := by decide +kernel
def s3888_plain : CertifiedContract :=
  ⟨3888, 3889, 0, (.inc 2), s3888_plain_contract, 264, s3888_plain_checked⟩

def s3889_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, true, false, true, false, true, true], rootFrame [true, false, true, false, true, true, true, false, true, false, false] 0 .none⟩
theorem s3889_plain_checked : check 64 s3889_plain_contract = true := by decide +kernel
def s3889_plain : CertifiedContract :=
  ⟨3889, 3887, 0, .none, s3889_plain_contract, 64, s3889_plain_checked⟩

def s3890_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, true, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, true, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3890_zero_checked : check 272 s3890_zero_contract = true := by decide +kernel
def s3890_zero : CertifiedContract :=
  ⟨3890, 3894, 0, .none, s3890_zero_contract, 272, s3890_zero_checked⟩

def s3890_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, true, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, true, true, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3890_positive_checked : check 278 s3890_positive_contract = true := by decide +kernel
def s3890_positive : CertifiedContract :=
  ⟨3890, 3891, 1, (.dec 2), s3890_positive_contract, 278, s3890_positive_checked⟩

def s3891_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, true, true, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3891_plain_checked : check 291 s3891_plain_contract = true := by decide +kernel
def s3891_plain : CertifiedContract :=
  ⟨3891, 3892, 0, (.inc 5), s3891_plain_contract, 291, s3891_plain_checked⟩

def s3892_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, true, true, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3892_plain_checked : check 318 s3892_plain_contract = true := by decide +kernel
def s3892_plain : CertifiedContract :=
  ⟨3892, 3893, 0, (.inc 8), s3892_plain_contract, 318, s3892_plain_checked⟩

def s3893_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s3893_plain_checked : check 79 s3893_plain_contract = true := by decide +kernel
def s3893_plain : CertifiedContract :=
  ⟨3893, 3890, 0, .none, s3893_plain_contract, 79, s3893_plain_checked⟩

def s3894_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s3894_zero_checked : check 293 s3894_zero_contract = true := by decide +kernel
def s3894_zero : CertifiedContract :=
  ⟨3894, 3900, 0, .none, s3894_zero_contract, 293, s3894_zero_checked⟩

def s3894_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, true, true, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3894_positive_checked : check 296 s3894_positive_contract = true := by decide +kernel
def s3894_positive : CertifiedContract :=
  ⟨3894, 3895, 1, (.dec 8), s3894_positive_contract, 296, s3894_positive_checked⟩

def s3895_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, true, true, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3895_plain_checked : check 291 s3895_plain_contract = true := by decide +kernel
def s3895_plain : CertifiedContract :=
  ⟨3895, 3896, 0, (.inc 5), s3895_plain_contract, 291, s3895_plain_checked⟩

def s3896_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, true, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, true, true, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s3896_zero_checked : check 311 s3896_zero_contract = true := by decide +kernel
def s3896_zero : CertifiedContract :=
  ⟨3896, 3899, 0, .none, s3896_zero_contract, 311, s3896_zero_checked⟩

def s3896_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, true, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3896_positive_checked : check 314 s3896_positive_contract = true := by decide +kernel
def s3896_positive : CertifiedContract :=
  ⟨3896, 3897, 1, (.dec 8), s3896_positive_contract, 314, s3896_positive_checked⟩

def s3897_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, true, true, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3897_plain_checked : check 309 s3897_plain_contract = true := by decide +kernel
def s3897_plain : CertifiedContract :=
  ⟨3897, 3898, 0, (.inc 2), s3897_plain_contract, 309, s3897_plain_checked⟩

def s3898_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, true, true, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3898_plain_checked : check 79 s3898_plain_contract = true := by decide +kernel
def s3898_plain : CertifiedContract :=
  ⟨3898, 3896, 0, .none, s3898_plain_contract, 79, s3898_plain_checked⟩

def s3899_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s3899_plain_checked : check 82 s3899_plain_contract = true := by decide +kernel
def s3899_plain : CertifiedContract :=
  ⟨3899, 3890, 0, .none, s3899_plain_contract, 82, s3899_plain_checked⟩

def s3900_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, true, true, true, true, false, false] 0 .none⟩
theorem s3900_zero_checked : check 281 s3900_zero_contract = true := by decide +kernel
def s3900_zero : CertifiedContract :=
  ⟨3900, 3903, 0, .none, s3900_zero_contract, 281, s3900_zero_checked⟩

def s3900_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, true, true, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s3900_positive_checked : check 278 s3900_positive_contract = true := by decide +kernel
def s3900_positive : CertifiedContract :=
  ⟨3900, 3901, 1, (.dec 5), s3900_positive_contract, 278, s3900_positive_checked⟩

def s3901_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, true, true, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s3901_plain_checked : check 291 s3901_plain_contract = true := by decide +kernel
def s3901_plain : CertifiedContract :=
  ⟨3901, 3902, 0, (.inc 0), s3901_plain_contract, 291, s3901_plain_checked⟩

def s3902_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s3902_plain_checked : check 70 s3902_plain_contract = true := by decide +kernel
def s3902_plain : CertifiedContract :=
  ⟨3902, 3900, 0, .none, s3902_plain_contract, 70, s3902_plain_checked⟩

def s3903_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, true, true, true, true, false, false], rootFrame [true, false, true, false, true, true, true, true, true, false] 0 .none⟩
theorem s3903_zero_checked : check 245 s3903_zero_contract = true := by decide +kernel
def s3903_zero : CertifiedContract :=
  ⟨3903, 3907, 0, .none, s3903_zero_contract, 245, s3903_zero_checked⟩

def s3903_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, true, true, true, true, false, false], rootFrame [true, false, true, false, true, true, true, true, false, true, false] 1 (.dec 3)⟩
theorem s3903_positive_checked : check 251 s3903_positive_contract = true := by decide +kernel
def s3903_positive : CertifiedContract :=
  ⟨3903, 3904, 1, (.dec 3), s3903_positive_contract, 251, s3903_positive_checked⟩

def s3904_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, true, true, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s3904_plain_checked : check 264 s3904_plain_contract = true := by decide +kernel
def s3904_plain : CertifiedContract :=
  ⟨3904, 3905, 0, (.inc 2), s3904_plain_contract, 264, s3904_plain_checked⟩

def s3905_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, true, true, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3905_plain_checked : check 291 s3905_plain_contract = true := by decide +kernel
def s3905_plain : CertifiedContract :=
  ⟨3905, 3906, 0, (.inc 8), s3905_plain_contract, 291, s3905_plain_checked⟩

def s3906_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, true, true, true, true, false, false] 0 .none⟩
theorem s3906_plain_checked : check 70 s3906_plain_contract = true := by decide +kernel
def s3906_plain : CertifiedContract :=
  ⟨3906, 3903, 0, .none, s3906_plain_contract, 70, s3906_plain_checked⟩

def s3907_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, true, true, true, true, true, false], rootFrame [true, false, true, true] 0 .none⟩
theorem s3907_zero_checked : check 260 s3907_zero_contract = true := by decide +kernel
def s3907_zero : CertifiedContract :=
  ⟨3907, 3910, 0, .none, s3907_zero_contract, 260, s3907_zero_checked⟩

def s3907_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, true, true, true, true, true, false], rootFrame [true, false, true, false, true, true, true, true, true, true, false] 1 (.dec 8)⟩
theorem s3907_positive_checked : check 251 s3907_positive_contract = true := by decide +kernel
def s3907_positive : CertifiedContract :=
  ⟨3907, 3908, 1, (.dec 8), s3907_positive_contract, 251, s3907_positive_checked⟩

def s3908_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, true, true, true, true, false], rootFrame [true, false, true, false, true, true, true, true, true, true, true] 0 (.inc 3)⟩
theorem s3908_plain_checked : check 267 s3908_plain_contract = true := by decide +kernel
def s3908_plain : CertifiedContract :=
  ⟨3908, 3909, 0, (.inc 3), s3908_plain_contract, 267, s3908_plain_checked⟩

def s3909_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, true, true, true, true, true, true], rootFrame [true, false, true, false, true, true, true, true, true, false] 0 .none⟩
theorem s3909_plain_checked : check 61 s3909_plain_contract = true := by decide +kernel
def s3909_plain : CertifiedContract :=
  ⟨3909, 3907, 0, .none, s3909_plain_contract, 61, s3909_plain_checked⟩

def s3910_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, true], rootFrame [false, false, false, false] 0 .none⟩
theorem s3910_plain_checked : check 40 s3910_plain_contract = true := by decide +kernel
def s3910_plain : CertifiedContract :=
  ⟨3910, 0, 0, .none, s3910_plain_contract, 40, s3910_plain_checked⟩

def s3911_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, true, false, false], rootFrame [true, true, true, false, false, false] 0 .none⟩
theorem s3911_zero_checked : check 191 s3911_zero_contract = true := by decide +kernel
def s3911_zero : CertifiedContract :=
  ⟨3911, 3914, 0, .none, s3911_zero_contract, 191, s3911_zero_checked⟩

def s3911_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, true, false, false], rootFrame [true, true, false, true, false] 1 (.dec 2)⟩
theorem s3911_positive_checked : check 197 s3911_positive_contract = true := by decide +kernel
def s3911_positive : CertifiedContract :=
  ⟨3911, 3912, 1, (.dec 2), s3911_positive_contract, 197, s3911_positive_checked⟩

def s3912_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, false, true, false], rootFrame [true, true, false, true, true] 0 (.inc 8)⟩
theorem s3912_plain_checked : check 210 s3912_plain_contract = true := by decide +kernel
def s3912_plain : CertifiedContract :=
  ⟨3912, 3913, 0, (.inc 8), s3912_plain_contract, 210, s3912_plain_checked⟩

def s3913_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, false, true, true], rootFrame [true, true, false, false] 0 .none⟩
theorem s3913_plain_checked : check 43 s3913_plain_contract = true := by decide +kernel
def s3913_plain : CertifiedContract :=
  ⟨3913, 3911, 0, .none, s3913_plain_contract, 43, s3913_plain_checked⟩

def s3914_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, true, true, false, false, false], rootFrame [true, true, true, false, true, false] 0 .none⟩
theorem s3914_zero_checked : check 209 s3914_zero_contract = true := by decide +kernel
def s3914_zero : CertifiedContract :=
  ⟨3914, 3918, 0, .none, s3914_zero_contract, 209, s3914_zero_checked⟩

def s3914_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, true, true, false, false, false], rootFrame [true, true, true, false, false, true, false] 1 (.dec 7)⟩
theorem s3914_positive_checked : check 215 s3914_positive_contract = true := by decide +kernel
def s3914_positive : CertifiedContract :=
  ⟨3914, 3915, 1, (.dec 7), s3914_positive_contract, 215, s3914_positive_checked⟩

def s3915_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, false, false, true, false], rootFrame [true, true, true, false, false, true, true, false] 0 (.inc 2)⟩
theorem s3915_plain_checked : check 219 s3915_plain_contract = true := by decide +kernel
def s3915_plain : CertifiedContract :=
  ⟨3915, 3916, 0, (.inc 2), s3915_plain_contract, 219, s3915_plain_checked⟩

def s3916_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, false, false, true, true, false], rootFrame [true, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3916_plain_checked : check 246 s3916_plain_contract = true := by decide +kernel
def s3916_plain : CertifiedContract :=
  ⟨3916, 3917, 0, (.inc 8), s3916_plain_contract, 246, s3916_plain_checked⟩

def s3917_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, false, false, true, true, true], rootFrame [true, true, true, false, false, false] 0 .none⟩
theorem s3917_plain_checked : check 55 s3917_plain_contract = true := by decide +kernel
def s3917_plain : CertifiedContract :=
  ⟨3917, 3914, 0, .none, s3917_plain_contract, 55, s3917_plain_checked⟩

def s3918_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, true, true, false, true, false], rootFrame [true, true, true, true, false] 0 .none⟩
theorem s3918_zero_checked : check 212 s3918_zero_contract = true := by decide +kernel
def s3918_zero : CertifiedContract :=
  ⟨3918, 3921, 0, .none, s3918_zero_contract, 212, s3918_zero_checked⟩

def s3918_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, true, true, false, true, false], rootFrame [true, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3918_positive_checked : check 215 s3918_positive_contract = true := by decide +kernel
def s3918_positive : CertifiedContract :=
  ⟨3918, 3919, 1, (.dec 8), s3918_positive_contract, 215, s3918_positive_checked⟩

def s3919_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, false, true, true, false], rootFrame [true, true, true, false, true, true, true] 0 (.inc 7)⟩
theorem s3919_plain_checked : check 246 s3919_plain_contract = true := by decide +kernel
def s3919_plain : CertifiedContract :=
  ⟨3919, 3920, 0, (.inc 7), s3919_plain_contract, 246, s3919_plain_checked⟩

def s3920_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, false, true, true, true], rootFrame [true, true, true, false, true, false] 0 .none⟩
theorem s3920_plain_checked : check 49 s3920_plain_contract = true := by decide +kernel
def s3920_plain : CertifiedContract :=
  ⟨3920, 3918, 0, .none, s3920_plain_contract, 49, s3920_plain_checked⟩

def s3921_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, false], rootFrame [true, true, true, true, true, false, false, false, false, false] 0 (.inc 8)⟩
theorem s3921_plain_checked : check 210 s3921_plain_contract = true := by decide +kernel
def s3921_plain : CertifiedContract :=
  ⟨3921, 3922, 0, (.inc 8), s3921_plain_contract, 210, s3921_plain_checked⟩

def s3922_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, true, true, true, true, false, false, false, false, false], rootFrame [true, true, true, true, true, false, false, false, true] 0 .none⟩
theorem s3922_zero_checked : check 245 s3922_zero_contract = true := by decide +kernel
def s3922_zero : CertifiedContract :=
  ⟨3922, 3926, 0, .none, s3922_zero_contract, 245, s3922_zero_checked⟩

def s3922_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, true, true, true, true, false, false, false, false, false], rootFrame [true, true, true, true, true, false, false, false, false, true, false, false] 1 (.dec 7)⟩
theorem s3922_positive_checked : check 251 s3922_positive_contract = true := by decide +kernel
def s3922_positive : CertifiedContract :=
  ⟨3922, 3923, 1, (.dec 7), s3922_positive_contract, 251, s3922_positive_checked⟩

def s3923_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, true, true, true, true, false, false, false, false, true, false, false], rootFrame [true, true, true, true, true, false, false, false, false, true, true] 0 .none⟩
theorem s3923_zero_checked : check 263 s3923_zero_contract = true := by decide +kernel
def s3923_zero : CertifiedContract :=
  ⟨3923, 3925, 0, .none, s3923_zero_contract, 263, s3923_zero_checked⟩

def s3923_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, true, true, true, true, false, false, false, false, true, false, false], rootFrame [true, true, true, true, true, false, false, false, false, true, false, true] 1 (.dec 8)⟩
theorem s3923_positive_checked : check 269 s3923_positive_contract = true := by decide +kernel
def s3923_positive : CertifiedContract :=
  ⟨3923, 3924, 1, (.dec 8), s3923_positive_contract, 269, s3923_positive_checked⟩

def s3924_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, false, false, false, false, true, false, true], rootFrame [true, true, true, true, true, false, false, false, false, false] 0 .none⟩
theorem s3924_plain_checked : check 64 s3924_plain_contract = true := by decide +kernel
def s3924_plain : CertifiedContract :=
  ⟨3924, 3922, 0, .none, s3924_plain_contract, 64, s3924_plain_checked⟩

def s3925_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, false, false, false, false, true, true], rootFrame [true, true, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s3925_plain_checked : check 78 s3925_plain_contract = true := by decide +kernel
def s3925_plain : CertifiedContract :=
  ⟨3925, 3927, 0, .none, s3925_plain_contract, 78, s3925_plain_checked⟩

def s3926_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, true, true, true, true, false, false, false, true], rootFrame [true, true, true, true, true, false, true] 0 .none⟩
theorem s3926_zero_checked : check 239 s3926_zero_contract = true := by decide +kernel
def s3926_zero : CertifiedContract :=
  ⟨3926, 3932, 0, .none, s3926_zero_contract, 239, s3926_zero_checked⟩

def s3926_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, true, true, true, true, false, false, false, true], rootFrame [true, true, true, true, true, false, false, true, false, false] 1 (.dec 8)⟩
theorem s3926_positive_checked : check 245 s3926_positive_contract = true := by decide +kernel
def s3926_positive : CertifiedContract :=
  ⟨3926, 3927, 1, (.dec 8), s3926_positive_contract, 245, s3926_positive_checked⟩

def s3927_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, true, true, true, true, false, false, true, false, false], rootFrame [true, true, true, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s3927_zero_checked : check 254 s3927_zero_contract = true := by decide +kernel
def s3927_zero : CertifiedContract :=
  ⟨3927, 3929, 0, .none, s3927_zero_contract, 254, s3927_zero_checked⟩

def s3927_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, true, true, true, true, false, false, true, false, false], rootFrame [true, true, true, true, true, false, false, true, false, true] 1 (.dec 7)⟩
theorem s3927_positive_checked : check 260 s3927_positive_contract = true := by decide +kernel
def s3927_positive : CertifiedContract :=
  ⟨3927, 3928, 1, (.dec 7), s3927_positive_contract, 260, s3927_positive_checked⟩

def s3928_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, false, false, true, false, true], rootFrame [true, true, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s3928_plain_checked : check 58 s3928_plain_contract = true := by decide +kernel
def s3928_plain : CertifiedContract :=
  ⟨3928, 3927, 0, .none, s3928_plain_contract, 58, s3928_plain_checked⟩

def s3929_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, true, true, true, true, false, false, true, true, false, false], rootFrame [true, true, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s3929_zero_checked : check 254 s3929_zero_contract = true := by decide +kernel
def s3929_zero : CertifiedContract :=
  ⟨3929, 3931, 0, .none, s3929_zero_contract, 254, s3929_zero_checked⟩

def s3929_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, true, true, true, true, false, false, true, true, false, false], rootFrame [true, true, true, true, true, false, false, true, true, false, true] 1 (.dec 8)⟩
theorem s3929_positive_checked : check 260 s3929_positive_contract = true := by decide +kernel
def s3929_positive : CertifiedContract :=
  ⟨3929, 3930, 1, (.dec 8), s3929_positive_contract, 260, s3929_positive_checked⟩

def s3930_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, false, false, true, true, false, true], rootFrame [true, true, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s3930_plain_checked : check 61 s3930_plain_contract = true := by decide +kernel
def s3930_plain : CertifiedContract :=
  ⟨3930, 3927, 0, .none, s3930_plain_contract, 61, s3930_plain_checked⟩

def s3931_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, false, false, true, true, true], rootFrame [true, true, true, true, true, true, false, false, false] 0 .none⟩
theorem s3931_plain_checked : check 78 s3931_plain_contract = true := by decide +kernel
def s3931_plain : CertifiedContract :=
  ⟨3931, 3933, 0, .none, s3931_plain_contract, 78, s3931_plain_checked⟩

def s3932_plain_initial : SConf := rootFrame [true, true, true, true, true, false, true]
theorem s3932_plain_checked : haltCheck 8 (none) s3932_plain_initial = true := by decide +kernel
def s3932_plain : CertifiedHalt :=
  ⟨3932, (none), s3932_plain_initial, 8, s3932_plain_checked⟩

def s3933_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, true, true, true, true, true, false, false, false], rootFrame [true, true, true, true, true, true, false, true, false] 0 .none⟩
theorem s3933_zero_checked : check 257 s3933_zero_contract = true := by decide +kernel
def s3933_zero : CertifiedContract :=
  ⟨3933, 3941, 0, .none, s3933_zero_contract, 257, s3933_zero_checked⟩

def s3933_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, true, true, true, true, true, false, false, false], rootFrame [true, true, true, true, true, true, false, false, true, false] 1 (.dec 0)⟩
theorem s3933_positive_checked : check 263 s3933_positive_contract = true := by decide +kernel
def s3933_positive : CertifiedContract :=
  ⟨3933, 3934, 1, (.dec 0), s3933_positive_contract, 263, s3933_positive_checked⟩

def s3934_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, true, false, false, true, false], rootFrame [true, true, true, true, true, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3934_plain_checked : check 273 s3934_plain_contract = true := by decide +kernel
def s3934_plain : CertifiedContract :=
  ⟨3934, 3935, 0, (.inc 5), s3934_plain_contract, 273, s3934_plain_checked⟩

def s3935_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, true, true, true, true, true, false, false, true, true, false, false, false], rootFrame [true, true, true, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3935_zero_checked : check 299 s3935_zero_contract = true := by decide +kernel
def s3935_zero : CertifiedContract :=
  ⟨3935, 3937, 0, .none, s3935_zero_contract, 299, s3935_zero_checked⟩

def s3935_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, true, true, true, true, true, false, false, true, true, false, false, false], rootFrame [true, true, true, true, true, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3935_positive_checked : check 305 s3935_positive_contract = true := by decide +kernel
def s3935_positive : CertifiedContract :=
  ⟨3935, 3936, 1, (.dec 8), s3935_positive_contract, 305, s3935_positive_checked⟩

def nonterminal : Array CertifiedContract := #[
  s3888_plain,
  s3889_plain,
  s3890_zero,
  s3890_positive,
  s3891_plain,
  s3892_plain,
  s3893_plain,
  s3894_zero,
  s3894_positive,
  s3895_plain,
  s3896_zero,
  s3896_positive,
  s3897_plain,
  s3898_plain,
  s3899_plain,
  s3900_zero,
  s3900_positive,
  s3901_plain,
  s3902_plain,
  s3903_zero,
  s3903_positive,
  s3904_plain,
  s3905_plain,
  s3906_plain,
  s3907_zero,
  s3907_positive,
  s3908_plain,
  s3909_plain,
  s3910_plain,
  s3911_zero,
  s3911_positive,
  s3912_plain,
  s3913_plain,
  s3914_zero,
  s3914_positive,
  s3915_plain,
  s3916_plain,
  s3917_plain,
  s3918_zero,
  s3918_positive,
  s3919_plain,
  s3920_plain,
  s3921_plain,
  s3922_zero,
  s3922_positive,
  s3923_zero,
  s3923_positive,
  s3924_plain,
  s3925_plain,
  s3926_zero,
  s3926_positive,
  s3927_zero,
  s3927_positive,
  s3928_plain,
  s3929_zero,
  s3929_positive,
  s3930_plain,
  s3931_plain,
  s3933_zero,
  s3933_positive,
  s3934_plain,
  s3935_zero,
  s3935_positive
]
def terminal : Array CertifiedHalt := #[
  s3932_plain
]
end PA213.RuntimeShards.S079
