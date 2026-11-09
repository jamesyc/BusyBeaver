module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S018
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s0884_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0884_plain_checked : check 373 s0884_plain_contract = true := by decide +kernel
def s0884_plain : CertifiedContract :=
  ⟨884, 885, 0, (.inc 2), s0884_plain_contract, 373, s0884_plain_checked⟩

def s0885_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, true] 0 (.inc 2)⟩
theorem s0885_plain_checked : check 379 s0885_plain_contract = true := by decide +kernel
def s0885_plain : CertifiedContract :=
  ⟨885, 886, 0, (.inc 2), s0885_plain_contract, 379, s0885_plain_checked⟩

def s0886_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s0886_plain_checked : check 92 s0886_plain_contract = true := by decide +kernel
def s0886_plain : CertifiedContract :=
  ⟨886, 881, 0, .none, s0886_plain_contract, 92, s0886_plain_checked⟩

def s0887_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s0887_zero_checked : check 309 s0887_zero_contract = true := by decide +kernel
def s0887_zero : CertifiedContract :=
  ⟨887, 890, 0, .none, s0887_zero_contract, 309, s0887_zero_checked⟩

def s0887_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0887_positive_checked : check 315 s0887_positive_contract = true := by decide +kernel
def s0887_positive : CertifiedContract :=
  ⟨887, 888, 1, (.dec 2), s0887_positive_contract, 315, s0887_positive_checked⟩

def s0888_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s0888_plain_checked : check 328 s0888_plain_contract = true := by decide +kernel
def s0888_plain : CertifiedContract :=
  ⟨888, 889, 0, (.inc 8), s0888_plain_contract, 328, s0888_plain_checked⟩

def s0889_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s0889_plain_checked : check 83 s0889_plain_contract = true := by decide +kernel
def s0889_plain : CertifiedContract :=
  ⟨889, 887, 0, .none, s0889_plain_contract, 83, s0889_plain_checked⟩

def s0890_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0890_zero_checked : check 330 s0890_zero_contract = true := by decide +kernel
def s0890_zero : CertifiedContract :=
  ⟨890, 893, 0, .none, s0890_zero_contract, 330, s0890_zero_checked⟩

def s0890_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0890_positive_checked : check 336 s0890_positive_contract = true := by decide +kernel
def s0890_positive : CertifiedContract :=
  ⟨890, 891, 1, (.dec 0), s0890_positive_contract, 336, s0890_positive_checked⟩

def s0891_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0891_plain_checked : check 328 s0891_plain_contract = true := by decide +kernel
def s0891_plain : CertifiedContract :=
  ⟨891, 892, 0, (.inc 2), s0891_plain_contract, 328, s0891_plain_checked⟩

def s0892_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s0892_plain_checked : check 86 s0892_plain_contract = true := by decide +kernel
def s0892_plain : CertifiedContract :=
  ⟨892, 890, 0, .none, s0892_plain_contract, 86, s0892_plain_checked⟩

def s0893_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0893_zero_checked : check 336 s0893_zero_contract = true := by decide +kernel
def s0893_zero : CertifiedContract :=
  ⟨893, 897, 0, .none, s0893_zero_contract, 336, s0893_zero_checked⟩

def s0893_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0893_positive_checked : check 342 s0893_positive_contract = true := by decide +kernel
def s0893_positive : CertifiedContract :=
  ⟨893, 894, 1, (.dec 2), s0893_positive_contract, 342, s0893_positive_checked⟩

def s0894_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0894_plain_checked : check 355 s0894_plain_contract = true := by decide +kernel
def s0894_plain : CertifiedContract :=
  ⟨894, 895, 0, (.inc 5), s0894_plain_contract, 355, s0894_plain_checked⟩

def s0895_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0895_plain_checked : check 382 s0895_plain_contract = true := by decide +kernel
def s0895_plain : CertifiedContract :=
  ⟨895, 896, 0, (.inc 8), s0895_plain_contract, 382, s0895_plain_checked⟩

def s0896_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0896_plain_checked : check 101 s0896_plain_contract = true := by decide +kernel
def s0896_plain : CertifiedContract :=
  ⟨896, 893, 0, .none, s0896_plain_contract, 101, s0896_plain_checked⟩

def s0897_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s0897_zero_checked : check 357 s0897_zero_contract = true := by decide +kernel
def s0897_zero : CertifiedContract :=
  ⟨897, 903, 0, .none, s0897_zero_contract, 357, s0897_zero_checked⟩

def s0897_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0897_positive_checked : check 360 s0897_positive_contract = true := by decide +kernel
def s0897_positive : CertifiedContract :=
  ⟨897, 898, 1, (.dec 8), s0897_positive_contract, 360, s0897_positive_checked⟩

def s0898_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0898_plain_checked : check 355 s0898_plain_contract = true := by decide +kernel
def s0898_plain : CertifiedContract :=
  ⟨898, 899, 0, (.inc 5), s0898_plain_contract, 355, s0898_plain_checked⟩

def s0899_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s0899_zero_checked : check 375 s0899_zero_contract = true := by decide +kernel
def s0899_zero : CertifiedContract :=
  ⟨899, 902, 0, .none, s0899_zero_contract, 375, s0899_zero_checked⟩

def s0899_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0899_positive_checked : check 378 s0899_positive_contract = true := by decide +kernel
def s0899_positive : CertifiedContract :=
  ⟨899, 900, 1, (.dec 8), s0899_positive_contract, 378, s0899_positive_checked⟩

def s0900_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0900_plain_checked : check 373 s0900_plain_contract = true := by decide +kernel
def s0900_plain : CertifiedContract :=
  ⟨900, 901, 0, (.inc 2), s0900_plain_contract, 373, s0900_plain_checked⟩

def s0901_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0901_plain_checked : check 101 s0901_plain_contract = true := by decide +kernel
def s0901_plain : CertifiedContract :=
  ⟨901, 899, 0, .none, s0901_plain_contract, 101, s0901_plain_checked⟩

def s0902_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0902_plain_checked : check 104 s0902_plain_contract = true := by decide +kernel
def s0902_plain : CertifiedContract :=
  ⟨902, 893, 0, .none, s0902_plain_contract, 104, s0902_plain_checked⟩

def s0903_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false] 0 .none⟩
theorem s0903_zero_checked : check 345 s0903_zero_contract = true := by decide +kernel
def s0903_zero : CertifiedContract :=
  ⟨903, 906, 0, .none, s0903_zero_contract, 345, s0903_zero_checked⟩

def s0903_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0903_positive_checked : check 342 s0903_positive_contract = true := by decide +kernel
def s0903_positive : CertifiedContract :=
  ⟨903, 904, 1, (.dec 5), s0903_positive_contract, 342, s0903_positive_checked⟩

def s0904_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0904_plain_checked : check 355 s0904_plain_contract = true := by decide +kernel
def s0904_plain : CertifiedContract :=
  ⟨904, 905, 0, (.inc 0), s0904_plain_contract, 355, s0904_plain_checked⟩

def s0905_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s0905_plain_checked : check 92 s0905_plain_contract = true := by decide +kernel
def s0905_plain : CertifiedContract :=
  ⟨905, 903, 0, .none, s0905_plain_contract, 92, s0905_plain_checked⟩

def s0906_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s0906_zero_checked : check 309 s0906_zero_contract = true := by decide +kernel
def s0906_zero : CertifiedContract :=
  ⟨906, 910, 0, .none, s0906_zero_contract, 309, s0906_zero_checked⟩

def s0906_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, false] 1 (.dec 3)⟩
theorem s0906_positive_checked : check 315 s0906_positive_contract = true := by decide +kernel
def s0906_positive : CertifiedContract :=
  ⟨906, 907, 1, (.dec 3), s0906_positive_contract, 315, s0906_positive_checked⟩

def s0907_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0907_plain_checked : check 328 s0907_plain_contract = true := by decide +kernel
def s0907_plain : CertifiedContract :=
  ⟨907, 908, 0, (.inc 2), s0907_plain_contract, 328, s0907_plain_checked⟩

def s0908_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0908_plain_checked : check 355 s0908_plain_contract = true := by decide +kernel
def s0908_plain : CertifiedContract :=
  ⟨908, 909, 0, (.inc 8), s0908_plain_contract, 355, s0908_plain_checked⟩

def s0909_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false] 0 .none⟩
theorem s0909_plain_checked : check 92 s0909_plain_contract = true := by decide +kernel
def s0909_plain : CertifiedContract :=
  ⟨909, 906, 0, .none, s0909_plain_contract, 92, s0909_plain_checked⟩

def s0910_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s0910_zero_checked : check 318 s0910_zero_contract = true := by decide +kernel
def s0910_zero : CertifiedContract :=
  ⟨910, 913, 0, .none, s0910_zero_contract, 318, s0910_zero_checked⟩

def s0910_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s0910_positive_checked : check 315 s0910_positive_contract = true := by decide +kernel
def s0910_positive : CertifiedContract :=
  ⟨910, 911, 1, (.dec 8), s0910_positive_contract, 315, s0910_positive_checked⟩

def s0911_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, true, true, true] 0 (.inc 3)⟩
theorem s0911_plain_checked : check 331 s0911_plain_contract = true := by decide +kernel
def s0911_plain : CertifiedContract :=
  ⟨911, 912, 0, (.inc 3), s0911_plain_contract, 331, s0911_plain_checked⟩

def s0912_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s0912_plain_checked : check 83 s0912_plain_contract = true := by decide +kernel
def s0912_plain : CertifiedContract :=
  ⟨912, 910, 0, .none, s0912_plain_contract, 83, s0912_plain_checked⟩

def s0913_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0913_zero_checked : check 327 s0913_zero_contract = true := by decide +kernel
def s0913_zero : CertifiedContract :=
  ⟨913, 916, 0, .none, s0913_zero_contract, 327, s0913_zero_checked⟩

def s0913_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s0913_positive_checked : check 333 s0913_positive_contract = true := by decide +kernel
def s0913_positive : CertifiedContract :=
  ⟨913, 914, 1, (.dec 2), s0913_positive_contract, 333, s0913_positive_checked⟩

def s0914_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s0914_plain_checked : check 346 s0914_plain_contract = true := by decide +kernel
def s0914_plain : CertifiedContract :=
  ⟨914, 915, 0, (.inc 8), s0914_plain_contract, 346, s0914_plain_checked⟩

def s0915_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s0915_plain_checked : check 89 s0915_plain_contract = true := by decide +kernel
def s0915_plain : CertifiedContract :=
  ⟨915, 913, 0, .none, s0915_plain_contract, 89, s0915_plain_checked⟩

def s0916_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0916_zero_checked : check 348 s0916_zero_contract = true := by decide +kernel
def s0916_zero : CertifiedContract :=
  ⟨916, 919, 0, .none, s0916_zero_contract, 348, s0916_zero_checked⟩

def s0916_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0916_positive_checked : check 354 s0916_positive_contract = true := by decide +kernel
def s0916_positive : CertifiedContract :=
  ⟨916, 917, 1, (.dec 0), s0916_positive_contract, 354, s0916_positive_checked⟩

def s0917_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0917_plain_checked : check 346 s0917_plain_contract = true := by decide +kernel
def s0917_plain : CertifiedContract :=
  ⟨917, 918, 0, (.inc 2), s0917_plain_contract, 346, s0917_plain_checked⟩

def s0918_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0918_plain_checked : check 92 s0918_plain_contract = true := by decide +kernel
def s0918_plain : CertifiedContract :=
  ⟨918, 916, 0, .none, s0918_plain_contract, 92, s0918_plain_checked⟩

def s0919_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0919_zero_checked : check 354 s0919_zero_contract = true := by decide +kernel
def s0919_zero : CertifiedContract :=
  ⟨919, 923, 0, .none, s0919_zero_contract, 354, s0919_zero_checked⟩

def s0919_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0919_positive_checked : check 360 s0919_positive_contract = true := by decide +kernel
def s0919_positive : CertifiedContract :=
  ⟨919, 920, 1, (.dec 2), s0919_positive_contract, 360, s0919_positive_checked⟩

def s0920_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0920_plain_checked : check 373 s0920_plain_contract = true := by decide +kernel
def s0920_plain : CertifiedContract :=
  ⟨920, 921, 0, (.inc 5), s0920_plain_contract, 373, s0920_plain_checked⟩

def s0921_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0921_plain_checked : check 400 s0921_plain_contract = true := by decide +kernel
def s0921_plain : CertifiedContract :=
  ⟨921, 922, 0, (.inc 8), s0921_plain_contract, 400, s0921_plain_checked⟩

def s0922_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0922_plain_checked : check 107 s0922_plain_contract = true := by decide +kernel
def s0922_plain : CertifiedContract :=
  ⟨922, 919, 0, .none, s0922_plain_contract, 107, s0922_plain_checked⟩

def s0923_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s0923_zero_checked : check 375 s0923_zero_contract = true := by decide +kernel
def s0923_zero : CertifiedContract :=
  ⟨923, 929, 0, .none, s0923_zero_contract, 375, s0923_zero_checked⟩

def s0923_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0923_positive_checked : check 378 s0923_positive_contract = true := by decide +kernel
def s0923_positive : CertifiedContract :=
  ⟨923, 924, 1, (.dec 8), s0923_positive_contract, 378, s0923_positive_checked⟩

def s0924_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0924_plain_checked : check 373 s0924_plain_contract = true := by decide +kernel
def s0924_plain : CertifiedContract :=
  ⟨924, 925, 0, (.inc 5), s0924_plain_contract, 373, s0924_plain_checked⟩

def s0925_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s0925_zero_checked : check 393 s0925_zero_contract = true := by decide +kernel
def s0925_zero : CertifiedContract :=
  ⟨925, 928, 0, .none, s0925_zero_contract, 393, s0925_zero_checked⟩

def s0925_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0925_positive_checked : check 396 s0925_positive_contract = true := by decide +kernel
def s0925_positive : CertifiedContract :=
  ⟨925, 926, 1, (.dec 8), s0925_positive_contract, 396, s0925_positive_checked⟩

def s0926_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0926_plain_checked : check 391 s0926_plain_contract = true := by decide +kernel
def s0926_plain : CertifiedContract :=
  ⟨926, 927, 0, (.inc 2), s0926_plain_contract, 391, s0926_plain_checked⟩

def s0927_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0927_plain_checked : check 107 s0927_plain_contract = true := by decide +kernel
def s0927_plain : CertifiedContract :=
  ⟨927, 925, 0, .none, s0927_plain_contract, 107, s0927_plain_checked⟩

def s0928_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0928_plain_checked : check 110 s0928_plain_contract = true := by decide +kernel
def s0928_plain : CertifiedContract :=
  ⟨928, 919, 0, .none, s0928_plain_contract, 110, s0928_plain_checked⟩

def s0929_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s0929_zero_checked : check 363 s0929_zero_contract = true := by decide +kernel
def s0929_zero : CertifiedContract :=
  ⟨929, 932, 0, .none, s0929_zero_contract, 363, s0929_zero_checked⟩

def s0929_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0929_positive_checked : check 360 s0929_positive_contract = true := by decide +kernel
def s0929_positive : CertifiedContract :=
  ⟨929, 930, 1, (.dec 5), s0929_positive_contract, 360, s0929_positive_checked⟩

def s0930_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0930_plain_checked : check 373 s0930_plain_contract = true := by decide +kernel
def s0930_plain : CertifiedContract :=
  ⟨930, 931, 0, (.inc 0), s0930_plain_contract, 373, s0930_plain_checked⟩

def s0931_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s0931_plain_checked : check 98 s0931_plain_contract = true := by decide +kernel
def s0931_plain : CertifiedContract :=
  ⟨931, 929, 0, .none, s0931_plain_contract, 98, s0931_plain_checked⟩

def s0932_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s0932_zero_checked : check 327 s0932_zero_contract = true := by decide +kernel
def s0932_zero : CertifiedContract :=
  ⟨932, 936, 0, .none, s0932_zero_contract, 327, s0932_zero_checked⟩

def s0932_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, true, false] 1 (.dec 3)⟩
theorem s0932_positive_checked : check 333 s0932_positive_contract = true := by decide +kernel
def s0932_positive : CertifiedContract :=
  ⟨932, 933, 1, (.dec 3), s0932_positive_contract, 333, s0932_positive_checked⟩

end PA211.UserCandidate.RuntimeShards.S018
