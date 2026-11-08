import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S018
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s0884_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0884_plain_checked : check 363 s0884_plain_contract = true := by decide +kernel
def s0884_plain : CertifiedContract :=
  ⟨884, 885, 0, (.inc 2), s0884_plain_contract, 363, s0884_plain_checked⟩

def s0885_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, true] 0 (.inc 2)⟩
theorem s0885_plain_checked : check 369 s0885_plain_contract = true := by decide +kernel
def s0885_plain : CertifiedContract :=
  ⟨885, 886, 0, (.inc 2), s0885_plain_contract, 369, s0885_plain_checked⟩

def s0886_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s0886_plain_checked : check 91 s0886_plain_contract = true := by decide +kernel
def s0886_plain : CertifiedContract :=
  ⟨886, 881, 0, .none, s0886_plain_contract, 91, s0886_plain_checked⟩

def s0887_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s0887_zero_checked : check 308 s0887_zero_contract = true := by decide +kernel
def s0887_zero : CertifiedContract :=
  ⟨887, 890, 0, .none, s0887_zero_contract, 308, s0887_zero_checked⟩

def s0887_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0887_positive_checked : check 314 s0887_positive_contract = true := by decide +kernel
def s0887_positive : CertifiedContract :=
  ⟨887, 888, 1, (.dec 2), s0887_positive_contract, 314, s0887_positive_checked⟩

def s0888_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s0888_plain_checked : check 327 s0888_plain_contract = true := by decide +kernel
def s0888_plain : CertifiedContract :=
  ⟨888, 889, 0, (.inc 8), s0888_plain_contract, 327, s0888_plain_checked⟩

def s0889_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s0889_plain_checked : check 82 s0889_plain_contract = true := by decide +kernel
def s0889_plain : CertifiedContract :=
  ⟨889, 887, 0, .none, s0889_plain_contract, 82, s0889_plain_checked⟩

def s0890_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0890_zero_checked : check 329 s0890_zero_contract = true := by decide +kernel
def s0890_zero : CertifiedContract :=
  ⟨890, 893, 0, .none, s0890_zero_contract, 329, s0890_zero_checked⟩

def s0890_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0890_positive_checked : check 335 s0890_positive_contract = true := by decide +kernel
def s0890_positive : CertifiedContract :=
  ⟨890, 891, 1, (.dec 0), s0890_positive_contract, 335, s0890_positive_checked⟩

def s0891_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0891_plain_checked : check 327 s0891_plain_contract = true := by decide +kernel
def s0891_plain : CertifiedContract :=
  ⟨891, 892, 0, (.inc 2), s0891_plain_contract, 327, s0891_plain_checked⟩

def s0892_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s0892_plain_checked : check 85 s0892_plain_contract = true := by decide +kernel
def s0892_plain : CertifiedContract :=
  ⟨892, 890, 0, .none, s0892_plain_contract, 85, s0892_plain_checked⟩

def s0893_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0893_zero_checked : check 335 s0893_zero_contract = true := by decide +kernel
def s0893_zero : CertifiedContract :=
  ⟨893, 897, 0, .none, s0893_zero_contract, 335, s0893_zero_checked⟩

def s0893_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0893_positive_checked : check 341 s0893_positive_contract = true := by decide +kernel
def s0893_positive : CertifiedContract :=
  ⟨893, 894, 1, (.dec 2), s0893_positive_contract, 341, s0893_positive_checked⟩

def s0894_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0894_plain_checked : check 354 s0894_plain_contract = true := by decide +kernel
def s0894_plain : CertifiedContract :=
  ⟨894, 895, 0, (.inc 5), s0894_plain_contract, 354, s0894_plain_checked⟩

def s0895_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0895_plain_checked : check 381 s0895_plain_contract = true := by decide +kernel
def s0895_plain : CertifiedContract :=
  ⟨895, 896, 0, (.inc 8), s0895_plain_contract, 381, s0895_plain_checked⟩

def s0896_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0896_plain_checked : check 100 s0896_plain_contract = true := by decide +kernel
def s0896_plain : CertifiedContract :=
  ⟨896, 893, 0, .none, s0896_plain_contract, 100, s0896_plain_checked⟩

def s0897_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s0897_zero_checked : check 356 s0897_zero_contract = true := by decide +kernel
def s0897_zero : CertifiedContract :=
  ⟨897, 903, 0, .none, s0897_zero_contract, 356, s0897_zero_checked⟩

def s0897_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0897_positive_checked : check 359 s0897_positive_contract = true := by decide +kernel
def s0897_positive : CertifiedContract :=
  ⟨897, 898, 1, (.dec 8), s0897_positive_contract, 359, s0897_positive_checked⟩

def s0898_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0898_plain_checked : check 354 s0898_plain_contract = true := by decide +kernel
def s0898_plain : CertifiedContract :=
  ⟨898, 899, 0, (.inc 5), s0898_plain_contract, 354, s0898_plain_checked⟩

def s0899_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s0899_zero_checked : check 374 s0899_zero_contract = true := by decide +kernel
def s0899_zero : CertifiedContract :=
  ⟨899, 902, 0, .none, s0899_zero_contract, 374, s0899_zero_checked⟩

def s0899_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0899_positive_checked : check 377 s0899_positive_contract = true := by decide +kernel
def s0899_positive : CertifiedContract :=
  ⟨899, 900, 1, (.dec 8), s0899_positive_contract, 377, s0899_positive_checked⟩

def s0900_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0900_plain_checked : check 372 s0900_plain_contract = true := by decide +kernel
def s0900_plain : CertifiedContract :=
  ⟨900, 901, 0, (.inc 2), s0900_plain_contract, 372, s0900_plain_checked⟩

def s0901_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0901_plain_checked : check 100 s0901_plain_contract = true := by decide +kernel
def s0901_plain : CertifiedContract :=
  ⟨901, 899, 0, .none, s0901_plain_contract, 100, s0901_plain_checked⟩

def s0902_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0902_plain_checked : check 103 s0902_plain_contract = true := by decide +kernel
def s0902_plain : CertifiedContract :=
  ⟨902, 893, 0, .none, s0902_plain_contract, 103, s0902_plain_checked⟩

def s0903_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false] 0 .none⟩
theorem s0903_zero_checked : check 344 s0903_zero_contract = true := by decide +kernel
def s0903_zero : CertifiedContract :=
  ⟨903, 906, 0, .none, s0903_zero_contract, 344, s0903_zero_checked⟩

def s0903_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0903_positive_checked : check 341 s0903_positive_contract = true := by decide +kernel
def s0903_positive : CertifiedContract :=
  ⟨903, 904, 1, (.dec 5), s0903_positive_contract, 341, s0903_positive_checked⟩

def s0904_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0904_plain_checked : check 354 s0904_plain_contract = true := by decide +kernel
def s0904_plain : CertifiedContract :=
  ⟨904, 905, 0, (.inc 0), s0904_plain_contract, 354, s0904_plain_checked⟩

def s0905_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s0905_plain_checked : check 91 s0905_plain_contract = true := by decide +kernel
def s0905_plain : CertifiedContract :=
  ⟨905, 903, 0, .none, s0905_plain_contract, 91, s0905_plain_checked⟩

def s0906_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s0906_zero_checked : check 308 s0906_zero_contract = true := by decide +kernel
def s0906_zero : CertifiedContract :=
  ⟨906, 910, 0, .none, s0906_zero_contract, 308, s0906_zero_checked⟩

def s0906_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, false] 1 (.dec 3)⟩
theorem s0906_positive_checked : check 314 s0906_positive_contract = true := by decide +kernel
def s0906_positive : CertifiedContract :=
  ⟨906, 907, 1, (.dec 3), s0906_positive_contract, 314, s0906_positive_checked⟩

def s0907_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0907_plain_checked : check 327 s0907_plain_contract = true := by decide +kernel
def s0907_plain : CertifiedContract :=
  ⟨907, 908, 0, (.inc 2), s0907_plain_contract, 327, s0907_plain_checked⟩

def s0908_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0908_plain_checked : check 354 s0908_plain_contract = true := by decide +kernel
def s0908_plain : CertifiedContract :=
  ⟨908, 909, 0, (.inc 8), s0908_plain_contract, 354, s0908_plain_checked⟩

def s0909_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false] 0 .none⟩
theorem s0909_plain_checked : check 91 s0909_plain_contract = true := by decide +kernel
def s0909_plain : CertifiedContract :=
  ⟨909, 906, 0, .none, s0909_plain_contract, 91, s0909_plain_checked⟩

def s0910_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s0910_zero_checked : check 317 s0910_zero_contract = true := by decide +kernel
def s0910_zero : CertifiedContract :=
  ⟨910, 913, 0, .none, s0910_zero_contract, 317, s0910_zero_checked⟩

def s0910_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s0910_positive_checked : check 314 s0910_positive_contract = true := by decide +kernel
def s0910_positive : CertifiedContract :=
  ⟨910, 911, 1, (.dec 8), s0910_positive_contract, 314, s0910_positive_checked⟩

def s0911_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, true, true, true] 0 (.inc 3)⟩
theorem s0911_plain_checked : check 330 s0911_plain_contract = true := by decide +kernel
def s0911_plain : CertifiedContract :=
  ⟨911, 912, 0, (.inc 3), s0911_plain_contract, 330, s0911_plain_checked⟩

def s0912_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s0912_plain_checked : check 82 s0912_plain_contract = true := by decide +kernel
def s0912_plain : CertifiedContract :=
  ⟨912, 910, 0, .none, s0912_plain_contract, 82, s0912_plain_checked⟩

def s0913_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0913_zero_checked : check 326 s0913_zero_contract = true := by decide +kernel
def s0913_zero : CertifiedContract :=
  ⟨913, 916, 0, .none, s0913_zero_contract, 326, s0913_zero_checked⟩

def s0913_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s0913_positive_checked : check 332 s0913_positive_contract = true := by decide +kernel
def s0913_positive : CertifiedContract :=
  ⟨913, 914, 1, (.dec 2), s0913_positive_contract, 332, s0913_positive_checked⟩

def s0914_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s0914_plain_checked : check 345 s0914_plain_contract = true := by decide +kernel
def s0914_plain : CertifiedContract :=
  ⟨914, 915, 0, (.inc 8), s0914_plain_contract, 345, s0914_plain_checked⟩

def s0915_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s0915_plain_checked : check 88 s0915_plain_contract = true := by decide +kernel
def s0915_plain : CertifiedContract :=
  ⟨915, 913, 0, .none, s0915_plain_contract, 88, s0915_plain_checked⟩

def s0916_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0916_zero_checked : check 347 s0916_zero_contract = true := by decide +kernel
def s0916_zero : CertifiedContract :=
  ⟨916, 919, 0, .none, s0916_zero_contract, 347, s0916_zero_checked⟩

def s0916_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0916_positive_checked : check 353 s0916_positive_contract = true := by decide +kernel
def s0916_positive : CertifiedContract :=
  ⟨916, 917, 1, (.dec 0), s0916_positive_contract, 353, s0916_positive_checked⟩

def s0917_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0917_plain_checked : check 345 s0917_plain_contract = true := by decide +kernel
def s0917_plain : CertifiedContract :=
  ⟨917, 918, 0, (.inc 2), s0917_plain_contract, 345, s0917_plain_checked⟩

def s0918_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0918_plain_checked : check 91 s0918_plain_contract = true := by decide +kernel
def s0918_plain : CertifiedContract :=
  ⟨918, 916, 0, .none, s0918_plain_contract, 91, s0918_plain_checked⟩

def s0919_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0919_zero_checked : check 353 s0919_zero_contract = true := by decide +kernel
def s0919_zero : CertifiedContract :=
  ⟨919, 923, 0, .none, s0919_zero_contract, 353, s0919_zero_checked⟩

def s0919_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0919_positive_checked : check 359 s0919_positive_contract = true := by decide +kernel
def s0919_positive : CertifiedContract :=
  ⟨919, 920, 1, (.dec 2), s0919_positive_contract, 359, s0919_positive_checked⟩

def s0920_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0920_plain_checked : check 372 s0920_plain_contract = true := by decide +kernel
def s0920_plain : CertifiedContract :=
  ⟨920, 921, 0, (.inc 5), s0920_plain_contract, 372, s0920_plain_checked⟩

def s0921_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0921_plain_checked : check 399 s0921_plain_contract = true := by decide +kernel
def s0921_plain : CertifiedContract :=
  ⟨921, 922, 0, (.inc 8), s0921_plain_contract, 399, s0921_plain_checked⟩

def s0922_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0922_plain_checked : check 106 s0922_plain_contract = true := by decide +kernel
def s0922_plain : CertifiedContract :=
  ⟨922, 919, 0, .none, s0922_plain_contract, 106, s0922_plain_checked⟩

def s0923_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s0923_zero_checked : check 374 s0923_zero_contract = true := by decide +kernel
def s0923_zero : CertifiedContract :=
  ⟨923, 929, 0, .none, s0923_zero_contract, 374, s0923_zero_checked⟩

def s0923_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0923_positive_checked : check 377 s0923_positive_contract = true := by decide +kernel
def s0923_positive : CertifiedContract :=
  ⟨923, 924, 1, (.dec 8), s0923_positive_contract, 377, s0923_positive_checked⟩

def s0924_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0924_plain_checked : check 372 s0924_plain_contract = true := by decide +kernel
def s0924_plain : CertifiedContract :=
  ⟨924, 925, 0, (.inc 5), s0924_plain_contract, 372, s0924_plain_checked⟩

def s0925_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s0925_zero_checked : check 392 s0925_zero_contract = true := by decide +kernel
def s0925_zero : CertifiedContract :=
  ⟨925, 928, 0, .none, s0925_zero_contract, 392, s0925_zero_checked⟩

def s0925_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0925_positive_checked : check 395 s0925_positive_contract = true := by decide +kernel
def s0925_positive : CertifiedContract :=
  ⟨925, 926, 1, (.dec 8), s0925_positive_contract, 395, s0925_positive_checked⟩

def s0926_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0926_plain_checked : check 390 s0926_plain_contract = true := by decide +kernel
def s0926_plain : CertifiedContract :=
  ⟨926, 927, 0, (.inc 2), s0926_plain_contract, 390, s0926_plain_checked⟩

def s0927_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0927_plain_checked : check 106 s0927_plain_contract = true := by decide +kernel
def s0927_plain : CertifiedContract :=
  ⟨927, 925, 0, .none, s0927_plain_contract, 106, s0927_plain_checked⟩

def s0928_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0928_plain_checked : check 109 s0928_plain_contract = true := by decide +kernel
def s0928_plain : CertifiedContract :=
  ⟨928, 919, 0, .none, s0928_plain_contract, 109, s0928_plain_checked⟩

def s0929_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s0929_zero_checked : check 362 s0929_zero_contract = true := by decide +kernel
def s0929_zero : CertifiedContract :=
  ⟨929, 932, 0, .none, s0929_zero_contract, 362, s0929_zero_checked⟩

def s0929_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0929_positive_checked : check 359 s0929_positive_contract = true := by decide +kernel
def s0929_positive : CertifiedContract :=
  ⟨929, 930, 1, (.dec 5), s0929_positive_contract, 359, s0929_positive_checked⟩

def s0930_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0930_plain_checked : check 372 s0930_plain_contract = true := by decide +kernel
def s0930_plain : CertifiedContract :=
  ⟨930, 931, 0, (.inc 0), s0930_plain_contract, 372, s0930_plain_checked⟩

def s0931_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s0931_plain_checked : check 97 s0931_plain_contract = true := by decide +kernel
def s0931_plain : CertifiedContract :=
  ⟨931, 929, 0, .none, s0931_plain_contract, 97, s0931_plain_checked⟩

def s0932_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s0932_zero_checked : check 326 s0932_zero_contract = true := by decide +kernel
def s0932_zero : CertifiedContract :=
  ⟨932, 936, 0, .none, s0932_zero_contract, 326, s0932_zero_checked⟩

def s0932_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, false, true, false] 1 (.dec 3)⟩
theorem s0932_positive_checked : check 332 s0932_positive_contract = true := by decide +kernel
def s0932_positive : CertifiedContract :=
  ⟨932, 933, 1, (.dec 3), s0932_positive_contract, 332, s0932_positive_checked⟩

def nonterminal : Array CertifiedContract := #[
  s0884_plain,
  s0885_plain,
  s0886_plain,
  s0887_zero,
  s0887_positive,
  s0888_plain,
  s0889_plain,
  s0890_zero,
  s0890_positive,
  s0891_plain,
  s0892_plain,
  s0893_zero,
  s0893_positive,
  s0894_plain,
  s0895_plain,
  s0896_plain,
  s0897_zero,
  s0897_positive,
  s0898_plain,
  s0899_zero,
  s0899_positive,
  s0900_plain,
  s0901_plain,
  s0902_plain,
  s0903_zero,
  s0903_positive,
  s0904_plain,
  s0905_plain,
  s0906_zero,
  s0906_positive,
  s0907_plain,
  s0908_plain,
  s0909_plain,
  s0910_zero,
  s0910_positive,
  s0911_plain,
  s0912_plain,
  s0913_zero,
  s0913_positive,
  s0914_plain,
  s0915_plain,
  s0916_zero,
  s0916_positive,
  s0917_plain,
  s0918_plain,
  s0919_zero,
  s0919_positive,
  s0920_plain,
  s0921_plain,
  s0922_plain,
  s0923_zero,
  s0923_positive,
  s0924_plain,
  s0925_zero,
  s0925_positive,
  s0926_plain,
  s0927_plain,
  s0928_plain,
  s0929_zero,
  s0929_positive,
  s0930_plain,
  s0931_plain,
  s0932_zero,
  s0932_positive
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S018
