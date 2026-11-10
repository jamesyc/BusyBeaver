import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S058
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s2859_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s2859_zero_checked : check 389 s2859_zero_contract = true := by decide +kernel
def s2859_zero : CertifiedContract :=
  ⟨2859, 2861, 0, .none, s2859_zero_contract, 389, s2859_zero_checked⟩

def s2859_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2859_positive_checked : check 395 s2859_positive_contract = true := by decide +kernel
def s2859_positive : CertifiedContract :=
  ⟨2859, 2860, 1, (.dec 8), s2859_positive_contract, 395, s2859_positive_checked⟩

def s2860_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s2860_plain_checked : check 106 s2860_plain_contract = true := by decide +kernel
def s2860_plain : CertifiedContract :=
  ⟨2860, 2864, 0, .none, s2860_plain_contract, 106, s2860_plain_checked⟩

def s2861_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s2861_zero_checked : check 401 s2861_zero_contract = true := by decide +kernel
def s2861_zero : CertifiedContract :=
  ⟨2861, 2864, 0, .none, s2861_zero_contract, 401, s2861_zero_checked⟩

def s2861_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2861_positive_checked : check 404 s2861_positive_contract = true := by decide +kernel
def s2861_positive : CertifiedContract :=
  ⟨2861, 2862, 1, (.dec 5), s2861_positive_contract, 404, s2861_positive_checked⟩

def s2862_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2862_plain_checked : check 408 s2862_plain_contract = true := by decide +kernel
def s2862_plain : CertifiedContract :=
  ⟨2862, 2863, 0, (.inc 8), s2862_plain_contract, 408, s2862_plain_checked⟩

def s2863_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s2863_plain_checked : check 109 s2863_plain_contract = true := by decide +kernel
def s2863_plain : CertifiedContract :=
  ⟨2863, 2861, 0, .none, s2863_plain_contract, 109, s2863_plain_checked⟩

def s2864_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, false] 0 .none⟩
theorem s2864_plain_checked : check 100 s2864_plain_contract = true := by decide +kernel
def s2864_plain : CertifiedContract :=
  ⟨2864, 2857, 0, .none, s2864_plain_contract, 100, s2864_plain_checked⟩

def s2865_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s2865_zero_checked : check 347 s2865_zero_contract = true := by decide +kernel
def s2865_zero : CertifiedContract :=
  ⟨2865, 2868, 0, .none, s2865_zero_contract, 347, s2865_zero_checked⟩

def s2865_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2865_positive_checked : check 350 s2865_positive_contract = true := by decide +kernel
def s2865_positive : CertifiedContract :=
  ⟨2865, 2866, 1, (.dec 5), s2865_positive_contract, 350, s2865_positive_checked⟩

def s2866_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, true, true, true] 0 (.inc 0)⟩
theorem s2866_plain_checked : check 363 s2866_plain_contract = true := by decide +kernel
def s2866_plain : CertifiedContract :=
  ⟨2866, 2867, 0, (.inc 0), s2866_plain_contract, 363, s2866_plain_checked⟩

def s2867_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, true, false] 0 .none⟩
theorem s2867_plain_checked : check 94 s2867_plain_contract = true := by decide +kernel
def s2867_plain : CertifiedContract :=
  ⟨2867, 2865, 0, .none, s2867_plain_contract, 94, s2867_plain_checked⟩

def s2868_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, false] 0 .none⟩
theorem s2868_zero_checked : check 344 s2868_zero_contract = true := by decide +kernel
def s2868_zero : CertifiedContract :=
  ⟨2868, 2872, 0, .none, s2868_zero_contract, 344, s2868_zero_checked⟩

def s2868_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2868_positive_checked : check 350 s2868_positive_contract = true := by decide +kernel
def s2868_positive : CertifiedContract :=
  ⟨2868, 2869, 1, (.dec 2), s2868_positive_contract, 350, s2868_positive_checked⟩

def s2869_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2869_plain_checked : check 363 s2869_plain_contract = true := by decide +kernel
def s2869_plain : CertifiedContract :=
  ⟨2869, 2870, 0, (.inc 5), s2869_plain_contract, 363, s2869_plain_checked⟩

def s2870_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2870_plain_checked : check 390 s2870_plain_contract = true := by decide +kernel
def s2870_plain : CertifiedContract :=
  ⟨2870, 2871, 0, (.inc 8), s2870_plain_contract, 390, s2870_plain_checked⟩

def s2871_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s2871_plain_checked : check 103 s2871_plain_contract = true := by decide +kernel
def s2871_plain : CertifiedContract :=
  ⟨2871, 2868, 0, .none, s2871_plain_contract, 103, s2871_plain_checked⟩

def s2872_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, false] 0 .none⟩
theorem s2872_zero_checked : check 365 s2872_zero_contract = true := by decide +kernel
def s2872_zero : CertifiedContract :=
  ⟨2872, 2878, 0, .none, s2872_zero_contract, 365, s2872_zero_checked⟩

def s2872_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2872_positive_checked : check 368 s2872_positive_contract = true := by decide +kernel
def s2872_positive : CertifiedContract :=
  ⟨2872, 2873, 1, (.dec 8), s2872_positive_contract, 368, s2872_positive_checked⟩

def s2873_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2873_plain_checked : check 363 s2873_plain_contract = true := by decide +kernel
def s2873_plain : CertifiedContract :=
  ⟨2873, 2874, 0, (.inc 5), s2873_plain_contract, 363, s2873_plain_checked⟩

def s2874_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, true] 0 .none⟩
theorem s2874_zero_checked : check 383 s2874_zero_contract = true := by decide +kernel
def s2874_zero : CertifiedContract :=
  ⟨2874, 2877, 0, .none, s2874_zero_contract, 383, s2874_zero_checked⟩

def s2874_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2874_positive_checked : check 386 s2874_positive_contract = true := by decide +kernel
def s2874_positive : CertifiedContract :=
  ⟨2874, 2875, 1, (.dec 8), s2874_positive_contract, 386, s2874_positive_checked⟩

def s2875_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2875_plain_checked : check 381 s2875_plain_contract = true := by decide +kernel
def s2875_plain : CertifiedContract :=
  ⟨2875, 2876, 0, (.inc 2), s2875_plain_contract, 381, s2875_plain_checked⟩

def s2876_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2876_plain_checked : check 103 s2876_plain_contract = true := by decide +kernel
def s2876_plain : CertifiedContract :=
  ⟨2876, 2874, 0, .none, s2876_plain_contract, 103, s2876_plain_checked⟩

def s2877_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s2877_plain_checked : check 106 s2877_plain_contract = true := by decide +kernel
def s2877_plain : CertifiedContract :=
  ⟨2877, 2868, 0, .none, s2877_plain_contract, 106, s2877_plain_checked⟩

def s2878_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s2878_zero_checked : check 359 s2878_zero_contract = true := by decide +kernel
def s2878_zero : CertifiedContract :=
  ⟨2878, 2884, 0, .none, s2878_zero_contract, 359, s2878_zero_checked⟩

def s2878_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2878_positive_checked : check 350 s2878_positive_contract = true := by decide +kernel
def s2878_positive : CertifiedContract :=
  ⟨2878, 2879, 1, (.dec 5), s2878_positive_contract, 350, s2878_positive_checked⟩

def s2879_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2879_plain_checked : check 363 s2879_plain_contract = true := by decide +kernel
def s2879_plain : CertifiedContract :=
  ⟨2879, 2880, 0, (.inc 2), s2879_plain_contract, 363, s2879_plain_checked⟩

def s2880_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2880_plain_checked : check 366 s2880_plain_contract = true := by decide +kernel
def s2880_plain : CertifiedContract :=
  ⟨2880, 2881, 0, (.inc 2), s2880_plain_contract, 366, s2880_plain_checked⟩

def s2881_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2881_plain_checked : check 363 s2881_plain_contract = true := by decide +kernel
def s2881_plain : CertifiedContract :=
  ⟨2881, 2882, 0, (.inc 2), s2881_plain_contract, 363, s2881_plain_checked⟩

def s2882_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, true] 0 (.inc 2)⟩
theorem s2882_plain_checked : check 369 s2882_plain_contract = true := by decide +kernel
def s2882_plain : CertifiedContract :=
  ⟨2882, 2883, 0, (.inc 2), s2882_plain_contract, 369, s2882_plain_checked⟩

def s2883_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, false] 0 .none⟩
theorem s2883_plain_checked : check 91 s2883_plain_contract = true := by decide +kernel
def s2883_plain : CertifiedContract :=
  ⟨2883, 2878, 0, .none, s2883_plain_contract, 91, s2883_plain_checked⟩

def s2884_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s2884_zero_checked : check 335 s2884_zero_contract = true := by decide +kernel
def s2884_zero : CertifiedContract :=
  ⟨2884, 2887, 0, .none, s2884_zero_contract, 335, s2884_zero_checked⟩

def s2884_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s2884_positive_checked : check 341 s2884_positive_contract = true := by decide +kernel
def s2884_positive : CertifiedContract :=
  ⟨2884, 2885, 1, (.dec 2), s2884_positive_contract, 341, s2884_positive_checked⟩

def s2885_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s2885_plain_checked : check 354 s2885_plain_contract = true := by decide +kernel
def s2885_plain : CertifiedContract :=
  ⟨2885, 2886, 0, (.inc 8), s2885_plain_contract, 354, s2885_plain_checked⟩

def s2886_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s2886_plain_checked : check 91 s2886_plain_contract = true := by decide +kernel
def s2886_plain : CertifiedContract :=
  ⟨2886, 2884, 0, .none, s2886_plain_contract, 91, s2886_plain_checked⟩

def s2887_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2887_zero_checked : check 356 s2887_zero_contract = true := by decide +kernel
def s2887_zero : CertifiedContract :=
  ⟨2887, 2890, 0, .none, s2887_zero_contract, 356, s2887_zero_checked⟩

def s2887_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2887_positive_checked : check 362 s2887_positive_contract = true := by decide +kernel
def s2887_positive : CertifiedContract :=
  ⟨2887, 2888, 1, (.dec 0), s2887_positive_contract, 362, s2887_positive_checked⟩

def s2888_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2888_plain_checked : check 354 s2888_plain_contract = true := by decide +kernel
def s2888_plain : CertifiedContract :=
  ⟨2888, 2889, 0, (.inc 2), s2888_plain_contract, 354, s2888_plain_checked⟩

def s2889_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s2889_plain_checked : check 94 s2889_plain_contract = true := by decide +kernel
def s2889_plain : CertifiedContract :=
  ⟨2889, 2887, 0, .none, s2889_plain_contract, 94, s2889_plain_checked⟩

def s2890_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2890_zero_checked : check 362 s2890_zero_contract = true := by decide +kernel
def s2890_zero : CertifiedContract :=
  ⟨2890, 2894, 0, .none, s2890_zero_contract, 362, s2890_zero_checked⟩

def s2890_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2890_positive_checked : check 368 s2890_positive_contract = true := by decide +kernel
def s2890_positive : CertifiedContract :=
  ⟨2890, 2891, 1, (.dec 2), s2890_positive_contract, 368, s2890_positive_checked⟩

def s2891_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2891_plain_checked : check 381 s2891_plain_contract = true := by decide +kernel
def s2891_plain : CertifiedContract :=
  ⟨2891, 2892, 0, (.inc 5), s2891_plain_contract, 381, s2891_plain_checked⟩

def s2892_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2892_plain_checked : check 408 s2892_plain_contract = true := by decide +kernel
def s2892_plain : CertifiedContract :=
  ⟨2892, 2893, 0, (.inc 8), s2892_plain_contract, 408, s2892_plain_checked⟩

def s2893_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2893_plain_checked : check 109 s2893_plain_contract = true := by decide +kernel
def s2893_plain : CertifiedContract :=
  ⟨2893, 2890, 0, .none, s2893_plain_contract, 109, s2893_plain_checked⟩

def s2894_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s2894_zero_checked : check 383 s2894_zero_contract = true := by decide +kernel
def s2894_zero : CertifiedContract :=
  ⟨2894, 2900, 0, .none, s2894_zero_contract, 383, s2894_zero_checked⟩

def s2894_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2894_positive_checked : check 386 s2894_positive_contract = true := by decide +kernel
def s2894_positive : CertifiedContract :=
  ⟨2894, 2895, 1, (.dec 8), s2894_positive_contract, 386, s2894_positive_checked⟩

def s2895_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2895_plain_checked : check 381 s2895_plain_contract = true := by decide +kernel
def s2895_plain : CertifiedContract :=
  ⟨2895, 2896, 0, (.inc 5), s2895_plain_contract, 381, s2895_plain_checked⟩

def s2896_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s2896_zero_checked : check 401 s2896_zero_contract = true := by decide +kernel
def s2896_zero : CertifiedContract :=
  ⟨2896, 2899, 0, .none, s2896_zero_contract, 401, s2896_zero_checked⟩

def s2896_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2896_positive_checked : check 404 s2896_positive_contract = true := by decide +kernel
def s2896_positive : CertifiedContract :=
  ⟨2896, 2897, 1, (.dec 8), s2896_positive_contract, 404, s2896_positive_checked⟩

def s2897_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2897_plain_checked : check 399 s2897_plain_contract = true := by decide +kernel
def s2897_plain : CertifiedContract :=
  ⟨2897, 2898, 0, (.inc 2), s2897_plain_contract, 399, s2897_plain_checked⟩

def s2898_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2898_plain_checked : check 109 s2898_plain_contract = true := by decide +kernel
def s2898_plain : CertifiedContract :=
  ⟨2898, 2896, 0, .none, s2898_plain_contract, 109, s2898_plain_checked⟩

def s2899_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2899_plain_checked : check 112 s2899_plain_contract = true := by decide +kernel
def s2899_plain : CertifiedContract :=
  ⟨2899, 2890, 0, .none, s2899_plain_contract, 112, s2899_plain_checked⟩

def s2900_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s2900_zero_checked : check 371 s2900_zero_contract = true := by decide +kernel
def s2900_zero : CertifiedContract :=
  ⟨2900, 2903, 0, .none, s2900_zero_contract, 371, s2900_zero_checked⟩

def s2900_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2900_positive_checked : check 368 s2900_positive_contract = true := by decide +kernel
def s2900_positive : CertifiedContract :=
  ⟨2900, 2901, 1, (.dec 5), s2900_positive_contract, 368, s2900_positive_checked⟩

def s2901_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2901_plain_checked : check 381 s2901_plain_contract = true := by decide +kernel
def s2901_plain : CertifiedContract :=
  ⟨2901, 2902, 0, (.inc 0), s2901_plain_contract, 381, s2901_plain_checked⟩

def s2902_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s2902_plain_checked : check 100 s2902_plain_contract = true := by decide +kernel
def s2902_plain : CertifiedContract :=
  ⟨2902, 2900, 0, .none, s2902_plain_contract, 100, s2902_plain_checked⟩

def s2903_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s2903_zero_checked : check 335 s2903_zero_contract = true := by decide +kernel
def s2903_zero : CertifiedContract :=
  ⟨2903, 2907, 0, .none, s2903_zero_contract, 335, s2903_zero_checked⟩

def s2903_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, true, false] 1 (.dec 4)⟩
theorem s2903_positive_checked : check 341 s2903_positive_contract = true := by decide +kernel
def s2903_positive : CertifiedContract :=
  ⟨2903, 2904, 1, (.dec 4), s2903_positive_contract, 341, s2903_positive_checked⟩

def s2904_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2904_plain_checked : check 354 s2904_plain_contract = true := by decide +kernel
def s2904_plain : CertifiedContract :=
  ⟨2904, 2905, 0, (.inc 2), s2904_plain_contract, 354, s2904_plain_checked⟩

def s2905_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2905_plain_checked : check 381 s2905_plain_contract = true := by decide +kernel
def s2905_plain : CertifiedContract :=
  ⟨2905, 2906, 0, (.inc 8), s2905_plain_contract, 381, s2905_plain_checked⟩

def s2906_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s2906_plain_checked : check 100 s2906_plain_contract = true := by decide +kernel
def s2906_plain : CertifiedContract :=
  ⟨2906, 2903, 0, .none, s2906_plain_contract, 100, s2906_plain_checked⟩

def s2907_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s2907_zero_checked : check 341 s2907_zero_contract = true := by decide +kernel
def s2907_zero : CertifiedContract :=
  ⟨2907, 2910, 0, .none, s2907_zero_contract, 341, s2907_zero_checked⟩

def s2907_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s2907_positive_checked : check 341 s2907_positive_contract = true := by decide +kernel
def s2907_positive : CertifiedContract :=
  ⟨2907, 2908, 1, (.dec 8), s2907_positive_contract, 341, s2907_positive_checked⟩

def nonterminal : Array CertifiedContract := #[
  s2859_zero,
  s2859_positive,
  s2860_plain,
  s2861_zero,
  s2861_positive,
  s2862_plain,
  s2863_plain,
  s2864_plain,
  s2865_zero,
  s2865_positive,
  s2866_plain,
  s2867_plain,
  s2868_zero,
  s2868_positive,
  s2869_plain,
  s2870_plain,
  s2871_plain,
  s2872_zero,
  s2872_positive,
  s2873_plain,
  s2874_zero,
  s2874_positive,
  s2875_plain,
  s2876_plain,
  s2877_plain,
  s2878_zero,
  s2878_positive,
  s2879_plain,
  s2880_plain,
  s2881_plain,
  s2882_plain,
  s2883_plain,
  s2884_zero,
  s2884_positive,
  s2885_plain,
  s2886_plain,
  s2887_zero,
  s2887_positive,
  s2888_plain,
  s2889_plain,
  s2890_zero,
  s2890_positive,
  s2891_plain,
  s2892_plain,
  s2893_plain,
  s2894_zero,
  s2894_positive,
  s2895_plain,
  s2896_zero,
  s2896_positive,
  s2897_plain,
  s2898_plain,
  s2899_plain,
  s2900_zero,
  s2900_positive,
  s2901_plain,
  s2902_plain,
  s2903_zero,
  s2903_positive,
  s2904_plain,
  s2905_plain,
  s2906_plain,
  s2907_zero,
  s2907_positive
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S058
