module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S058
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s2859_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s2859_zero_checked : check 390 s2859_zero_contract = true := by decide +kernel
def s2859_zero : CertifiedContract :=
  ⟨2859, 2861, 0, .none, s2859_zero_contract, 390, s2859_zero_checked⟩

def s2859_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2859_positive_checked : check 396 s2859_positive_contract = true := by decide +kernel
def s2859_positive : CertifiedContract :=
  ⟨2859, 2860, 1, (.dec 8), s2859_positive_contract, 396, s2859_positive_checked⟩

def s2860_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s2860_plain_checked : check 107 s2860_plain_contract = true := by decide +kernel
def s2860_plain : CertifiedContract :=
  ⟨2860, 2864, 0, .none, s2860_plain_contract, 107, s2860_plain_checked⟩

def s2861_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s2861_zero_checked : check 402 s2861_zero_contract = true := by decide +kernel
def s2861_zero : CertifiedContract :=
  ⟨2861, 2864, 0, .none, s2861_zero_contract, 402, s2861_zero_checked⟩

def s2861_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2861_positive_checked : check 405 s2861_positive_contract = true := by decide +kernel
def s2861_positive : CertifiedContract :=
  ⟨2861, 2862, 1, (.dec 5), s2861_positive_contract, 405, s2861_positive_checked⟩

def s2862_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2862_plain_checked : check 409 s2862_plain_contract = true := by decide +kernel
def s2862_plain : CertifiedContract :=
  ⟨2862, 2863, 0, (.inc 8), s2862_plain_contract, 409, s2862_plain_checked⟩

def s2863_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s2863_plain_checked : check 110 s2863_plain_contract = true := by decide +kernel
def s2863_plain : CertifiedContract :=
  ⟨2863, 2861, 0, .none, s2863_plain_contract, 110, s2863_plain_checked⟩

def s2864_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, false] 0 .none⟩
theorem s2864_plain_checked : check 101 s2864_plain_contract = true := by decide +kernel
def s2864_plain : CertifiedContract :=
  ⟨2864, 2857, 0, .none, s2864_plain_contract, 101, s2864_plain_checked⟩

def s2865_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s2865_zero_checked : check 348 s2865_zero_contract = true := by decide +kernel
def s2865_zero : CertifiedContract :=
  ⟨2865, 2868, 0, .none, s2865_zero_contract, 348, s2865_zero_checked⟩

def s2865_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2865_positive_checked : check 351 s2865_positive_contract = true := by decide +kernel
def s2865_positive : CertifiedContract :=
  ⟨2865, 2866, 1, (.dec 5), s2865_positive_contract, 351, s2865_positive_checked⟩

def s2866_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, true, true, true] 0 (.inc 0)⟩
theorem s2866_plain_checked : check 364 s2866_plain_contract = true := by decide +kernel
def s2866_plain : CertifiedContract :=
  ⟨2866, 2867, 0, (.inc 0), s2866_plain_contract, 364, s2866_plain_checked⟩

def s2867_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, true, false] 0 .none⟩
theorem s2867_plain_checked : check 95 s2867_plain_contract = true := by decide +kernel
def s2867_plain : CertifiedContract :=
  ⟨2867, 2865, 0, .none, s2867_plain_contract, 95, s2867_plain_checked⟩

def s2868_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, false] 0 .none⟩
theorem s2868_zero_checked : check 345 s2868_zero_contract = true := by decide +kernel
def s2868_zero : CertifiedContract :=
  ⟨2868, 2872, 0, .none, s2868_zero_contract, 345, s2868_zero_checked⟩

def s2868_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2868_positive_checked : check 351 s2868_positive_contract = true := by decide +kernel
def s2868_positive : CertifiedContract :=
  ⟨2868, 2869, 1, (.dec 2), s2868_positive_contract, 351, s2868_positive_checked⟩

def s2869_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2869_plain_checked : check 364 s2869_plain_contract = true := by decide +kernel
def s2869_plain : CertifiedContract :=
  ⟨2869, 2870, 0, (.inc 5), s2869_plain_contract, 364, s2869_plain_checked⟩

def s2870_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2870_plain_checked : check 391 s2870_plain_contract = true := by decide +kernel
def s2870_plain : CertifiedContract :=
  ⟨2870, 2871, 0, (.inc 8), s2870_plain_contract, 391, s2870_plain_checked⟩

def s2871_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s2871_plain_checked : check 104 s2871_plain_contract = true := by decide +kernel
def s2871_plain : CertifiedContract :=
  ⟨2871, 2868, 0, .none, s2871_plain_contract, 104, s2871_plain_checked⟩

def s2872_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, false] 0 .none⟩
theorem s2872_zero_checked : check 366 s2872_zero_contract = true := by decide +kernel
def s2872_zero : CertifiedContract :=
  ⟨2872, 2878, 0, .none, s2872_zero_contract, 366, s2872_zero_checked⟩

def s2872_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2872_positive_checked : check 369 s2872_positive_contract = true := by decide +kernel
def s2872_positive : CertifiedContract :=
  ⟨2872, 2873, 1, (.dec 8), s2872_positive_contract, 369, s2872_positive_checked⟩

def s2873_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2873_plain_checked : check 364 s2873_plain_contract = true := by decide +kernel
def s2873_plain : CertifiedContract :=
  ⟨2873, 2874, 0, (.inc 5), s2873_plain_contract, 364, s2873_plain_checked⟩

def s2874_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, true] 0 .none⟩
theorem s2874_zero_checked : check 384 s2874_zero_contract = true := by decide +kernel
def s2874_zero : CertifiedContract :=
  ⟨2874, 2877, 0, .none, s2874_zero_contract, 384, s2874_zero_checked⟩

def s2874_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2874_positive_checked : check 387 s2874_positive_contract = true := by decide +kernel
def s2874_positive : CertifiedContract :=
  ⟨2874, 2875, 1, (.dec 8), s2874_positive_contract, 387, s2874_positive_checked⟩

def s2875_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2875_plain_checked : check 382 s2875_plain_contract = true := by decide +kernel
def s2875_plain : CertifiedContract :=
  ⟨2875, 2876, 0, (.inc 2), s2875_plain_contract, 382, s2875_plain_checked⟩

def s2876_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2876_plain_checked : check 104 s2876_plain_contract = true := by decide +kernel
def s2876_plain : CertifiedContract :=
  ⟨2876, 2874, 0, .none, s2876_plain_contract, 104, s2876_plain_checked⟩

def s2877_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s2877_plain_checked : check 107 s2877_plain_contract = true := by decide +kernel
def s2877_plain : CertifiedContract :=
  ⟨2877, 2868, 0, .none, s2877_plain_contract, 107, s2877_plain_checked⟩

def s2878_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s2878_zero_checked : check 360 s2878_zero_contract = true := by decide +kernel
def s2878_zero : CertifiedContract :=
  ⟨2878, 2884, 0, .none, s2878_zero_contract, 360, s2878_zero_checked⟩

def s2878_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2878_positive_checked : check 351 s2878_positive_contract = true := by decide +kernel
def s2878_positive : CertifiedContract :=
  ⟨2878, 2879, 1, (.dec 5), s2878_positive_contract, 351, s2878_positive_checked⟩

def s2879_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2879_plain_checked : check 364 s2879_plain_contract = true := by decide +kernel
def s2879_plain : CertifiedContract :=
  ⟨2879, 2880, 0, (.inc 2), s2879_plain_contract, 364, s2879_plain_checked⟩

def s2880_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2880_plain_checked : check 367 s2880_plain_contract = true := by decide +kernel
def s2880_plain : CertifiedContract :=
  ⟨2880, 2881, 0, (.inc 2), s2880_plain_contract, 367, s2880_plain_checked⟩

def s2881_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2881_plain_checked : check 373 s2881_plain_contract = true := by decide +kernel
def s2881_plain : CertifiedContract :=
  ⟨2881, 2882, 0, (.inc 2), s2881_plain_contract, 373, s2881_plain_checked⟩

def s2882_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, true] 0 (.inc 2)⟩
theorem s2882_plain_checked : check 379 s2882_plain_contract = true := by decide +kernel
def s2882_plain : CertifiedContract :=
  ⟨2882, 2883, 0, (.inc 2), s2882_plain_contract, 379, s2882_plain_checked⟩

def s2883_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, false] 0 .none⟩
theorem s2883_plain_checked : check 92 s2883_plain_contract = true := by decide +kernel
def s2883_plain : CertifiedContract :=
  ⟨2883, 2878, 0, .none, s2883_plain_contract, 92, s2883_plain_checked⟩

def s2884_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s2884_zero_checked : check 336 s2884_zero_contract = true := by decide +kernel
def s2884_zero : CertifiedContract :=
  ⟨2884, 2887, 0, .none, s2884_zero_contract, 336, s2884_zero_checked⟩

def s2884_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s2884_positive_checked : check 342 s2884_positive_contract = true := by decide +kernel
def s2884_positive : CertifiedContract :=
  ⟨2884, 2885, 1, (.dec 2), s2884_positive_contract, 342, s2884_positive_checked⟩

def s2885_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s2885_plain_checked : check 355 s2885_plain_contract = true := by decide +kernel
def s2885_plain : CertifiedContract :=
  ⟨2885, 2886, 0, (.inc 8), s2885_plain_contract, 355, s2885_plain_checked⟩

def s2886_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s2886_plain_checked : check 92 s2886_plain_contract = true := by decide +kernel
def s2886_plain : CertifiedContract :=
  ⟨2886, 2884, 0, .none, s2886_plain_contract, 92, s2886_plain_checked⟩

def s2887_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2887_zero_checked : check 357 s2887_zero_contract = true := by decide +kernel
def s2887_zero : CertifiedContract :=
  ⟨2887, 2890, 0, .none, s2887_zero_contract, 357, s2887_zero_checked⟩

def s2887_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2887_positive_checked : check 363 s2887_positive_contract = true := by decide +kernel
def s2887_positive : CertifiedContract :=
  ⟨2887, 2888, 1, (.dec 0), s2887_positive_contract, 363, s2887_positive_checked⟩

def s2888_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2888_plain_checked : check 355 s2888_plain_contract = true := by decide +kernel
def s2888_plain : CertifiedContract :=
  ⟨2888, 2889, 0, (.inc 2), s2888_plain_contract, 355, s2888_plain_checked⟩

def s2889_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s2889_plain_checked : check 95 s2889_plain_contract = true := by decide +kernel
def s2889_plain : CertifiedContract :=
  ⟨2889, 2887, 0, .none, s2889_plain_contract, 95, s2889_plain_checked⟩

def s2890_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2890_zero_checked : check 363 s2890_zero_contract = true := by decide +kernel
def s2890_zero : CertifiedContract :=
  ⟨2890, 2894, 0, .none, s2890_zero_contract, 363, s2890_zero_checked⟩

def s2890_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2890_positive_checked : check 369 s2890_positive_contract = true := by decide +kernel
def s2890_positive : CertifiedContract :=
  ⟨2890, 2891, 1, (.dec 2), s2890_positive_contract, 369, s2890_positive_checked⟩

def s2891_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2891_plain_checked : check 382 s2891_plain_contract = true := by decide +kernel
def s2891_plain : CertifiedContract :=
  ⟨2891, 2892, 0, (.inc 5), s2891_plain_contract, 382, s2891_plain_checked⟩

def s2892_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2892_plain_checked : check 409 s2892_plain_contract = true := by decide +kernel
def s2892_plain : CertifiedContract :=
  ⟨2892, 2893, 0, (.inc 8), s2892_plain_contract, 409, s2892_plain_checked⟩

def s2893_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2893_plain_checked : check 110 s2893_plain_contract = true := by decide +kernel
def s2893_plain : CertifiedContract :=
  ⟨2893, 2890, 0, .none, s2893_plain_contract, 110, s2893_plain_checked⟩

def s2894_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s2894_zero_checked : check 384 s2894_zero_contract = true := by decide +kernel
def s2894_zero : CertifiedContract :=
  ⟨2894, 2900, 0, .none, s2894_zero_contract, 384, s2894_zero_checked⟩

def s2894_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2894_positive_checked : check 387 s2894_positive_contract = true := by decide +kernel
def s2894_positive : CertifiedContract :=
  ⟨2894, 2895, 1, (.dec 8), s2894_positive_contract, 387, s2894_positive_checked⟩

def s2895_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2895_plain_checked : check 382 s2895_plain_contract = true := by decide +kernel
def s2895_plain : CertifiedContract :=
  ⟨2895, 2896, 0, (.inc 5), s2895_plain_contract, 382, s2895_plain_checked⟩

def s2896_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s2896_zero_checked : check 402 s2896_zero_contract = true := by decide +kernel
def s2896_zero : CertifiedContract :=
  ⟨2896, 2899, 0, .none, s2896_zero_contract, 402, s2896_zero_checked⟩

def s2896_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2896_positive_checked : check 405 s2896_positive_contract = true := by decide +kernel
def s2896_positive : CertifiedContract :=
  ⟨2896, 2897, 1, (.dec 8), s2896_positive_contract, 405, s2896_positive_checked⟩

def s2897_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2897_plain_checked : check 400 s2897_plain_contract = true := by decide +kernel
def s2897_plain : CertifiedContract :=
  ⟨2897, 2898, 0, (.inc 2), s2897_plain_contract, 400, s2897_plain_checked⟩

def s2898_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2898_plain_checked : check 110 s2898_plain_contract = true := by decide +kernel
def s2898_plain : CertifiedContract :=
  ⟨2898, 2896, 0, .none, s2898_plain_contract, 110, s2898_plain_checked⟩

def s2899_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2899_plain_checked : check 113 s2899_plain_contract = true := by decide +kernel
def s2899_plain : CertifiedContract :=
  ⟨2899, 2890, 0, .none, s2899_plain_contract, 113, s2899_plain_checked⟩

def s2900_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s2900_zero_checked : check 372 s2900_zero_contract = true := by decide +kernel
def s2900_zero : CertifiedContract :=
  ⟨2900, 2903, 0, .none, s2900_zero_contract, 372, s2900_zero_checked⟩

def s2900_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2900_positive_checked : check 369 s2900_positive_contract = true := by decide +kernel
def s2900_positive : CertifiedContract :=
  ⟨2900, 2901, 1, (.dec 5), s2900_positive_contract, 369, s2900_positive_checked⟩

def s2901_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2901_plain_checked : check 382 s2901_plain_contract = true := by decide +kernel
def s2901_plain : CertifiedContract :=
  ⟨2901, 2902, 0, (.inc 0), s2901_plain_contract, 382, s2901_plain_checked⟩

def s2902_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s2902_plain_checked : check 101 s2902_plain_contract = true := by decide +kernel
def s2902_plain : CertifiedContract :=
  ⟨2902, 2900, 0, .none, s2902_plain_contract, 101, s2902_plain_checked⟩

def s2903_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s2903_zero_checked : check 336 s2903_zero_contract = true := by decide +kernel
def s2903_zero : CertifiedContract :=
  ⟨2903, 2907, 0, .none, s2903_zero_contract, 336, s2903_zero_checked⟩

def s2903_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, true, false] 1 (.dec 4)⟩
theorem s2903_positive_checked : check 342 s2903_positive_contract = true := by decide +kernel
def s2903_positive : CertifiedContract :=
  ⟨2903, 2904, 1, (.dec 4), s2903_positive_contract, 342, s2903_positive_checked⟩

def s2904_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2904_plain_checked : check 355 s2904_plain_contract = true := by decide +kernel
def s2904_plain : CertifiedContract :=
  ⟨2904, 2905, 0, (.inc 2), s2904_plain_contract, 355, s2904_plain_checked⟩

def s2905_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2905_plain_checked : check 382 s2905_plain_contract = true := by decide +kernel
def s2905_plain : CertifiedContract :=
  ⟨2905, 2906, 0, (.inc 8), s2905_plain_contract, 382, s2905_plain_checked⟩

def s2906_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s2906_plain_checked : check 101 s2906_plain_contract = true := by decide +kernel
def s2906_plain : CertifiedContract :=
  ⟨2906, 2903, 0, .none, s2906_plain_contract, 101, s2906_plain_checked⟩

def s2907_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s2907_zero_checked : check 342 s2907_zero_contract = true := by decide +kernel
def s2907_zero : CertifiedContract :=
  ⟨2907, 2910, 0, .none, s2907_zero_contract, 342, s2907_zero_checked⟩

def s2907_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s2907_positive_checked : check 342 s2907_positive_contract = true := by decide +kernel
def s2907_positive : CertifiedContract :=
  ⟨2907, 2908, 1, (.dec 8), s2907_positive_contract, 342, s2907_positive_checked⟩

end PA211.UserCandidate.RuntimeShards.S058
