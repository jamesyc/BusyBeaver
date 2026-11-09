module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S056
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s2760_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s2760_zero_checked : check 410 s2760_zero_contract = true := by decide +kernel
def s2760_zero : CertifiedContract :=
  ⟨2760, 2763, 0, .none, s2760_zero_contract, 410, s2760_zero_checked⟩

def s2760_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2760_positive_checked : check 413 s2760_positive_contract = true := by decide +kernel
def s2760_positive : CertifiedContract :=
  ⟨2760, 2761, 1, (.dec 8), s2760_positive_contract, 413, s2760_positive_checked⟩

def s2761_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2761_plain_checked : check 408 s2761_plain_contract = true := by decide +kernel
def s2761_plain : CertifiedContract :=
  ⟨2761, 2762, 0, (.inc 2), s2761_plain_contract, 408, s2761_plain_checked⟩

def s2762_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2762_plain_checked : check 112 s2762_plain_contract = true := by decide +kernel
def s2762_plain : CertifiedContract :=
  ⟨2762, 2760, 0, .none, s2762_plain_contract, 112, s2762_plain_checked⟩

def s2763_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2763_plain_checked : check 115 s2763_plain_contract = true := by decide +kernel
def s2763_plain : CertifiedContract :=
  ⟨2763, 2754, 0, .none, s2763_plain_contract, 115, s2763_plain_checked⟩

def s2764_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s2764_zero_checked : check 380 s2764_zero_contract = true := by decide +kernel
def s2764_zero : CertifiedContract :=
  ⟨2764, 2767, 0, .none, s2764_zero_contract, 380, s2764_zero_checked⟩

def s2764_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2764_positive_checked : check 377 s2764_positive_contract = true := by decide +kernel
def s2764_positive : CertifiedContract :=
  ⟨2764, 2765, 1, (.dec 5), s2764_positive_contract, 377, s2764_positive_checked⟩

def s2765_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2765_plain_checked : check 390 s2765_plain_contract = true := by decide +kernel
def s2765_plain : CertifiedContract :=
  ⟨2765, 2766, 0, (.inc 0), s2765_plain_contract, 390, s2765_plain_checked⟩

def s2766_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s2766_plain_checked : check 103 s2766_plain_contract = true := by decide +kernel
def s2766_plain : CertifiedContract :=
  ⟨2766, 2764, 0, .none, s2766_plain_contract, 103, s2766_plain_checked⟩

def s2767_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s2767_zero_checked : check 344 s2767_zero_contract = true := by decide +kernel
def s2767_zero : CertifiedContract :=
  ⟨2767, 2771, 0, .none, s2767_zero_contract, 344, s2767_zero_checked⟩

def s2767_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, true, false, true, false] 1 (.dec 3)⟩
theorem s2767_positive_checked : check 350 s2767_positive_contract = true := by decide +kernel
def s2767_positive : CertifiedContract :=
  ⟨2767, 2768, 1, (.dec 3), s2767_positive_contract, 350, s2767_positive_checked⟩

def s2768_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2768_plain_checked : check 363 s2768_plain_contract = true := by decide +kernel
def s2768_plain : CertifiedContract :=
  ⟨2768, 2769, 0, (.inc 2), s2768_plain_contract, 363, s2768_plain_checked⟩

def s2769_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2769_plain_checked : check 390 s2769_plain_contract = true := by decide +kernel
def s2769_plain : CertifiedContract :=
  ⟨2769, 2770, 0, (.inc 8), s2769_plain_contract, 390, s2769_plain_checked⟩

def s2770_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s2770_plain_checked : check 103 s2770_plain_contract = true := by decide +kernel
def s2770_plain : CertifiedContract :=
  ⟨2770, 2767, 0, .none, s2770_plain_contract, 103, s2770_plain_checked⟩

def s2771_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s2771_zero_checked : check 350 s2771_zero_contract = true := by decide +kernel
def s2771_zero : CertifiedContract :=
  ⟨2771, 2774, 0, .none, s2771_zero_contract, 350, s2771_zero_checked⟩

def s2771_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s2771_positive_checked : check 350 s2771_positive_contract = true := by decide +kernel
def s2771_positive : CertifiedContract :=
  ⟨2771, 2772, 1, (.dec 8), s2771_positive_contract, 350, s2771_positive_checked⟩

def s2772_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, true, true, true, true] 0 (.inc 3)⟩
theorem s2772_plain_checked : check 366 s2772_plain_contract = true := by decide +kernel
def s2772_plain : CertifiedContract :=
  ⟨2772, 2773, 0, (.inc 3), s2772_plain_contract, 366, s2772_plain_checked⟩

def s2773_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s2773_plain_checked : check 94 s2773_plain_contract = true := by decide +kernel
def s2773_plain : CertifiedContract :=
  ⟨2773, 2771, 0, .none, s2773_plain_contract, 94, s2773_plain_checked⟩

def s2774_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s2774_zero_checked : check 344 s2774_zero_contract = true := by decide +kernel
def s2774_zero : CertifiedContract :=
  ⟨2774, 2777, 0, .none, s2774_zero_contract, 344, s2774_zero_checked⟩

def s2774_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2774_positive_checked : check 350 s2774_positive_contract = true := by decide +kernel
def s2774_positive : CertifiedContract :=
  ⟨2774, 2775, 1, (.dec 2), s2774_positive_contract, 350, s2774_positive_checked⟩

def s2775_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s2775_plain_checked : check 363 s2775_plain_contract = true := by decide +kernel
def s2775_plain : CertifiedContract :=
  ⟨2775, 2776, 0, (.inc 8), s2775_plain_contract, 363, s2775_plain_checked⟩

def s2776_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s2776_plain_checked : check 94 s2776_plain_contract = true := by decide +kernel
def s2776_plain : CertifiedContract :=
  ⟨2776, 2774, 0, .none, s2776_plain_contract, 94, s2776_plain_checked⟩

def s2777_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2777_zero_checked : check 365 s2777_zero_contract = true := by decide +kernel
def s2777_zero : CertifiedContract :=
  ⟨2777, 2780, 0, .none, s2777_zero_contract, 365, s2777_zero_checked⟩

def s2777_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2777_positive_checked : check 371 s2777_positive_contract = true := by decide +kernel
def s2777_positive : CertifiedContract :=
  ⟨2777, 2778, 1, (.dec 0), s2777_positive_contract, 371, s2777_positive_checked⟩

def s2778_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2778_plain_checked : check 363 s2778_plain_contract = true := by decide +kernel
def s2778_plain : CertifiedContract :=
  ⟨2778, 2779, 0, (.inc 2), s2778_plain_contract, 363, s2778_plain_checked⟩

def s2779_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s2779_plain_checked : check 97 s2779_plain_contract = true := by decide +kernel
def s2779_plain : CertifiedContract :=
  ⟨2779, 2777, 0, .none, s2779_plain_contract, 97, s2779_plain_checked⟩

def s2780_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2780_zero_checked : check 371 s2780_zero_contract = true := by decide +kernel
def s2780_zero : CertifiedContract :=
  ⟨2780, 2784, 0, .none, s2780_zero_contract, 371, s2780_zero_checked⟩

def s2780_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2780_positive_checked : check 377 s2780_positive_contract = true := by decide +kernel
def s2780_positive : CertifiedContract :=
  ⟨2780, 2781, 1, (.dec 2), s2780_positive_contract, 377, s2780_positive_checked⟩

def s2781_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2781_plain_checked : check 390 s2781_plain_contract = true := by decide +kernel
def s2781_plain : CertifiedContract :=
  ⟨2781, 2782, 0, (.inc 5), s2781_plain_contract, 390, s2781_plain_checked⟩

def s2782_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2782_plain_checked : check 417 s2782_plain_contract = true := by decide +kernel
def s2782_plain : CertifiedContract :=
  ⟨2782, 2783, 0, (.inc 8), s2782_plain_contract, 417, s2782_plain_checked⟩

def s2783_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2783_plain_checked : check 112 s2783_plain_contract = true := by decide +kernel
def s2783_plain : CertifiedContract :=
  ⟨2783, 2780, 0, .none, s2783_plain_contract, 112, s2783_plain_checked⟩

def s2784_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s2784_zero_checked : check 392 s2784_zero_contract = true := by decide +kernel
def s2784_zero : CertifiedContract :=
  ⟨2784, 2790, 0, .none, s2784_zero_contract, 392, s2784_zero_checked⟩

def s2784_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2784_positive_checked : check 395 s2784_positive_contract = true := by decide +kernel
def s2784_positive : CertifiedContract :=
  ⟨2784, 2785, 1, (.dec 8), s2784_positive_contract, 395, s2784_positive_checked⟩

def s2785_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2785_plain_checked : check 390 s2785_plain_contract = true := by decide +kernel
def s2785_plain : CertifiedContract :=
  ⟨2785, 2786, 0, (.inc 5), s2785_plain_contract, 390, s2785_plain_checked⟩

def s2786_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s2786_zero_checked : check 410 s2786_zero_contract = true := by decide +kernel
def s2786_zero : CertifiedContract :=
  ⟨2786, 2789, 0, .none, s2786_zero_contract, 410, s2786_zero_checked⟩

def s2786_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2786_positive_checked : check 413 s2786_positive_contract = true := by decide +kernel
def s2786_positive : CertifiedContract :=
  ⟨2786, 2787, 1, (.dec 8), s2786_positive_contract, 413, s2786_positive_checked⟩

def s2787_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2787_plain_checked : check 408 s2787_plain_contract = true := by decide +kernel
def s2787_plain : CertifiedContract :=
  ⟨2787, 2788, 0, (.inc 2), s2787_plain_contract, 408, s2787_plain_checked⟩

def s2788_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2788_plain_checked : check 112 s2788_plain_contract = true := by decide +kernel
def s2788_plain : CertifiedContract :=
  ⟨2788, 2786, 0, .none, s2788_plain_contract, 112, s2788_plain_checked⟩

def s2789_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2789_plain_checked : check 115 s2789_plain_contract = true := by decide +kernel
def s2789_plain : CertifiedContract :=
  ⟨2789, 2780, 0, .none, s2789_plain_contract, 115, s2789_plain_checked⟩

def s2790_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s2790_zero_checked : check 380 s2790_zero_contract = true := by decide +kernel
def s2790_zero : CertifiedContract :=
  ⟨2790, 2793, 0, .none, s2790_zero_contract, 380, s2790_zero_checked⟩

def s2790_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2790_positive_checked : check 377 s2790_positive_contract = true := by decide +kernel
def s2790_positive : CertifiedContract :=
  ⟨2790, 2791, 1, (.dec 5), s2790_positive_contract, 377, s2790_positive_checked⟩

def s2791_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2791_plain_checked : check 390 s2791_plain_contract = true := by decide +kernel
def s2791_plain : CertifiedContract :=
  ⟨2791, 2792, 0, (.inc 0), s2791_plain_contract, 390, s2791_plain_checked⟩

def s2792_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s2792_plain_checked : check 103 s2792_plain_contract = true := by decide +kernel
def s2792_plain : CertifiedContract :=
  ⟨2792, 2790, 0, .none, s2792_plain_contract, 103, s2792_plain_checked⟩

def s2793_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s2793_zero_checked : check 344 s2793_zero_contract = true := by decide +kernel
def s2793_zero : CertifiedContract :=
  ⟨2793, 2797, 0, .none, s2793_zero_contract, 344, s2793_zero_checked⟩

def s2793_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s2793_positive_checked : check 350 s2793_positive_contract = true := by decide +kernel
def s2793_positive : CertifiedContract :=
  ⟨2793, 2794, 1, (.dec 7), s2793_positive_contract, 350, s2793_positive_checked⟩

def s2794_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2794_plain_checked : check 354 s2794_plain_contract = true := by decide +kernel
def s2794_plain : CertifiedContract :=
  ⟨2794, 2795, 0, (.inc 2), s2794_plain_contract, 354, s2794_plain_checked⟩

def s2795_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2795_plain_checked : check 381 s2795_plain_contract = true := by decide +kernel
def s2795_plain : CertifiedContract :=
  ⟨2795, 2796, 0, (.inc 8), s2795_plain_contract, 381, s2795_plain_checked⟩

def s2796_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s2796_plain_checked : check 100 s2796_plain_contract = true := by decide +kernel
def s2796_plain : CertifiedContract :=
  ⟨2796, 2793, 0, .none, s2796_plain_contract, 100, s2796_plain_checked⟩

def s2797_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s2797_zero_checked : check 353 s2797_zero_contract = true := by decide +kernel
def s2797_zero : CertifiedContract :=
  ⟨2797, 2800, 0, .none, s2797_zero_contract, 353, s2797_zero_checked⟩

def s2797_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s2797_positive_checked : check 350 s2797_positive_contract = true := by decide +kernel
def s2797_positive : CertifiedContract :=
  ⟨2797, 2798, 1, (.dec 8), s2797_positive_contract, 350, s2797_positive_checked⟩

def s2798_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s2798_plain_checked : check 381 s2798_plain_contract = true := by decide +kernel
def s2798_plain : CertifiedContract :=
  ⟨2798, 2799, 0, (.inc 7), s2798_plain_contract, 381, s2798_plain_checked⟩

def s2799_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s2799_plain_checked : check 94 s2799_plain_contract = true := by decide +kernel
def s2799_plain : CertifiedContract :=
  ⟨2799, 2797, 0, .none, s2799_plain_contract, 94, s2799_plain_checked⟩

def s2800_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s2800_zero_checked : check 356 s2800_zero_contract = true := by decide +kernel
def s2800_zero : CertifiedContract :=
  ⟨2800, 2808, 0, .none, s2800_zero_contract, 356, s2800_zero_checked⟩

def s2800_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s2800_positive_checked : check 362 s2800_positive_contract = true := by decide +kernel
def s2800_positive : CertifiedContract :=
  ⟨2800, 2801, 1, (.dec 0), s2800_positive_contract, 362, s2800_positive_checked⟩

def s2801_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2801_plain_checked : check 372 s2801_plain_contract = true := by decide +kernel
def s2801_plain : CertifiedContract :=
  ⟨2801, 2802, 0, (.inc 5), s2801_plain_contract, 372, s2801_plain_checked⟩

def s2802_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2802_zero_checked : check 398 s2802_zero_contract = true := by decide +kernel
def s2802_zero : CertifiedContract :=
  ⟨2802, 2804, 0, .none, s2802_zero_contract, 398, s2802_zero_checked⟩

def s2802_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2802_positive_checked : check 404 s2802_positive_contract = true := by decide +kernel
def s2802_positive : CertifiedContract :=
  ⟨2802, 2803, 1, (.dec 8), s2802_positive_contract, 404, s2802_positive_checked⟩

def s2803_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s2803_plain_checked : check 109 s2803_plain_contract = true := by decide +kernel
def s2803_plain : CertifiedContract :=
  ⟨2803, 2807, 0, .none, s2803_plain_contract, 109, s2803_plain_checked⟩

def s2804_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s2804_zero_checked : check 410 s2804_zero_contract = true := by decide +kernel
def s2804_zero : CertifiedContract :=
  ⟨2804, 2807, 0, .none, s2804_zero_contract, 410, s2804_zero_checked⟩

def s2804_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2804_positive_checked : check 413 s2804_positive_contract = true := by decide +kernel
def s2804_positive : CertifiedContract :=
  ⟨2804, 2805, 1, (.dec 5), s2804_positive_contract, 413, s2804_positive_checked⟩

def s2805_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2805_plain_checked : check 417 s2805_plain_contract = true := by decide +kernel
def s2805_plain : CertifiedContract :=
  ⟨2805, 2806, 0, (.inc 8), s2805_plain_contract, 417, s2805_plain_checked⟩

def s2806_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2806_plain_checked : check 112 s2806_plain_contract = true := by decide +kernel
def s2806_plain : CertifiedContract :=
  ⟨2806, 2804, 0, .none, s2806_plain_contract, 112, s2806_plain_checked⟩

def s2807_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s2807_plain_checked : check 103 s2807_plain_contract = true := by decide +kernel
def s2807_plain : CertifiedContract :=
  ⟨2807, 2800, 0, .none, s2807_plain_contract, 103, s2807_plain_checked⟩

def s2808_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2808_zero_checked : check 356 s2808_zero_contract = true := by decide +kernel
def s2808_zero : CertifiedContract :=
  ⟨2808, 2811, 0, .none, s2808_zero_contract, 356, s2808_zero_checked⟩

def nonterminal : Array CertifiedContract := #[
  s2760_zero,
  s2760_positive,
  s2761_plain,
  s2762_plain,
  s2763_plain,
  s2764_zero,
  s2764_positive,
  s2765_plain,
  s2766_plain,
  s2767_zero,
  s2767_positive,
  s2768_plain,
  s2769_plain,
  s2770_plain,
  s2771_zero,
  s2771_positive,
  s2772_plain,
  s2773_plain,
  s2774_zero,
  s2774_positive,
  s2775_plain,
  s2776_plain,
  s2777_zero,
  s2777_positive,
  s2778_plain,
  s2779_plain,
  s2780_zero,
  s2780_positive,
  s2781_plain,
  s2782_plain,
  s2783_plain,
  s2784_zero,
  s2784_positive,
  s2785_plain,
  s2786_zero,
  s2786_positive,
  s2787_plain,
  s2788_plain,
  s2789_plain,
  s2790_zero,
  s2790_positive,
  s2791_plain,
  s2792_plain,
  s2793_zero,
  s2793_positive,
  s2794_plain,
  s2795_plain,
  s2796_plain,
  s2797_zero,
  s2797_positive,
  s2798_plain,
  s2799_plain,
  s2800_zero,
  s2800_positive,
  s2801_plain,
  s2802_zero,
  s2802_positive,
  s2803_plain,
  s2804_zero,
  s2804_positive,
  s2805_plain,
  s2806_plain,
  s2807_plain,
  s2808_zero
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S056
