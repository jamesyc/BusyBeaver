module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S057
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s2808_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s2808_positive_checked : check 359 s2808_positive_contract = true := by decide +kernel
def s2808_positive : CertifiedContract :=
  ⟨2808, 2809, 1, (.dec 5), s2808_positive_contract, 359, s2808_positive_checked⟩

def s2809_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s2809_plain_checked : check 372 s2809_plain_contract = true := by decide +kernel
def s2809_plain : CertifiedContract :=
  ⟨2809, 2810, 0, (.inc 0), s2809_plain_contract, 372, s2809_plain_checked⟩

def s2810_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s2810_plain_checked : check 97 s2810_plain_contract = true := by decide +kernel
def s2810_plain : CertifiedContract :=
  ⟨2810, 2808, 0, .none, s2810_plain_contract, 97, s2810_plain_checked⟩

def s2811_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s2811_zero_checked : check 353 s2811_zero_contract = true := by decide +kernel
def s2811_zero : CertifiedContract :=
  ⟨2811, 2815, 0, .none, s2811_zero_contract, 353, s2811_zero_checked⟩

def s2811_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2811_positive_checked : check 359 s2811_positive_contract = true := by decide +kernel
def s2811_positive : CertifiedContract :=
  ⟨2811, 2812, 1, (.dec 2), s2811_positive_contract, 359, s2811_positive_checked⟩

def s2812_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2812_plain_checked : check 372 s2812_plain_contract = true := by decide +kernel
def s2812_plain : CertifiedContract :=
  ⟨2812, 2813, 0, (.inc 5), s2812_plain_contract, 372, s2812_plain_checked⟩

def s2813_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2813_plain_checked : check 399 s2813_plain_contract = true := by decide +kernel
def s2813_plain : CertifiedContract :=
  ⟨2813, 2814, 0, (.inc 8), s2813_plain_contract, 399, s2813_plain_checked⟩

def s2814_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2814_plain_checked : check 106 s2814_plain_contract = true := by decide +kernel
def s2814_plain : CertifiedContract :=
  ⟨2814, 2811, 0, .none, s2814_plain_contract, 106, s2814_plain_checked⟩

def s2815_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s2815_zero_checked : check 374 s2815_zero_contract = true := by decide +kernel
def s2815_zero : CertifiedContract :=
  ⟨2815, 2821, 0, .none, s2815_zero_contract, 374, s2815_zero_checked⟩

def s2815_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2815_positive_checked : check 377 s2815_positive_contract = true := by decide +kernel
def s2815_positive : CertifiedContract :=
  ⟨2815, 2816, 1, (.dec 8), s2815_positive_contract, 377, s2815_positive_checked⟩

def s2816_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2816_plain_checked : check 372 s2816_plain_contract = true := by decide +kernel
def s2816_plain : CertifiedContract :=
  ⟨2816, 2817, 0, (.inc 5), s2816_plain_contract, 372, s2816_plain_checked⟩

def s2817_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s2817_zero_checked : check 392 s2817_zero_contract = true := by decide +kernel
def s2817_zero : CertifiedContract :=
  ⟨2817, 2820, 0, .none, s2817_zero_contract, 392, s2817_zero_checked⟩

def s2817_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2817_positive_checked : check 395 s2817_positive_contract = true := by decide +kernel
def s2817_positive : CertifiedContract :=
  ⟨2817, 2818, 1, (.dec 8), s2817_positive_contract, 395, s2817_positive_checked⟩

def s2818_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2818_plain_checked : check 390 s2818_plain_contract = true := by decide +kernel
def s2818_plain : CertifiedContract :=
  ⟨2818, 2819, 0, (.inc 2), s2818_plain_contract, 390, s2818_plain_checked⟩

def s2819_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2819_plain_checked : check 106 s2819_plain_contract = true := by decide +kernel
def s2819_plain : CertifiedContract :=
  ⟨2819, 2817, 0, .none, s2819_plain_contract, 106, s2819_plain_checked⟩

def s2820_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2820_plain_checked : check 109 s2820_plain_contract = true := by decide +kernel
def s2820_plain : CertifiedContract :=
  ⟨2820, 2811, 0, .none, s2820_plain_contract, 109, s2820_plain_checked⟩

def s2821_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, true] 0 .none⟩
theorem s2821_zero_checked : check 359 s2821_zero_contract = true := by decide +kernel
def s2821_zero : CertifiedContract :=
  ⟨2821, 2827, 0, .none, s2821_zero_contract, 359, s2821_zero_checked⟩

def s2821_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2821_positive_checked : check 359 s2821_positive_contract = true := by decide +kernel
def s2821_positive : CertifiedContract :=
  ⟨2821, 2822, 1, (.dec 5), s2821_positive_contract, 359, s2821_positive_checked⟩

def s2822_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2822_plain_checked : check 372 s2822_plain_contract = true := by decide +kernel
def s2822_plain : CertifiedContract :=
  ⟨2822, 2823, 0, (.inc 2), s2822_plain_contract, 372, s2822_plain_checked⟩

def s2823_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2823_plain_checked : check 375 s2823_plain_contract = true := by decide +kernel
def s2823_plain : CertifiedContract :=
  ⟨2823, 2824, 0, (.inc 2), s2823_plain_contract, 375, s2823_plain_checked⟩

def s2824_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2824_plain_checked : check 372 s2824_plain_contract = true := by decide +kernel
def s2824_plain : CertifiedContract :=
  ⟨2824, 2825, 0, (.inc 2), s2824_plain_contract, 372, s2824_plain_checked⟩

def s2825_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s2825_plain_checked : check 378 s2825_plain_contract = true := by decide +kernel
def s2825_plain : CertifiedContract :=
  ⟨2825, 2826, 0, (.inc 2), s2825_plain_contract, 378, s2825_plain_checked⟩

def s2826_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s2826_plain_checked : check 94 s2826_plain_contract = true := by decide +kernel
def s2826_plain : CertifiedContract :=
  ⟨2826, 2821, 0, .none, s2826_plain_contract, 94, s2826_plain_checked⟩

def s2827_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, false] 0 (.inc 2)⟩
theorem s2827_plain_checked : check 333 s2827_plain_contract = true := by decide +kernel
def s2827_plain : CertifiedContract :=
  ⟨2827, 2828, 0, (.inc 2), s2827_plain_contract, 333, s2827_plain_checked⟩

def s2828_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, true, false] 0 .none⟩
theorem s2828_zero_checked : check 356 s2828_zero_contract = true := by decide +kernel
def s2828_zero : CertifiedContract :=
  ⟨2828, 2836, 0, .none, s2828_zero_contract, 356, s2828_zero_checked⟩

def s2828_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s2828_positive_checked : check 362 s2828_positive_contract = true := by decide +kernel
def s2828_positive : CertifiedContract :=
  ⟨2828, 2829, 1, (.dec 0), s2828_positive_contract, 362, s2828_positive_checked⟩

def s2829_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2829_plain_checked : check 372 s2829_plain_contract = true := by decide +kernel
def s2829_plain : CertifiedContract :=
  ⟨2829, 2830, 0, (.inc 5), s2829_plain_contract, 372, s2829_plain_checked⟩

def s2830_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2830_zero_checked : check 398 s2830_zero_contract = true := by decide +kernel
def s2830_zero : CertifiedContract :=
  ⟨2830, 2832, 0, .none, s2830_zero_contract, 398, s2830_zero_checked⟩

def s2830_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2830_positive_checked : check 404 s2830_positive_contract = true := by decide +kernel
def s2830_positive : CertifiedContract :=
  ⟨2830, 2831, 1, (.dec 8), s2830_positive_contract, 404, s2830_positive_checked⟩

def s2831_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s2831_plain_checked : check 109 s2831_plain_contract = true := by decide +kernel
def s2831_plain : CertifiedContract :=
  ⟨2831, 2835, 0, .none, s2831_plain_contract, 109, s2831_plain_checked⟩

def s2832_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s2832_zero_checked : check 410 s2832_zero_contract = true := by decide +kernel
def s2832_zero : CertifiedContract :=
  ⟨2832, 2835, 0, .none, s2832_zero_contract, 410, s2832_zero_checked⟩

def s2832_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2832_positive_checked : check 413 s2832_positive_contract = true := by decide +kernel
def s2832_positive : CertifiedContract :=
  ⟨2832, 2833, 1, (.dec 5), s2832_positive_contract, 413, s2832_positive_checked⟩

def s2833_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2833_plain_checked : check 417 s2833_plain_contract = true := by decide +kernel
def s2833_plain : CertifiedContract :=
  ⟨2833, 2834, 0, (.inc 8), s2833_plain_contract, 417, s2833_plain_checked⟩

def s2834_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2834_plain_checked : check 112 s2834_plain_contract = true := by decide +kernel
def s2834_plain : CertifiedContract :=
  ⟨2834, 2832, 0, .none, s2834_plain_contract, 112, s2834_plain_checked⟩

def s2835_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, false, false] 0 .none⟩
theorem s2835_plain_checked : check 103 s2835_plain_contract = true := by decide +kernel
def s2835_plain : CertifiedContract :=
  ⟨2835, 2828, 0, .none, s2835_plain_contract, 103, s2835_plain_checked⟩

def s2836_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s2836_zero_checked : check 356 s2836_zero_contract = true := by decide +kernel
def s2836_zero : CertifiedContract :=
  ⟨2836, 2839, 0, .none, s2836_zero_contract, 356, s2836_zero_checked⟩

def s2836_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s2836_positive_checked : check 359 s2836_positive_contract = true := by decide +kernel
def s2836_positive : CertifiedContract :=
  ⟨2836, 2837, 1, (.dec 5), s2836_positive_contract, 359, s2836_positive_checked⟩

def s2837_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s2837_plain_checked : check 372 s2837_plain_contract = true := by decide +kernel
def s2837_plain : CertifiedContract :=
  ⟨2837, 2838, 0, (.inc 0), s2837_plain_contract, 372, s2837_plain_checked⟩

def s2838_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, false, true, false] 0 .none⟩
theorem s2838_plain_checked : check 97 s2838_plain_contract = true := by decide +kernel
def s2838_plain : CertifiedContract :=
  ⟨2838, 2836, 0, .none, s2838_plain_contract, 97, s2838_plain_checked⟩

def s2839_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, true, false] 0 .none⟩
theorem s2839_zero_checked : check 353 s2839_zero_contract = true := by decide +kernel
def s2839_zero : CertifiedContract :=
  ⟨2839, 2843, 0, .none, s2839_zero_contract, 353, s2839_zero_checked⟩

def s2839_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2839_positive_checked : check 359 s2839_positive_contract = true := by decide +kernel
def s2839_positive : CertifiedContract :=
  ⟨2839, 2840, 1, (.dec 2), s2839_positive_contract, 359, s2839_positive_checked⟩

def s2840_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2840_plain_checked : check 372 s2840_plain_contract = true := by decide +kernel
def s2840_plain : CertifiedContract :=
  ⟨2840, 2841, 0, (.inc 5), s2840_plain_contract, 372, s2840_plain_checked⟩

def s2841_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2841_plain_checked : check 399 s2841_plain_contract = true := by decide +kernel
def s2841_plain : CertifiedContract :=
  ⟨2841, 2842, 0, (.inc 8), s2841_plain_contract, 399, s2841_plain_checked⟩

def s2842_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s2842_plain_checked : check 106 s2842_plain_contract = true := by decide +kernel
def s2842_plain : CertifiedContract :=
  ⟨2842, 2839, 0, .none, s2842_plain_contract, 106, s2842_plain_checked⟩

def s2843_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, true, false] 0 .none⟩
theorem s2843_zero_checked : check 374 s2843_zero_contract = true := by decide +kernel
def s2843_zero : CertifiedContract :=
  ⟨2843, 2849, 0, .none, s2843_zero_contract, 374, s2843_zero_checked⟩

def s2843_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2843_positive_checked : check 377 s2843_positive_contract = true := by decide +kernel
def s2843_positive : CertifiedContract :=
  ⟨2843, 2844, 1, (.dec 8), s2843_positive_contract, 377, s2843_positive_checked⟩

def s2844_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2844_plain_checked : check 372 s2844_plain_contract = true := by decide +kernel
def s2844_plain : CertifiedContract :=
  ⟨2844, 2845, 0, (.inc 5), s2844_plain_contract, 372, s2844_plain_checked⟩

def s2845_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, true, true, true] 0 .none⟩
theorem s2845_zero_checked : check 392 s2845_zero_contract = true := by decide +kernel
def s2845_zero : CertifiedContract :=
  ⟨2845, 2848, 0, .none, s2845_zero_contract, 392, s2845_zero_checked⟩

def s2845_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2845_positive_checked : check 395 s2845_positive_contract = true := by decide +kernel
def s2845_positive : CertifiedContract :=
  ⟨2845, 2846, 1, (.dec 8), s2845_positive_contract, 395, s2845_positive_checked⟩

def s2846_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2846_plain_checked : check 390 s2846_plain_contract = true := by decide +kernel
def s2846_plain : CertifiedContract :=
  ⟨2846, 2847, 0, (.inc 2), s2846_plain_contract, 390, s2846_plain_checked⟩

def s2847_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2847_plain_checked : check 106 s2847_plain_contract = true := by decide +kernel
def s2847_plain : CertifiedContract :=
  ⟨2847, 2845, 0, .none, s2847_plain_contract, 106, s2847_plain_checked⟩

def s2848_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s2848_plain_checked : check 109 s2848_plain_contract = true := by decide +kernel
def s2848_plain : CertifiedContract :=
  ⟨2848, 2839, 0, .none, s2848_plain_contract, 109, s2848_plain_checked⟩

def s2849_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s2849_zero_checked : check 359 s2849_zero_contract = true := by decide +kernel
def s2849_zero : CertifiedContract :=
  ⟨2849, 2855, 0, .none, s2849_zero_contract, 359, s2849_zero_checked⟩

def s2849_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2849_positive_checked : check 359 s2849_positive_contract = true := by decide +kernel
def s2849_positive : CertifiedContract :=
  ⟨2849, 2850, 1, (.dec 5), s2849_positive_contract, 359, s2849_positive_checked⟩

def s2850_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2850_plain_checked : check 372 s2850_plain_contract = true := by decide +kernel
def s2850_plain : CertifiedContract :=
  ⟨2850, 2851, 0, (.inc 2), s2850_plain_contract, 372, s2850_plain_checked⟩

def s2851_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2851_plain_checked : check 375 s2851_plain_contract = true := by decide +kernel
def s2851_plain : CertifiedContract :=
  ⟨2851, 2852, 0, (.inc 2), s2851_plain_contract, 375, s2851_plain_checked⟩

def s2852_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2852_plain_checked : check 372 s2852_plain_contract = true := by decide +kernel
def s2852_plain : CertifiedContract :=
  ⟨2852, 2853, 0, (.inc 2), s2852_plain_contract, 372, s2852_plain_checked⟩

def s2853_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s2853_plain_checked : check 378 s2853_plain_contract = true := by decide +kernel
def s2853_plain : CertifiedContract :=
  ⟨2853, 2854, 0, (.inc 2), s2853_plain_contract, 378, s2853_plain_checked⟩

def s2854_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, false, true, true, false] 0 .none⟩
theorem s2854_plain_checked : check 94 s2854_plain_contract = true := by decide +kernel
def s2854_plain : CertifiedContract :=
  ⟨2854, 2849, 0, .none, s2854_plain_contract, 94, s2854_plain_checked⟩

def s2855_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2855_plain_checked : check 327 s2855_plain_contract = true := by decide +kernel
def s2855_plain : CertifiedContract :=
  ⟨2855, 2856, 0, (.inc 2), s2855_plain_contract, 327, s2855_plain_checked⟩

def s2856_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, false] 0 (.inc 2)⟩
theorem s2856_plain_checked : check 333 s2856_plain_contract = true := by decide +kernel
def s2856_plain : CertifiedContract :=
  ⟨2856, 2857, 0, (.inc 2), s2856_plain_contract, 333, s2856_plain_checked⟩

def s2857_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, true, false] 0 .none⟩
theorem s2857_zero_checked : check 347 s2857_zero_contract = true := by decide +kernel
def s2857_zero : CertifiedContract :=
  ⟨2857, 2865, 0, .none, s2857_zero_contract, 347, s2857_zero_checked⟩

def s2857_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, false] 1 (.dec 0)⟩
theorem s2857_positive_checked : check 353 s2857_positive_contract = true := by decide +kernel
def s2857_positive : CertifiedContract :=
  ⟨2857, 2858, 1, (.dec 0), s2857_positive_contract, 353, s2857_positive_checked⟩

def s2858_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2858_plain_checked : check 363 s2858_plain_contract = true := by decide +kernel
def s2858_plain : CertifiedContract :=
  ⟨2858, 2859, 0, (.inc 5), s2858_plain_contract, 363, s2858_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s2808_positive,
  s2809_plain,
  s2810_plain,
  s2811_zero,
  s2811_positive,
  s2812_plain,
  s2813_plain,
  s2814_plain,
  s2815_zero,
  s2815_positive,
  s2816_plain,
  s2817_zero,
  s2817_positive,
  s2818_plain,
  s2819_plain,
  s2820_plain,
  s2821_zero,
  s2821_positive,
  s2822_plain,
  s2823_plain,
  s2824_plain,
  s2825_plain,
  s2826_plain,
  s2827_plain,
  s2828_zero,
  s2828_positive,
  s2829_plain,
  s2830_zero,
  s2830_positive,
  s2831_plain,
  s2832_zero,
  s2832_positive,
  s2833_plain,
  s2834_plain,
  s2835_plain,
  s2836_zero,
  s2836_positive,
  s2837_plain,
  s2838_plain,
  s2839_zero,
  s2839_positive,
  s2840_plain,
  s2841_plain,
  s2842_plain,
  s2843_zero,
  s2843_positive,
  s2844_plain,
  s2845_zero,
  s2845_positive,
  s2846_plain,
  s2847_plain,
  s2848_plain,
  s2849_zero,
  s2849_positive,
  s2850_plain,
  s2851_plain,
  s2852_plain,
  s2853_plain,
  s2854_plain,
  s2855_plain,
  s2856_plain,
  s2857_zero,
  s2857_positive,
  s2858_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S057
