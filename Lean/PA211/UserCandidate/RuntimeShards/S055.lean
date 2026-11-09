import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S055
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s2710_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2710_plain_checked : check 337 s2710_plain_contract = true := by decide +kernel
def s2710_plain : CertifiedContract :=
  ⟨2710, 2711, 0, (.inc 5), s2710_plain_contract, 337, s2710_plain_checked⟩

def s2711_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s2711_zero_checked : check 357 s2711_zero_contract = true := by decide +kernel
def s2711_zero : CertifiedContract :=
  ⟨2711, 2714, 0, .none, s2711_zero_contract, 357, s2711_zero_checked⟩

def s2711_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2711_positive_checked : check 360 s2711_positive_contract = true := by decide +kernel
def s2711_positive : CertifiedContract :=
  ⟨2711, 2712, 1, (.dec 8), s2711_positive_contract, 360, s2711_positive_checked⟩

def s2712_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2712_plain_checked : check 355 s2712_plain_contract = true := by decide +kernel
def s2712_plain : CertifiedContract :=
  ⟨2712, 2713, 0, (.inc 2), s2712_plain_contract, 355, s2712_plain_checked⟩

def s2713_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2713_plain_checked : check 95 s2713_plain_contract = true := by decide +kernel
def s2713_plain : CertifiedContract :=
  ⟨2713, 2711, 0, .none, s2713_plain_contract, 95, s2713_plain_checked⟩

def s2714_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2714_plain_checked : check 98 s2714_plain_contract = true := by decide +kernel
def s2714_plain : CertifiedContract :=
  ⟨2714, 2705, 0, .none, s2714_plain_contract, 98, s2714_plain_checked⟩

def s2715_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, true] 0 .none⟩
theorem s2715_zero_checked : check 324 s2715_zero_contract = true := by decide +kernel
def s2715_zero : CertifiedContract :=
  ⟨2715, 2721, 0, .none, s2715_zero_contract, 324, s2715_zero_checked⟩

def s2715_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2715_positive_checked : check 324 s2715_positive_contract = true := by decide +kernel
def s2715_positive : CertifiedContract :=
  ⟨2715, 2716, 1, (.dec 5), s2715_positive_contract, 324, s2715_positive_checked⟩

def s2716_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2716_plain_checked : check 337 s2716_plain_contract = true := by decide +kernel
def s2716_plain : CertifiedContract :=
  ⟨2716, 2717, 0, (.inc 2), s2716_plain_contract, 337, s2716_plain_checked⟩

def s2717_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2717_plain_checked : check 340 s2717_plain_contract = true := by decide +kernel
def s2717_plain : CertifiedContract :=
  ⟨2717, 2718, 0, (.inc 2), s2717_plain_contract, 340, s2717_plain_checked⟩

def s2718_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2718_plain_checked : check 346 s2718_plain_contract = true := by decide +kernel
def s2718_plain : CertifiedContract :=
  ⟨2718, 2719, 0, (.inc 2), s2718_plain_contract, 346, s2718_plain_checked⟩

def s2719_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s2719_plain_checked : check 352 s2719_plain_contract = true := by decide +kernel
def s2719_plain : CertifiedContract :=
  ⟨2719, 2720, 0, (.inc 2), s2719_plain_contract, 352, s2719_plain_checked⟩

def s2720_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s2720_plain_checked : check 83 s2720_plain_contract = true := by decide +kernel
def s2720_plain : CertifiedContract :=
  ⟨2720, 2715, 0, .none, s2720_plain_contract, 83, s2720_plain_checked⟩

def s2721_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, false, false] 0 (.inc 2)⟩
theorem s2721_plain_checked : check 298 s2721_plain_contract = true := by decide +kernel
def s2721_plain : CertifiedContract :=
  ⟨2721, 2722, 0, (.inc 2), s2721_plain_contract, 298, s2721_plain_checked⟩

def s2722_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s2722_zero_checked : check 318 s2722_zero_contract = true := by decide +kernel
def s2722_zero : CertifiedContract :=
  ⟨2722, 2725, 0, .none, s2722_zero_contract, 318, s2722_zero_checked⟩

def s2722_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s2722_positive_checked : check 324 s2722_positive_contract = true := by decide +kernel
def s2722_positive : CertifiedContract :=
  ⟨2722, 2723, 1, (.dec 2), s2722_positive_contract, 324, s2722_positive_checked⟩

def s2723_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s2723_plain_checked : check 337 s2723_plain_contract = true := by decide +kernel
def s2723_plain : CertifiedContract :=
  ⟨2723, 2724, 0, (.inc 8), s2723_plain_contract, 337, s2723_plain_checked⟩

def s2724_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s2724_plain_checked : check 86 s2724_plain_contract = true := by decide +kernel
def s2724_plain : CertifiedContract :=
  ⟨2724, 2722, 0, .none, s2724_plain_contract, 86, s2724_plain_checked⟩

def s2725_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2725_zero_checked : check 339 s2725_zero_contract = true := by decide +kernel
def s2725_zero : CertifiedContract :=
  ⟨2725, 2728, 0, .none, s2725_zero_contract, 339, s2725_zero_checked⟩

def s2725_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2725_positive_checked : check 345 s2725_positive_contract = true := by decide +kernel
def s2725_positive : CertifiedContract :=
  ⟨2725, 2726, 1, (.dec 0), s2725_positive_contract, 345, s2725_positive_checked⟩

def s2726_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2726_plain_checked : check 337 s2726_plain_contract = true := by decide +kernel
def s2726_plain : CertifiedContract :=
  ⟨2726, 2727, 0, (.inc 2), s2726_plain_contract, 337, s2726_plain_checked⟩

def s2727_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s2727_plain_checked : check 89 s2727_plain_contract = true := by decide +kernel
def s2727_plain : CertifiedContract :=
  ⟨2727, 2725, 0, .none, s2727_plain_contract, 89, s2727_plain_checked⟩

def s2728_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2728_zero_checked : check 345 s2728_zero_contract = true := by decide +kernel
def s2728_zero : CertifiedContract :=
  ⟨2728, 2732, 0, .none, s2728_zero_contract, 345, s2728_zero_checked⟩

def s2728_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2728_positive_checked : check 351 s2728_positive_contract = true := by decide +kernel
def s2728_positive : CertifiedContract :=
  ⟨2728, 2729, 1, (.dec 2), s2728_positive_contract, 351, s2728_positive_checked⟩

def s2729_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2729_plain_checked : check 364 s2729_plain_contract = true := by decide +kernel
def s2729_plain : CertifiedContract :=
  ⟨2729, 2730, 0, (.inc 5), s2729_plain_contract, 364, s2729_plain_checked⟩

def s2730_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2730_plain_checked : check 391 s2730_plain_contract = true := by decide +kernel
def s2730_plain : CertifiedContract :=
  ⟨2730, 2731, 0, (.inc 8), s2730_plain_contract, 391, s2730_plain_checked⟩

def s2731_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2731_plain_checked : check 104 s2731_plain_contract = true := by decide +kernel
def s2731_plain : CertifiedContract :=
  ⟨2731, 2728, 0, .none, s2731_plain_contract, 104, s2731_plain_checked⟩

def s2732_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s2732_zero_checked : check 366 s2732_zero_contract = true := by decide +kernel
def s2732_zero : CertifiedContract :=
  ⟨2732, 2738, 0, .none, s2732_zero_contract, 366, s2732_zero_checked⟩

def s2732_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2732_positive_checked : check 369 s2732_positive_contract = true := by decide +kernel
def s2732_positive : CertifiedContract :=
  ⟨2732, 2733, 1, (.dec 8), s2732_positive_contract, 369, s2732_positive_checked⟩

def s2733_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2733_plain_checked : check 364 s2733_plain_contract = true := by decide +kernel
def s2733_plain : CertifiedContract :=
  ⟨2733, 2734, 0, (.inc 5), s2733_plain_contract, 364, s2733_plain_checked⟩

def s2734_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s2734_zero_checked : check 384 s2734_zero_contract = true := by decide +kernel
def s2734_zero : CertifiedContract :=
  ⟨2734, 2737, 0, .none, s2734_zero_contract, 384, s2734_zero_checked⟩

def s2734_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2734_positive_checked : check 387 s2734_positive_contract = true := by decide +kernel
def s2734_positive : CertifiedContract :=
  ⟨2734, 2735, 1, (.dec 8), s2734_positive_contract, 387, s2734_positive_checked⟩

def s2735_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2735_plain_checked : check 382 s2735_plain_contract = true := by decide +kernel
def s2735_plain : CertifiedContract :=
  ⟨2735, 2736, 0, (.inc 2), s2735_plain_contract, 382, s2735_plain_checked⟩

def s2736_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2736_plain_checked : check 104 s2736_plain_contract = true := by decide +kernel
def s2736_plain : CertifiedContract :=
  ⟨2736, 2734, 0, .none, s2736_plain_contract, 104, s2736_plain_checked⟩

def s2737_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2737_plain_checked : check 107 s2737_plain_contract = true := by decide +kernel
def s2737_plain : CertifiedContract :=
  ⟨2737, 2728, 0, .none, s2737_plain_contract, 107, s2737_plain_checked⟩

def s2738_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s2738_zero_checked : check 354 s2738_zero_contract = true := by decide +kernel
def s2738_zero : CertifiedContract :=
  ⟨2738, 2741, 0, .none, s2738_zero_contract, 354, s2738_zero_checked⟩

def s2738_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2738_positive_checked : check 351 s2738_positive_contract = true := by decide +kernel
def s2738_positive : CertifiedContract :=
  ⟨2738, 2739, 1, (.dec 5), s2738_positive_contract, 351, s2738_positive_checked⟩

def s2739_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2739_plain_checked : check 364 s2739_plain_contract = true := by decide +kernel
def s2739_plain : CertifiedContract :=
  ⟨2739, 2740, 0, (.inc 0), s2739_plain_contract, 364, s2739_plain_checked⟩

def s2740_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s2740_plain_checked : check 95 s2740_plain_contract = true := by decide +kernel
def s2740_plain : CertifiedContract :=
  ⟨2740, 2738, 0, .none, s2740_plain_contract, 95, s2740_plain_checked⟩

def s2741_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s2741_zero_checked : check 318 s2741_zero_contract = true := by decide +kernel
def s2741_zero : CertifiedContract :=
  ⟨2741, 2745, 0, .none, s2741_zero_contract, 318, s2741_zero_checked⟩

def s2741_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, true, false, true, false] 1 (.dec 4)⟩
theorem s2741_positive_checked : check 324 s2741_positive_contract = true := by decide +kernel
def s2741_positive : CertifiedContract :=
  ⟨2741, 2742, 1, (.dec 4), s2741_positive_contract, 324, s2741_positive_checked⟩

def s2742_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2742_plain_checked : check 337 s2742_plain_contract = true := by decide +kernel
def s2742_plain : CertifiedContract :=
  ⟨2742, 2743, 0, (.inc 2), s2742_plain_contract, 337, s2742_plain_checked⟩

def s2743_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2743_plain_checked : check 364 s2743_plain_contract = true := by decide +kernel
def s2743_plain : CertifiedContract :=
  ⟨2743, 2744, 0, (.inc 8), s2743_plain_contract, 364, s2743_plain_checked⟩

def s2744_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s2744_plain_checked : check 95 s2744_plain_contract = true := by decide +kernel
def s2744_plain : CertifiedContract :=
  ⟨2744, 2741, 0, .none, s2744_plain_contract, 95, s2744_plain_checked⟩

def s2745_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s2745_zero_checked : check 324 s2745_zero_contract = true := by decide +kernel
def s2745_zero : CertifiedContract :=
  ⟨2745, 2748, 0, .none, s2745_zero_contract, 324, s2745_zero_checked⟩

def s2745_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s2745_positive_checked : check 324 s2745_positive_contract = true := by decide +kernel
def s2745_positive : CertifiedContract :=
  ⟨2745, 2746, 1, (.dec 8), s2745_positive_contract, 324, s2745_positive_checked⟩

def s2746_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, true, true, true, true] 0 (.inc 4)⟩
theorem s2746_plain_checked : check 328 s2746_plain_contract = true := by decide +kernel
def s2746_plain : CertifiedContract :=
  ⟨2746, 2747, 0, (.inc 4), s2746_plain_contract, 328, s2746_plain_checked⟩

def s2747_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s2747_plain_checked : check 86 s2747_plain_contract = true := by decide +kernel
def s2747_plain : CertifiedContract :=
  ⟨2747, 2745, 0, .none, s2747_plain_contract, 86, s2747_plain_checked⟩

def s2748_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s2748_zero_checked : check 345 s2748_zero_contract = true := by decide +kernel
def s2748_zero : CertifiedContract :=
  ⟨2748, 2751, 0, .none, s2748_zero_contract, 345, s2748_zero_checked⟩

def s2748_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s2748_positive_checked : check 351 s2748_positive_contract = true := by decide +kernel
def s2748_positive : CertifiedContract :=
  ⟨2748, 2749, 1, (.dec 2), s2748_positive_contract, 351, s2748_positive_checked⟩

def s2749_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s2749_plain_checked : check 364 s2749_plain_contract = true := by decide +kernel
def s2749_plain : CertifiedContract :=
  ⟨2749, 2750, 0, (.inc 8), s2749_plain_contract, 364, s2749_plain_checked⟩

def s2750_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s2750_plain_checked : check 95 s2750_plain_contract = true := by decide +kernel
def s2750_plain : CertifiedContract :=
  ⟨2750, 2748, 0, .none, s2750_plain_contract, 95, s2750_plain_checked⟩

def s2751_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2751_zero_checked : check 366 s2751_zero_contract = true := by decide +kernel
def s2751_zero : CertifiedContract :=
  ⟨2751, 2754, 0, .none, s2751_zero_contract, 366, s2751_zero_checked⟩

def s2751_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2751_positive_checked : check 372 s2751_positive_contract = true := by decide +kernel
def s2751_positive : CertifiedContract :=
  ⟨2751, 2752, 1, (.dec 0), s2751_positive_contract, 372, s2751_positive_checked⟩

def s2752_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2752_plain_checked : check 364 s2752_plain_contract = true := by decide +kernel
def s2752_plain : CertifiedContract :=
  ⟨2752, 2753, 0, (.inc 2), s2752_plain_contract, 364, s2752_plain_checked⟩

def s2753_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s2753_plain_checked : check 98 s2753_plain_contract = true := by decide +kernel
def s2753_plain : CertifiedContract :=
  ⟨2753, 2751, 0, .none, s2753_plain_contract, 98, s2753_plain_checked⟩

def s2754_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2754_zero_checked : check 372 s2754_zero_contract = true := by decide +kernel
def s2754_zero : CertifiedContract :=
  ⟨2754, 2758, 0, .none, s2754_zero_contract, 372, s2754_zero_checked⟩

def s2754_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2754_positive_checked : check 378 s2754_positive_contract = true := by decide +kernel
def s2754_positive : CertifiedContract :=
  ⟨2754, 2755, 1, (.dec 2), s2754_positive_contract, 378, s2754_positive_checked⟩

def s2755_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2755_plain_checked : check 391 s2755_plain_contract = true := by decide +kernel
def s2755_plain : CertifiedContract :=
  ⟨2755, 2756, 0, (.inc 5), s2755_plain_contract, 391, s2755_plain_checked⟩

def s2756_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2756_plain_checked : check 418 s2756_plain_contract = true := by decide +kernel
def s2756_plain : CertifiedContract :=
  ⟨2756, 2757, 0, (.inc 8), s2756_plain_contract, 418, s2756_plain_checked⟩

def s2757_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2757_plain_checked : check 113 s2757_plain_contract = true := by decide +kernel
def s2757_plain : CertifiedContract :=
  ⟨2757, 2754, 0, .none, s2757_plain_contract, 113, s2757_plain_checked⟩

def s2758_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s2758_zero_checked : check 393 s2758_zero_contract = true := by decide +kernel
def s2758_zero : CertifiedContract :=
  ⟨2758, 2764, 0, .none, s2758_zero_contract, 393, s2758_zero_checked⟩

def s2758_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2758_positive_checked : check 396 s2758_positive_contract = true := by decide +kernel
def s2758_positive : CertifiedContract :=
  ⟨2758, 2759, 1, (.dec 8), s2758_positive_contract, 396, s2758_positive_checked⟩

def s2759_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2759_plain_checked : check 391 s2759_plain_contract = true := by decide +kernel
def s2759_plain : CertifiedContract :=
  ⟨2759, 2760, 0, (.inc 5), s2759_plain_contract, 391, s2759_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S055
