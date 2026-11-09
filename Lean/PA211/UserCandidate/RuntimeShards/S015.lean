module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S015
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s0735_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0735_plain_checked : check 418 s0735_plain_contract = true := by decide +kernel
def s0735_plain : CertifiedContract :=
  ⟨735, 736, 0, (.inc 2), s0735_plain_contract, 418, s0735_plain_checked⟩

def s0736_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0736_plain_checked : check 116 s0736_plain_contract = true := by decide +kernel
def s0736_plain : CertifiedContract :=
  ⟨736, 734, 0, .none, s0736_plain_contract, 116, s0736_plain_checked⟩

def s0737_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0737_plain_checked : check 119 s0737_plain_contract = true := by decide +kernel
def s0737_plain : CertifiedContract :=
  ⟨737, 728, 0, .none, s0737_plain_contract, 119, s0737_plain_checked⟩

def s0738_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s0738_zero_checked : check 390 s0738_zero_contract = true := by decide +kernel
def s0738_zero : CertifiedContract :=
  ⟨738, 741, 0, .none, s0738_zero_contract, 390, s0738_zero_checked⟩

def s0738_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0738_positive_checked : check 387 s0738_positive_contract = true := by decide +kernel
def s0738_positive : CertifiedContract :=
  ⟨738, 739, 1, (.dec 5), s0738_positive_contract, 387, s0738_positive_checked⟩

def s0739_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0739_plain_checked : check 400 s0739_plain_contract = true := by decide +kernel
def s0739_plain : CertifiedContract :=
  ⟨739, 740, 0, (.inc 0), s0739_plain_contract, 400, s0739_plain_checked⟩

def s0740_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s0740_plain_checked : check 107 s0740_plain_contract = true := by decide +kernel
def s0740_plain : CertifiedContract :=
  ⟨740, 738, 0, .none, s0740_plain_contract, 107, s0740_plain_checked⟩

def s0741_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s0741_zero_checked : check 354 s0741_zero_contract = true := by decide +kernel
def s0741_zero : CertifiedContract :=
  ⟨741, 745, 0, .none, s0741_zero_contract, 354, s0741_zero_checked⟩

def s0741_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, true, false, true, false] 1 (.dec 3)⟩
theorem s0741_positive_checked : check 360 s0741_positive_contract = true := by decide +kernel
def s0741_positive : CertifiedContract :=
  ⟨741, 742, 1, (.dec 3), s0741_positive_contract, 360, s0741_positive_checked⟩

def s0742_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0742_plain_checked : check 373 s0742_plain_contract = true := by decide +kernel
def s0742_plain : CertifiedContract :=
  ⟨742, 743, 0, (.inc 2), s0742_plain_contract, 373, s0742_plain_checked⟩

def s0743_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0743_plain_checked : check 400 s0743_plain_contract = true := by decide +kernel
def s0743_plain : CertifiedContract :=
  ⟨743, 744, 0, (.inc 8), s0743_plain_contract, 400, s0743_plain_checked⟩

def s0744_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s0744_plain_checked : check 107 s0744_plain_contract = true := by decide +kernel
def s0744_plain : CertifiedContract :=
  ⟨744, 741, 0, .none, s0744_plain_contract, 107, s0744_plain_checked⟩

def s0745_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0745_zero_checked : check 360 s0745_zero_contract = true := by decide +kernel
def s0745_zero : CertifiedContract :=
  ⟨745, 748, 0, .none, s0745_zero_contract, 360, s0745_zero_checked⟩

def s0745_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s0745_positive_checked : check 360 s0745_positive_contract = true := by decide +kernel
def s0745_positive : CertifiedContract :=
  ⟨745, 746, 1, (.dec 8), s0745_positive_contract, 360, s0745_positive_checked⟩

def s0746_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, true, true, true, true] 0 (.inc 3)⟩
theorem s0746_plain_checked : check 376 s0746_plain_contract = true := by decide +kernel
def s0746_plain : CertifiedContract :=
  ⟨746, 747, 0, (.inc 3), s0746_plain_contract, 376, s0746_plain_checked⟩

def s0747_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s0747_plain_checked : check 98 s0747_plain_contract = true := by decide +kernel
def s0747_plain : CertifiedContract :=
  ⟨747, 745, 0, .none, s0747_plain_contract, 98, s0747_plain_checked⟩

def s0748_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s0748_zero_checked : check 354 s0748_zero_contract = true := by decide +kernel
def s0748_zero : CertifiedContract :=
  ⟨748, 751, 0, .none, s0748_zero_contract, 354, s0748_zero_checked⟩

def s0748_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0748_positive_checked : check 360 s0748_positive_contract = true := by decide +kernel
def s0748_positive : CertifiedContract :=
  ⟨748, 749, 1, (.dec 2), s0748_positive_contract, 360, s0748_positive_checked⟩

def s0749_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s0749_plain_checked : check 373 s0749_plain_contract = true := by decide +kernel
def s0749_plain : CertifiedContract :=
  ⟨749, 750, 0, (.inc 8), s0749_plain_contract, 373, s0749_plain_checked⟩

def s0750_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0750_plain_checked : check 98 s0750_plain_contract = true := by decide +kernel
def s0750_plain : CertifiedContract :=
  ⟨750, 748, 0, .none, s0750_plain_contract, 98, s0750_plain_checked⟩

def s0751_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0751_zero_checked : check 375 s0751_zero_contract = true := by decide +kernel
def s0751_zero : CertifiedContract :=
  ⟨751, 754, 0, .none, s0751_zero_contract, 375, s0751_zero_checked⟩

def s0751_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0751_positive_checked : check 381 s0751_positive_contract = true := by decide +kernel
def s0751_positive : CertifiedContract :=
  ⟨751, 752, 1, (.dec 0), s0751_positive_contract, 381, s0751_positive_checked⟩

def s0752_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0752_plain_checked : check 373 s0752_plain_contract = true := by decide +kernel
def s0752_plain : CertifiedContract :=
  ⟨752, 753, 0, (.inc 2), s0752_plain_contract, 373, s0752_plain_checked⟩

def s0753_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s0753_plain_checked : check 101 s0753_plain_contract = true := by decide +kernel
def s0753_plain : CertifiedContract :=
  ⟨753, 751, 0, .none, s0753_plain_contract, 101, s0753_plain_checked⟩

def s0754_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0754_zero_checked : check 381 s0754_zero_contract = true := by decide +kernel
def s0754_zero : CertifiedContract :=
  ⟨754, 758, 0, .none, s0754_zero_contract, 381, s0754_zero_checked⟩

def s0754_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0754_positive_checked : check 387 s0754_positive_contract = true := by decide +kernel
def s0754_positive : CertifiedContract :=
  ⟨754, 755, 1, (.dec 2), s0754_positive_contract, 387, s0754_positive_checked⟩

def s0755_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0755_plain_checked : check 400 s0755_plain_contract = true := by decide +kernel
def s0755_plain : CertifiedContract :=
  ⟨755, 756, 0, (.inc 5), s0755_plain_contract, 400, s0755_plain_checked⟩

def s0756_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0756_plain_checked : check 427 s0756_plain_contract = true := by decide +kernel
def s0756_plain : CertifiedContract :=
  ⟨756, 757, 0, (.inc 8), s0756_plain_contract, 427, s0756_plain_checked⟩

def s0757_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0757_plain_checked : check 116 s0757_plain_contract = true := by decide +kernel
def s0757_plain : CertifiedContract :=
  ⟨757, 754, 0, .none, s0757_plain_contract, 116, s0757_plain_checked⟩

def s0758_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s0758_zero_checked : check 402 s0758_zero_contract = true := by decide +kernel
def s0758_zero : CertifiedContract :=
  ⟨758, 764, 0, .none, s0758_zero_contract, 402, s0758_zero_checked⟩

def s0758_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0758_positive_checked : check 405 s0758_positive_contract = true := by decide +kernel
def s0758_positive : CertifiedContract :=
  ⟨758, 759, 1, (.dec 8), s0758_positive_contract, 405, s0758_positive_checked⟩

def s0759_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0759_plain_checked : check 400 s0759_plain_contract = true := by decide +kernel
def s0759_plain : CertifiedContract :=
  ⟨759, 760, 0, (.inc 5), s0759_plain_contract, 400, s0759_plain_checked⟩

def s0760_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s0760_zero_checked : check 420 s0760_zero_contract = true := by decide +kernel
def s0760_zero : CertifiedContract :=
  ⟨760, 763, 0, .none, s0760_zero_contract, 420, s0760_zero_checked⟩

def s0760_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0760_positive_checked : check 423 s0760_positive_contract = true := by decide +kernel
def s0760_positive : CertifiedContract :=
  ⟨760, 761, 1, (.dec 8), s0760_positive_contract, 423, s0760_positive_checked⟩

def s0761_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0761_plain_checked : check 418 s0761_plain_contract = true := by decide +kernel
def s0761_plain : CertifiedContract :=
  ⟨761, 762, 0, (.inc 2), s0761_plain_contract, 418, s0761_plain_checked⟩

def s0762_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0762_plain_checked : check 116 s0762_plain_contract = true := by decide +kernel
def s0762_plain : CertifiedContract :=
  ⟨762, 760, 0, .none, s0762_plain_contract, 116, s0762_plain_checked⟩

def s0763_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0763_plain_checked : check 119 s0763_plain_contract = true := by decide +kernel
def s0763_plain : CertifiedContract :=
  ⟨763, 754, 0, .none, s0763_plain_contract, 119, s0763_plain_checked⟩

def s0764_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s0764_zero_checked : check 390 s0764_zero_contract = true := by decide +kernel
def s0764_zero : CertifiedContract :=
  ⟨764, 767, 0, .none, s0764_zero_contract, 390, s0764_zero_checked⟩

def s0764_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0764_positive_checked : check 387 s0764_positive_contract = true := by decide +kernel
def s0764_positive : CertifiedContract :=
  ⟨764, 765, 1, (.dec 5), s0764_positive_contract, 387, s0764_positive_checked⟩

def s0765_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0765_plain_checked : check 400 s0765_plain_contract = true := by decide +kernel
def s0765_plain : CertifiedContract :=
  ⟨765, 766, 0, (.inc 0), s0765_plain_contract, 400, s0765_plain_checked⟩

def s0766_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s0766_plain_checked : check 107 s0766_plain_contract = true := by decide +kernel
def s0766_plain : CertifiedContract :=
  ⟨766, 764, 0, .none, s0766_plain_contract, 107, s0766_plain_checked⟩

def s0767_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s0767_zero_checked : check 354 s0767_zero_contract = true := by decide +kernel
def s0767_zero : CertifiedContract :=
  ⟨767, 771, 0, .none, s0767_zero_contract, 354, s0767_zero_checked⟩

def s0767_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s0767_positive_checked : check 360 s0767_positive_contract = true := by decide +kernel
def s0767_positive : CertifiedContract :=
  ⟨767, 768, 1, (.dec 7), s0767_positive_contract, 360, s0767_positive_checked⟩

def s0768_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0768_plain_checked : check 364 s0768_plain_contract = true := by decide +kernel
def s0768_plain : CertifiedContract :=
  ⟨768, 769, 0, (.inc 2), s0768_plain_contract, 364, s0768_plain_checked⟩

def s0769_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0769_plain_checked : check 391 s0769_plain_contract = true := by decide +kernel
def s0769_plain : CertifiedContract :=
  ⟨769, 770, 0, (.inc 8), s0769_plain_contract, 391, s0769_plain_checked⟩

def s0770_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s0770_plain_checked : check 104 s0770_plain_contract = true := by decide +kernel
def s0770_plain : CertifiedContract :=
  ⟨770, 767, 0, .none, s0770_plain_contract, 104, s0770_plain_checked⟩

def s0771_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s0771_zero_checked : check 363 s0771_zero_contract = true := by decide +kernel
def s0771_zero : CertifiedContract :=
  ⟨771, 774, 0, .none, s0771_zero_contract, 363, s0771_zero_checked⟩

def s0771_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s0771_positive_checked : check 360 s0771_positive_contract = true := by decide +kernel
def s0771_positive : CertifiedContract :=
  ⟨771, 772, 1, (.dec 8), s0771_positive_contract, 360, s0771_positive_checked⟩

def s0772_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s0772_plain_checked : check 391 s0772_plain_contract = true := by decide +kernel
def s0772_plain : CertifiedContract :=
  ⟨772, 773, 0, (.inc 7), s0772_plain_contract, 391, s0772_plain_checked⟩

def s0773_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s0773_plain_checked : check 98 s0773_plain_contract = true := by decide +kernel
def s0773_plain : CertifiedContract :=
  ⟨773, 771, 0, .none, s0773_plain_contract, 98, s0773_plain_checked⟩

def s0774_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s0774_zero_checked : check 357 s0774_zero_contract = true := by decide +kernel
def s0774_zero : CertifiedContract :=
  ⟨774, 782, 0, .none, s0774_zero_contract, 357, s0774_zero_checked⟩

def s0774_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s0774_positive_checked : check 363 s0774_positive_contract = true := by decide +kernel
def s0774_positive : CertifiedContract :=
  ⟨774, 775, 1, (.dec 0), s0774_positive_contract, 363, s0774_positive_checked⟩

def s0775_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0775_plain_checked : check 373 s0775_plain_contract = true := by decide +kernel
def s0775_plain : CertifiedContract :=
  ⟨775, 776, 0, (.inc 5), s0775_plain_contract, 373, s0775_plain_checked⟩

def s0776_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0776_zero_checked : check 399 s0776_zero_contract = true := by decide +kernel
def s0776_zero : CertifiedContract :=
  ⟨776, 778, 0, .none, s0776_zero_contract, 399, s0776_zero_checked⟩

def s0776_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0776_positive_checked : check 405 s0776_positive_contract = true := by decide +kernel
def s0776_positive : CertifiedContract :=
  ⟨776, 777, 1, (.dec 8), s0776_positive_contract, 405, s0776_positive_checked⟩

def s0777_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s0777_plain_checked : check 110 s0777_plain_contract = true := by decide +kernel
def s0777_plain : CertifiedContract :=
  ⟨777, 781, 0, .none, s0777_plain_contract, 110, s0777_plain_checked⟩

def s0778_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s0778_zero_checked : check 411 s0778_zero_contract = true := by decide +kernel
def s0778_zero : CertifiedContract :=
  ⟨778, 781, 0, .none, s0778_zero_contract, 411, s0778_zero_checked⟩

def s0778_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0778_positive_checked : check 414 s0778_positive_contract = true := by decide +kernel
def s0778_positive : CertifiedContract :=
  ⟨778, 779, 1, (.dec 5), s0778_positive_contract, 414, s0778_positive_checked⟩

def s0779_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0779_plain_checked : check 418 s0779_plain_contract = true := by decide +kernel
def s0779_plain : CertifiedContract :=
  ⟨779, 780, 0, (.inc 8), s0779_plain_contract, 418, s0779_plain_checked⟩

def s0780_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0780_plain_checked : check 113 s0780_plain_contract = true := by decide +kernel
def s0780_plain : CertifiedContract :=
  ⟨780, 778, 0, .none, s0780_plain_contract, 113, s0780_plain_checked⟩

def s0781_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s0781_plain_checked : check 104 s0781_plain_contract = true := by decide +kernel
def s0781_plain : CertifiedContract :=
  ⟨781, 774, 0, .none, s0781_plain_contract, 104, s0781_plain_checked⟩

def s0782_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0782_zero_checked : check 357 s0782_zero_contract = true := by decide +kernel
def s0782_zero : CertifiedContract :=
  ⟨782, 785, 0, .none, s0782_zero_contract, 357, s0782_zero_checked⟩

def s0782_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0782_positive_checked : check 360 s0782_positive_contract = true := by decide +kernel
def s0782_positive : CertifiedContract :=
  ⟨782, 783, 1, (.dec 5), s0782_positive_contract, 360, s0782_positive_checked⟩

def s0783_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s0783_plain_checked : check 373 s0783_plain_contract = true := by decide +kernel
def s0783_plain : CertifiedContract :=
  ⟨783, 784, 0, (.inc 0), s0783_plain_contract, 373, s0783_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S015
