import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S014
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s0686_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s0686_plain_checked : check 101 s0686_plain_contract = true := by decide +kernel
def s0686_plain : CertifiedContract :=
  ⟨686, 684, 0, .none, s0686_plain_contract, 101, s0686_plain_checked⟩

def s0687_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s0687_zero_checked : check 336 s0687_zero_contract = true := by decide +kernel
def s0687_zero : CertifiedContract :=
  ⟨687, 691, 0, .none, s0687_zero_contract, 336, s0687_zero_checked⟩

def s0687_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s0687_positive_checked : check 342 s0687_positive_contract = true := by decide +kernel
def s0687_positive : CertifiedContract :=
  ⟨687, 688, 1, (.dec 7), s0687_positive_contract, 342, s0687_positive_checked⟩

def s0688_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0688_plain_checked : check 346 s0688_plain_contract = true := by decide +kernel
def s0688_plain : CertifiedContract :=
  ⟨688, 689, 0, (.inc 2), s0688_plain_contract, 346, s0688_plain_checked⟩

def s0689_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0689_plain_checked : check 373 s0689_plain_contract = true := by decide +kernel
def s0689_plain : CertifiedContract :=
  ⟨689, 690, 0, (.inc 8), s0689_plain_contract, 373, s0689_plain_checked⟩

def s0690_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s0690_plain_checked : check 98 s0690_plain_contract = true := by decide +kernel
def s0690_plain : CertifiedContract :=
  ⟨690, 687, 0, .none, s0690_plain_contract, 98, s0690_plain_checked⟩

def s0691_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s0691_zero_checked : check 345 s0691_zero_contract = true := by decide +kernel
def s0691_zero : CertifiedContract :=
  ⟨691, 694, 0, .none, s0691_zero_contract, 345, s0691_zero_checked⟩

def s0691_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s0691_positive_checked : check 342 s0691_positive_contract = true := by decide +kernel
def s0691_positive : CertifiedContract :=
  ⟨691, 692, 1, (.dec 8), s0691_positive_contract, 342, s0691_positive_checked⟩

def s0692_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s0692_plain_checked : check 373 s0692_plain_contract = true := by decide +kernel
def s0692_plain : CertifiedContract :=
  ⟨692, 693, 0, (.inc 7), s0692_plain_contract, 373, s0692_plain_checked⟩

def s0693_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s0693_plain_checked : check 92 s0693_plain_contract = true := by decide +kernel
def s0693_plain : CertifiedContract :=
  ⟨693, 691, 0, .none, s0693_plain_contract, 92, s0693_plain_checked⟩

def s0694_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s0694_zero_checked : check 348 s0694_zero_contract = true := by decide +kernel
def s0694_zero : CertifiedContract :=
  ⟨694, 702, 0, .none, s0694_zero_contract, 348, s0694_zero_checked⟩

def s0694_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s0694_positive_checked : check 354 s0694_positive_contract = true := by decide +kernel
def s0694_positive : CertifiedContract :=
  ⟨694, 695, 1, (.dec 0), s0694_positive_contract, 354, s0694_positive_checked⟩

def s0695_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0695_plain_checked : check 364 s0695_plain_contract = true := by decide +kernel
def s0695_plain : CertifiedContract :=
  ⟨695, 696, 0, (.inc 5), s0695_plain_contract, 364, s0695_plain_checked⟩

def s0696_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0696_zero_checked : check 390 s0696_zero_contract = true := by decide +kernel
def s0696_zero : CertifiedContract :=
  ⟨696, 698, 0, .none, s0696_zero_contract, 390, s0696_zero_checked⟩

def s0696_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0696_positive_checked : check 396 s0696_positive_contract = true := by decide +kernel
def s0696_positive : CertifiedContract :=
  ⟨696, 697, 1, (.dec 8), s0696_positive_contract, 396, s0696_positive_checked⟩

def s0697_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s0697_plain_checked : check 107 s0697_plain_contract = true := by decide +kernel
def s0697_plain : CertifiedContract :=
  ⟨697, 701, 0, .none, s0697_plain_contract, 107, s0697_plain_checked⟩

def s0698_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s0698_zero_checked : check 402 s0698_zero_contract = true := by decide +kernel
def s0698_zero : CertifiedContract :=
  ⟨698, 701, 0, .none, s0698_zero_contract, 402, s0698_zero_checked⟩

def s0698_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0698_positive_checked : check 405 s0698_positive_contract = true := by decide +kernel
def s0698_positive : CertifiedContract :=
  ⟨698, 699, 1, (.dec 5), s0698_positive_contract, 405, s0698_positive_checked⟩

def s0699_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0699_plain_checked : check 409 s0699_plain_contract = true := by decide +kernel
def s0699_plain : CertifiedContract :=
  ⟨699, 700, 0, (.inc 8), s0699_plain_contract, 409, s0699_plain_checked⟩

def s0700_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0700_plain_checked : check 110 s0700_plain_contract = true := by decide +kernel
def s0700_plain : CertifiedContract :=
  ⟨700, 698, 0, .none, s0700_plain_contract, 110, s0700_plain_checked⟩

def s0701_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s0701_plain_checked : check 101 s0701_plain_contract = true := by decide +kernel
def s0701_plain : CertifiedContract :=
  ⟨701, 694, 0, .none, s0701_plain_contract, 101, s0701_plain_checked⟩

def s0702_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0702_zero_checked : check 348 s0702_zero_contract = true := by decide +kernel
def s0702_zero : CertifiedContract :=
  ⟨702, 705, 0, .none, s0702_zero_contract, 348, s0702_zero_checked⟩

def s0702_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0702_positive_checked : check 351 s0702_positive_contract = true := by decide +kernel
def s0702_positive : CertifiedContract :=
  ⟨702, 703, 1, (.dec 5), s0702_positive_contract, 351, s0702_positive_checked⟩

def s0703_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s0703_plain_checked : check 364 s0703_plain_contract = true := by decide +kernel
def s0703_plain : CertifiedContract :=
  ⟨703, 704, 0, (.inc 0), s0703_plain_contract, 364, s0703_plain_checked⟩

def s0704_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s0704_plain_checked : check 95 s0704_plain_contract = true := by decide +kernel
def s0704_plain : CertifiedContract :=
  ⟨704, 702, 0, .none, s0704_plain_contract, 95, s0704_plain_checked⟩

def s0705_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s0705_zero_checked : check 345 s0705_zero_contract = true := by decide +kernel
def s0705_zero : CertifiedContract :=
  ⟨705, 709, 0, .none, s0705_zero_contract, 345, s0705_zero_checked⟩

def s0705_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0705_positive_checked : check 351 s0705_positive_contract = true := by decide +kernel
def s0705_positive : CertifiedContract :=
  ⟨705, 706, 1, (.dec 2), s0705_positive_contract, 351, s0705_positive_checked⟩

def s0706_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0706_plain_checked : check 364 s0706_plain_contract = true := by decide +kernel
def s0706_plain : CertifiedContract :=
  ⟨706, 707, 0, (.inc 5), s0706_plain_contract, 364, s0706_plain_checked⟩

def s0707_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0707_plain_checked : check 391 s0707_plain_contract = true := by decide +kernel
def s0707_plain : CertifiedContract :=
  ⟨707, 708, 0, (.inc 8), s0707_plain_contract, 391, s0707_plain_checked⟩

def s0708_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0708_plain_checked : check 104 s0708_plain_contract = true := by decide +kernel
def s0708_plain : CertifiedContract :=
  ⟨708, 705, 0, .none, s0708_plain_contract, 104, s0708_plain_checked⟩

def s0709_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s0709_zero_checked : check 366 s0709_zero_contract = true := by decide +kernel
def s0709_zero : CertifiedContract :=
  ⟨709, 715, 0, .none, s0709_zero_contract, 366, s0709_zero_checked⟩

def s0709_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0709_positive_checked : check 369 s0709_positive_contract = true := by decide +kernel
def s0709_positive : CertifiedContract :=
  ⟨709, 710, 1, (.dec 8), s0709_positive_contract, 369, s0709_positive_checked⟩

def s0710_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0710_plain_checked : check 364 s0710_plain_contract = true := by decide +kernel
def s0710_plain : CertifiedContract :=
  ⟨710, 711, 0, (.inc 5), s0710_plain_contract, 364, s0710_plain_checked⟩

def s0711_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s0711_zero_checked : check 384 s0711_zero_contract = true := by decide +kernel
def s0711_zero : CertifiedContract :=
  ⟨711, 714, 0, .none, s0711_zero_contract, 384, s0711_zero_checked⟩

def s0711_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0711_positive_checked : check 387 s0711_positive_contract = true := by decide +kernel
def s0711_positive : CertifiedContract :=
  ⟨711, 712, 1, (.dec 8), s0711_positive_contract, 387, s0711_positive_checked⟩

def s0712_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0712_plain_checked : check 382 s0712_plain_contract = true := by decide +kernel
def s0712_plain : CertifiedContract :=
  ⟨712, 713, 0, (.inc 2), s0712_plain_contract, 382, s0712_plain_checked⟩

def s0713_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0713_plain_checked : check 104 s0713_plain_contract = true := by decide +kernel
def s0713_plain : CertifiedContract :=
  ⟨713, 711, 0, .none, s0713_plain_contract, 104, s0713_plain_checked⟩

def s0714_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0714_plain_checked : check 107 s0714_plain_contract = true := by decide +kernel
def s0714_plain : CertifiedContract :=
  ⟨714, 705, 0, .none, s0714_plain_contract, 107, s0714_plain_checked⟩

def s0715_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, true] 0 .none⟩
theorem s0715_zero_checked : check 351 s0715_zero_contract = true := by decide +kernel
def s0715_zero : CertifiedContract :=
  ⟨715, 721, 0, .none, s0715_zero_contract, 351, s0715_zero_checked⟩

def s0715_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0715_positive_checked : check 351 s0715_positive_contract = true := by decide +kernel
def s0715_positive : CertifiedContract :=
  ⟨715, 716, 1, (.dec 5), s0715_positive_contract, 351, s0715_positive_checked⟩

def s0716_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0716_plain_checked : check 364 s0716_plain_contract = true := by decide +kernel
def s0716_plain : CertifiedContract :=
  ⟨716, 717, 0, (.inc 2), s0716_plain_contract, 364, s0716_plain_checked⟩

def s0717_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0717_plain_checked : check 367 s0717_plain_contract = true := by decide +kernel
def s0717_plain : CertifiedContract :=
  ⟨717, 718, 0, (.inc 2), s0717_plain_contract, 367, s0717_plain_checked⟩

def s0718_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0718_plain_checked : check 373 s0718_plain_contract = true := by decide +kernel
def s0718_plain : CertifiedContract :=
  ⟨718, 719, 0, (.inc 2), s0718_plain_contract, 373, s0718_plain_checked⟩

def s0719_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s0719_plain_checked : check 379 s0719_plain_contract = true := by decide +kernel
def s0719_plain : CertifiedContract :=
  ⟨719, 720, 0, (.inc 2), s0719_plain_contract, 379, s0719_plain_checked⟩

def s0720_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s0720_plain_checked : check 92 s0720_plain_contract = true := by decide +kernel
def s0720_plain : CertifiedContract :=
  ⟨720, 715, 0, .none, s0720_plain_contract, 92, s0720_plain_checked⟩

def s0721_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, false, false] 0 (.inc 2)⟩
theorem s0721_plain_checked : check 325 s0721_plain_contract = true := by decide +kernel
def s0721_plain : CertifiedContract :=
  ⟨721, 722, 0, (.inc 2), s0721_plain_contract, 325, s0721_plain_checked⟩

def s0722_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0722_zero_checked : check 354 s0722_zero_contract = true := by decide +kernel
def s0722_zero : CertifiedContract :=
  ⟨722, 725, 0, .none, s0722_zero_contract, 354, s0722_zero_checked⟩

def s0722_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s0722_positive_checked : check 360 s0722_positive_contract = true := by decide +kernel
def s0722_positive : CertifiedContract :=
  ⟨722, 723, 1, (.dec 2), s0722_positive_contract, 360, s0722_positive_checked⟩

def s0723_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s0723_plain_checked : check 373 s0723_plain_contract = true := by decide +kernel
def s0723_plain : CertifiedContract :=
  ⟨723, 724, 0, (.inc 8), s0723_plain_contract, 373, s0723_plain_checked⟩

def s0724_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s0724_plain_checked : check 98 s0724_plain_contract = true := by decide +kernel
def s0724_plain : CertifiedContract :=
  ⟨724, 722, 0, .none, s0724_plain_contract, 98, s0724_plain_checked⟩

def s0725_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0725_zero_checked : check 375 s0725_zero_contract = true := by decide +kernel
def s0725_zero : CertifiedContract :=
  ⟨725, 728, 0, .none, s0725_zero_contract, 375, s0725_zero_checked⟩

def s0725_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0725_positive_checked : check 381 s0725_positive_contract = true := by decide +kernel
def s0725_positive : CertifiedContract :=
  ⟨725, 726, 1, (.dec 0), s0725_positive_contract, 381, s0725_positive_checked⟩

def s0726_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0726_plain_checked : check 373 s0726_plain_contract = true := by decide +kernel
def s0726_plain : CertifiedContract :=
  ⟨726, 727, 0, (.inc 2), s0726_plain_contract, 373, s0726_plain_checked⟩

def s0727_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0727_plain_checked : check 101 s0727_plain_contract = true := by decide +kernel
def s0727_plain : CertifiedContract :=
  ⟨727, 725, 0, .none, s0727_plain_contract, 101, s0727_plain_checked⟩

def s0728_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0728_zero_checked : check 381 s0728_zero_contract = true := by decide +kernel
def s0728_zero : CertifiedContract :=
  ⟨728, 732, 0, .none, s0728_zero_contract, 381, s0728_zero_checked⟩

def s0728_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0728_positive_checked : check 387 s0728_positive_contract = true := by decide +kernel
def s0728_positive : CertifiedContract :=
  ⟨728, 729, 1, (.dec 2), s0728_positive_contract, 387, s0728_positive_checked⟩

def s0729_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0729_plain_checked : check 400 s0729_plain_contract = true := by decide +kernel
def s0729_plain : CertifiedContract :=
  ⟨729, 730, 0, (.inc 5), s0729_plain_contract, 400, s0729_plain_checked⟩

def s0730_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0730_plain_checked : check 427 s0730_plain_contract = true := by decide +kernel
def s0730_plain : CertifiedContract :=
  ⟨730, 731, 0, (.inc 8), s0730_plain_contract, 427, s0730_plain_checked⟩

def s0731_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0731_plain_checked : check 116 s0731_plain_contract = true := by decide +kernel
def s0731_plain : CertifiedContract :=
  ⟨731, 728, 0, .none, s0731_plain_contract, 116, s0731_plain_checked⟩

def s0732_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s0732_zero_checked : check 402 s0732_zero_contract = true := by decide +kernel
def s0732_zero : CertifiedContract :=
  ⟨732, 738, 0, .none, s0732_zero_contract, 402, s0732_zero_checked⟩

def s0732_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0732_positive_checked : check 405 s0732_positive_contract = true := by decide +kernel
def s0732_positive : CertifiedContract :=
  ⟨732, 733, 1, (.dec 8), s0732_positive_contract, 405, s0732_positive_checked⟩

def s0733_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0733_plain_checked : check 400 s0733_plain_contract = true := by decide +kernel
def s0733_plain : CertifiedContract :=
  ⟨733, 734, 0, (.inc 5), s0733_plain_contract, 400, s0733_plain_checked⟩

def s0734_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s0734_zero_checked : check 420 s0734_zero_contract = true := by decide +kernel
def s0734_zero : CertifiedContract :=
  ⟨734, 737, 0, .none, s0734_zero_contract, 420, s0734_zero_checked⟩

def s0734_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0734_positive_checked : check 423 s0734_positive_contract = true := by decide +kernel
def s0734_positive : CertifiedContract :=
  ⟨734, 735, 1, (.dec 8), s0734_positive_contract, 423, s0734_positive_checked⟩

end PA211.UserCandidate.RuntimeShards.S014
