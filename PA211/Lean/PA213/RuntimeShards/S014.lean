import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S014
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s0686_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s0686_plain_checked : check 100 s0686_plain_contract = true := by decide +kernel
def s0686_plain : CertifiedContract :=
  ⟨686, 684, 0, .none, s0686_plain_contract, 100, s0686_plain_checked⟩

def s0687_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s0687_zero_checked : check 335 s0687_zero_contract = true := by decide +kernel
def s0687_zero : CertifiedContract :=
  ⟨687, 691, 0, .none, s0687_zero_contract, 335, s0687_zero_checked⟩

def s0687_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s0687_positive_checked : check 341 s0687_positive_contract = true := by decide +kernel
def s0687_positive : CertifiedContract :=
  ⟨687, 688, 1, (.dec 7), s0687_positive_contract, 341, s0687_positive_checked⟩

def s0688_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0688_plain_checked : check 345 s0688_plain_contract = true := by decide +kernel
def s0688_plain : CertifiedContract :=
  ⟨688, 689, 0, (.inc 2), s0688_plain_contract, 345, s0688_plain_checked⟩

def s0689_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0689_plain_checked : check 372 s0689_plain_contract = true := by decide +kernel
def s0689_plain : CertifiedContract :=
  ⟨689, 690, 0, (.inc 8), s0689_plain_contract, 372, s0689_plain_checked⟩

def s0690_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s0690_plain_checked : check 97 s0690_plain_contract = true := by decide +kernel
def s0690_plain : CertifiedContract :=
  ⟨690, 687, 0, .none, s0690_plain_contract, 97, s0690_plain_checked⟩

def s0691_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s0691_zero_checked : check 344 s0691_zero_contract = true := by decide +kernel
def s0691_zero : CertifiedContract :=
  ⟨691, 694, 0, .none, s0691_zero_contract, 344, s0691_zero_checked⟩

def s0691_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s0691_positive_checked : check 341 s0691_positive_contract = true := by decide +kernel
def s0691_positive : CertifiedContract :=
  ⟨691, 692, 1, (.dec 8), s0691_positive_contract, 341, s0691_positive_checked⟩

def s0692_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s0692_plain_checked : check 372 s0692_plain_contract = true := by decide +kernel
def s0692_plain : CertifiedContract :=
  ⟨692, 693, 0, (.inc 7), s0692_plain_contract, 372, s0692_plain_checked⟩

def s0693_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s0693_plain_checked : check 91 s0693_plain_contract = true := by decide +kernel
def s0693_plain : CertifiedContract :=
  ⟨693, 691, 0, .none, s0693_plain_contract, 91, s0693_plain_checked⟩

def s0694_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s0694_zero_checked : check 347 s0694_zero_contract = true := by decide +kernel
def s0694_zero : CertifiedContract :=
  ⟨694, 702, 0, .none, s0694_zero_contract, 347, s0694_zero_checked⟩

def s0694_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s0694_positive_checked : check 353 s0694_positive_contract = true := by decide +kernel
def s0694_positive : CertifiedContract :=
  ⟨694, 695, 1, (.dec 0), s0694_positive_contract, 353, s0694_positive_checked⟩

def s0695_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0695_plain_checked : check 363 s0695_plain_contract = true := by decide +kernel
def s0695_plain : CertifiedContract :=
  ⟨695, 696, 0, (.inc 5), s0695_plain_contract, 363, s0695_plain_checked⟩

def s0696_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0696_zero_checked : check 389 s0696_zero_contract = true := by decide +kernel
def s0696_zero : CertifiedContract :=
  ⟨696, 698, 0, .none, s0696_zero_contract, 389, s0696_zero_checked⟩

def s0696_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0696_positive_checked : check 395 s0696_positive_contract = true := by decide +kernel
def s0696_positive : CertifiedContract :=
  ⟨696, 697, 1, (.dec 8), s0696_positive_contract, 395, s0696_positive_checked⟩

def s0697_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s0697_plain_checked : check 106 s0697_plain_contract = true := by decide +kernel
def s0697_plain : CertifiedContract :=
  ⟨697, 701, 0, .none, s0697_plain_contract, 106, s0697_plain_checked⟩

def s0698_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s0698_zero_checked : check 401 s0698_zero_contract = true := by decide +kernel
def s0698_zero : CertifiedContract :=
  ⟨698, 701, 0, .none, s0698_zero_contract, 401, s0698_zero_checked⟩

def s0698_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0698_positive_checked : check 404 s0698_positive_contract = true := by decide +kernel
def s0698_positive : CertifiedContract :=
  ⟨698, 699, 1, (.dec 5), s0698_positive_contract, 404, s0698_positive_checked⟩

def s0699_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0699_plain_checked : check 408 s0699_plain_contract = true := by decide +kernel
def s0699_plain : CertifiedContract :=
  ⟨699, 700, 0, (.inc 8), s0699_plain_contract, 408, s0699_plain_checked⟩

def s0700_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0700_plain_checked : check 109 s0700_plain_contract = true := by decide +kernel
def s0700_plain : CertifiedContract :=
  ⟨700, 698, 0, .none, s0700_plain_contract, 109, s0700_plain_checked⟩

def s0701_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s0701_plain_checked : check 100 s0701_plain_contract = true := by decide +kernel
def s0701_plain : CertifiedContract :=
  ⟨701, 694, 0, .none, s0701_plain_contract, 100, s0701_plain_checked⟩

def s0702_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0702_zero_checked : check 347 s0702_zero_contract = true := by decide +kernel
def s0702_zero : CertifiedContract :=
  ⟨702, 705, 0, .none, s0702_zero_contract, 347, s0702_zero_checked⟩

def s0702_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0702_positive_checked : check 350 s0702_positive_contract = true := by decide +kernel
def s0702_positive : CertifiedContract :=
  ⟨702, 703, 1, (.dec 5), s0702_positive_contract, 350, s0702_positive_checked⟩

def s0703_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s0703_plain_checked : check 363 s0703_plain_contract = true := by decide +kernel
def s0703_plain : CertifiedContract :=
  ⟨703, 704, 0, (.inc 0), s0703_plain_contract, 363, s0703_plain_checked⟩

def s0704_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s0704_plain_checked : check 94 s0704_plain_contract = true := by decide +kernel
def s0704_plain : CertifiedContract :=
  ⟨704, 702, 0, .none, s0704_plain_contract, 94, s0704_plain_checked⟩

def s0705_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s0705_zero_checked : check 344 s0705_zero_contract = true := by decide +kernel
def s0705_zero : CertifiedContract :=
  ⟨705, 709, 0, .none, s0705_zero_contract, 344, s0705_zero_checked⟩

def s0705_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0705_positive_checked : check 350 s0705_positive_contract = true := by decide +kernel
def s0705_positive : CertifiedContract :=
  ⟨705, 706, 1, (.dec 2), s0705_positive_contract, 350, s0705_positive_checked⟩

def s0706_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0706_plain_checked : check 363 s0706_plain_contract = true := by decide +kernel
def s0706_plain : CertifiedContract :=
  ⟨706, 707, 0, (.inc 5), s0706_plain_contract, 363, s0706_plain_checked⟩

def s0707_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0707_plain_checked : check 390 s0707_plain_contract = true := by decide +kernel
def s0707_plain : CertifiedContract :=
  ⟨707, 708, 0, (.inc 8), s0707_plain_contract, 390, s0707_plain_checked⟩

def s0708_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0708_plain_checked : check 103 s0708_plain_contract = true := by decide +kernel
def s0708_plain : CertifiedContract :=
  ⟨708, 705, 0, .none, s0708_plain_contract, 103, s0708_plain_checked⟩

def s0709_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s0709_zero_checked : check 365 s0709_zero_contract = true := by decide +kernel
def s0709_zero : CertifiedContract :=
  ⟨709, 715, 0, .none, s0709_zero_contract, 365, s0709_zero_checked⟩

def s0709_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0709_positive_checked : check 368 s0709_positive_contract = true := by decide +kernel
def s0709_positive : CertifiedContract :=
  ⟨709, 710, 1, (.dec 8), s0709_positive_contract, 368, s0709_positive_checked⟩

def s0710_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0710_plain_checked : check 363 s0710_plain_contract = true := by decide +kernel
def s0710_plain : CertifiedContract :=
  ⟨710, 711, 0, (.inc 5), s0710_plain_contract, 363, s0710_plain_checked⟩

def s0711_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s0711_zero_checked : check 383 s0711_zero_contract = true := by decide +kernel
def s0711_zero : CertifiedContract :=
  ⟨711, 714, 0, .none, s0711_zero_contract, 383, s0711_zero_checked⟩

def s0711_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0711_positive_checked : check 386 s0711_positive_contract = true := by decide +kernel
def s0711_positive : CertifiedContract :=
  ⟨711, 712, 1, (.dec 8), s0711_positive_contract, 386, s0711_positive_checked⟩

def s0712_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0712_plain_checked : check 381 s0712_plain_contract = true := by decide +kernel
def s0712_plain : CertifiedContract :=
  ⟨712, 713, 0, (.inc 2), s0712_plain_contract, 381, s0712_plain_checked⟩

def s0713_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0713_plain_checked : check 103 s0713_plain_contract = true := by decide +kernel
def s0713_plain : CertifiedContract :=
  ⟨713, 711, 0, .none, s0713_plain_contract, 103, s0713_plain_checked⟩

def s0714_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0714_plain_checked : check 106 s0714_plain_contract = true := by decide +kernel
def s0714_plain : CertifiedContract :=
  ⟨714, 705, 0, .none, s0714_plain_contract, 106, s0714_plain_checked⟩

def s0715_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, true] 0 .none⟩
theorem s0715_zero_checked : check 350 s0715_zero_contract = true := by decide +kernel
def s0715_zero : CertifiedContract :=
  ⟨715, 721, 0, .none, s0715_zero_contract, 350, s0715_zero_checked⟩

def s0715_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0715_positive_checked : check 350 s0715_positive_contract = true := by decide +kernel
def s0715_positive : CertifiedContract :=
  ⟨715, 716, 1, (.dec 5), s0715_positive_contract, 350, s0715_positive_checked⟩

def s0716_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0716_plain_checked : check 363 s0716_plain_contract = true := by decide +kernel
def s0716_plain : CertifiedContract :=
  ⟨716, 717, 0, (.inc 2), s0716_plain_contract, 363, s0716_plain_checked⟩

def s0717_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0717_plain_checked : check 366 s0717_plain_contract = true := by decide +kernel
def s0717_plain : CertifiedContract :=
  ⟨717, 718, 0, (.inc 2), s0717_plain_contract, 366, s0717_plain_checked⟩

def s0718_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0718_plain_checked : check 363 s0718_plain_contract = true := by decide +kernel
def s0718_plain : CertifiedContract :=
  ⟨718, 719, 0, (.inc 2), s0718_plain_contract, 363, s0718_plain_checked⟩

def s0719_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s0719_plain_checked : check 369 s0719_plain_contract = true := by decide +kernel
def s0719_plain : CertifiedContract :=
  ⟨719, 720, 0, (.inc 2), s0719_plain_contract, 369, s0719_plain_checked⟩

def s0720_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s0720_plain_checked : check 91 s0720_plain_contract = true := by decide +kernel
def s0720_plain : CertifiedContract :=
  ⟨720, 715, 0, .none, s0720_plain_contract, 91, s0720_plain_checked⟩

def s0721_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, false, false] 0 (.inc 2)⟩
theorem s0721_plain_checked : check 324 s0721_plain_contract = true := by decide +kernel
def s0721_plain : CertifiedContract :=
  ⟨721, 722, 0, (.inc 2), s0721_plain_contract, 324, s0721_plain_checked⟩

def s0722_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0722_zero_checked : check 353 s0722_zero_contract = true := by decide +kernel
def s0722_zero : CertifiedContract :=
  ⟨722, 725, 0, .none, s0722_zero_contract, 353, s0722_zero_checked⟩

def s0722_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s0722_positive_checked : check 359 s0722_positive_contract = true := by decide +kernel
def s0722_positive : CertifiedContract :=
  ⟨722, 723, 1, (.dec 2), s0722_positive_contract, 359, s0722_positive_checked⟩

def s0723_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s0723_plain_checked : check 372 s0723_plain_contract = true := by decide +kernel
def s0723_plain : CertifiedContract :=
  ⟨723, 724, 0, (.inc 8), s0723_plain_contract, 372, s0723_plain_checked⟩

def s0724_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s0724_plain_checked : check 97 s0724_plain_contract = true := by decide +kernel
def s0724_plain : CertifiedContract :=
  ⟨724, 722, 0, .none, s0724_plain_contract, 97, s0724_plain_checked⟩

def s0725_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0725_zero_checked : check 374 s0725_zero_contract = true := by decide +kernel
def s0725_zero : CertifiedContract :=
  ⟨725, 728, 0, .none, s0725_zero_contract, 374, s0725_zero_checked⟩

def s0725_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0725_positive_checked : check 380 s0725_positive_contract = true := by decide +kernel
def s0725_positive : CertifiedContract :=
  ⟨725, 726, 1, (.dec 0), s0725_positive_contract, 380, s0725_positive_checked⟩

def s0726_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0726_plain_checked : check 372 s0726_plain_contract = true := by decide +kernel
def s0726_plain : CertifiedContract :=
  ⟨726, 727, 0, (.inc 2), s0726_plain_contract, 372, s0726_plain_checked⟩

def s0727_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0727_plain_checked : check 100 s0727_plain_contract = true := by decide +kernel
def s0727_plain : CertifiedContract :=
  ⟨727, 725, 0, .none, s0727_plain_contract, 100, s0727_plain_checked⟩

def s0728_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0728_zero_checked : check 380 s0728_zero_contract = true := by decide +kernel
def s0728_zero : CertifiedContract :=
  ⟨728, 732, 0, .none, s0728_zero_contract, 380, s0728_zero_checked⟩

def s0728_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0728_positive_checked : check 386 s0728_positive_contract = true := by decide +kernel
def s0728_positive : CertifiedContract :=
  ⟨728, 729, 1, (.dec 2), s0728_positive_contract, 386, s0728_positive_checked⟩

def s0729_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0729_plain_checked : check 399 s0729_plain_contract = true := by decide +kernel
def s0729_plain : CertifiedContract :=
  ⟨729, 730, 0, (.inc 5), s0729_plain_contract, 399, s0729_plain_checked⟩

def s0730_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0730_plain_checked : check 426 s0730_plain_contract = true := by decide +kernel
def s0730_plain : CertifiedContract :=
  ⟨730, 731, 0, (.inc 8), s0730_plain_contract, 426, s0730_plain_checked⟩

def s0731_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0731_plain_checked : check 115 s0731_plain_contract = true := by decide +kernel
def s0731_plain : CertifiedContract :=
  ⟨731, 728, 0, .none, s0731_plain_contract, 115, s0731_plain_checked⟩

def s0732_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s0732_zero_checked : check 401 s0732_zero_contract = true := by decide +kernel
def s0732_zero : CertifiedContract :=
  ⟨732, 738, 0, .none, s0732_zero_contract, 401, s0732_zero_checked⟩

def s0732_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0732_positive_checked : check 404 s0732_positive_contract = true := by decide +kernel
def s0732_positive : CertifiedContract :=
  ⟨732, 733, 1, (.dec 8), s0732_positive_contract, 404, s0732_positive_checked⟩

def s0733_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0733_plain_checked : check 399 s0733_plain_contract = true := by decide +kernel
def s0733_plain : CertifiedContract :=
  ⟨733, 734, 0, (.inc 5), s0733_plain_contract, 399, s0733_plain_checked⟩

def s0734_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s0734_zero_checked : check 419 s0734_zero_contract = true := by decide +kernel
def s0734_zero : CertifiedContract :=
  ⟨734, 737, 0, .none, s0734_zero_contract, 419, s0734_zero_checked⟩

def s0734_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0734_positive_checked : check 422 s0734_positive_contract = true := by decide +kernel
def s0734_positive : CertifiedContract :=
  ⟨734, 735, 1, (.dec 8), s0734_positive_contract, 422, s0734_positive_checked⟩

def nonterminal : Array CertifiedContract := #[
  s0686_plain,
  s0687_zero,
  s0687_positive,
  s0688_plain,
  s0689_plain,
  s0690_plain,
  s0691_zero,
  s0691_positive,
  s0692_plain,
  s0693_plain,
  s0694_zero,
  s0694_positive,
  s0695_plain,
  s0696_zero,
  s0696_positive,
  s0697_plain,
  s0698_zero,
  s0698_positive,
  s0699_plain,
  s0700_plain,
  s0701_plain,
  s0702_zero,
  s0702_positive,
  s0703_plain,
  s0704_plain,
  s0705_zero,
  s0705_positive,
  s0706_plain,
  s0707_plain,
  s0708_plain,
  s0709_zero,
  s0709_positive,
  s0710_plain,
  s0711_zero,
  s0711_positive,
  s0712_plain,
  s0713_plain,
  s0714_plain,
  s0715_zero,
  s0715_positive,
  s0716_plain,
  s0717_plain,
  s0718_plain,
  s0719_plain,
  s0720_plain,
  s0721_plain,
  s0722_zero,
  s0722_positive,
  s0723_plain,
  s0724_plain,
  s0725_zero,
  s0725_positive,
  s0726_plain,
  s0727_plain,
  s0728_zero,
  s0728_positive,
  s0729_plain,
  s0730_plain,
  s0731_plain,
  s0732_zero,
  s0732_positive,
  s0733_plain,
  s0734_zero,
  s0734_positive
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S014
