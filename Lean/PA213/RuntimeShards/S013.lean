module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S013
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s0636_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0636_plain_checked : check 372 s0636_plain_contract = true := by decide +kernel
def s0636_plain : CertifiedContract :=
  ⟨636, 637, 0, (.inc 2), s0636_plain_contract, 372, s0636_plain_checked⟩

def s0637_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s0637_plain_checked : check 378 s0637_plain_contract = true := by decide +kernel
def s0637_plain : CertifiedContract :=
  ⟨637, 638, 0, (.inc 2), s0637_plain_contract, 378, s0637_plain_checked⟩

def s0638_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true, false] 0 .none⟩
theorem s0638_plain_checked : check 94 s0638_plain_contract = true := by decide +kernel
def s0638_plain : CertifiedContract :=
  ⟨638, 633, 0, .none, s0638_plain_contract, 94, s0638_plain_checked⟩

def s0639_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, false, false] 0 (.inc 2)⟩
theorem s0639_plain_checked : check 357 s0639_plain_contract = true := by decide +kernel
def s0639_plain : CertifiedContract :=
  ⟨639, 640, 0, (.inc 2), s0639_plain_contract, 357, s0639_plain_checked⟩

def s0640_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, false, true] 0 (.inc 2)⟩
theorem s0640_plain_checked : check 273 s0640_plain_contract = true := by decide +kernel
def s0640_plain : CertifiedContract :=
  ⟨640, 641, 0, (.inc 2), s0640_plain_contract, 273, s0640_plain_checked⟩

def s0641_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, false, false] 0 (.inc 2)⟩
theorem s0641_plain_checked : check 276 s0641_plain_contract = true := by decide +kernel
def s0641_plain : CertifiedContract :=
  ⟨641, 642, 0, (.inc 2), s0641_plain_contract, 276, s0641_plain_checked⟩

def s0642_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0642_zero_checked : check 335 s0642_zero_contract = true := by decide +kernel
def s0642_zero : CertifiedContract :=
  ⟨642, 645, 0, .none, s0642_zero_contract, 335, s0642_zero_checked⟩

def s0642_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s0642_positive_checked : check 341 s0642_positive_contract = true := by decide +kernel
def s0642_positive : CertifiedContract :=
  ⟨642, 643, 1, (.dec 2), s0642_positive_contract, 341, s0642_positive_checked⟩

def s0643_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s0643_plain_checked : check 354 s0643_plain_contract = true := by decide +kernel
def s0643_plain : CertifiedContract :=
  ⟨643, 644, 0, (.inc 8), s0643_plain_contract, 354, s0643_plain_checked⟩

def s0644_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s0644_plain_checked : check 91 s0644_plain_contract = true := by decide +kernel
def s0644_plain : CertifiedContract :=
  ⟨644, 642, 0, .none, s0644_plain_contract, 91, s0644_plain_checked⟩

def s0645_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0645_zero_checked : check 356 s0645_zero_contract = true := by decide +kernel
def s0645_zero : CertifiedContract :=
  ⟨645, 648, 0, .none, s0645_zero_contract, 356, s0645_zero_checked⟩

def s0645_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0645_positive_checked : check 362 s0645_positive_contract = true := by decide +kernel
def s0645_positive : CertifiedContract :=
  ⟨645, 646, 1, (.dec 0), s0645_positive_contract, 362, s0645_positive_checked⟩

def s0646_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0646_plain_checked : check 354 s0646_plain_contract = true := by decide +kernel
def s0646_plain : CertifiedContract :=
  ⟨646, 647, 0, (.inc 2), s0646_plain_contract, 354, s0646_plain_checked⟩

def s0647_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0647_plain_checked : check 94 s0647_plain_contract = true := by decide +kernel
def s0647_plain : CertifiedContract :=
  ⟨647, 645, 0, .none, s0647_plain_contract, 94, s0647_plain_checked⟩

def s0648_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0648_zero_checked : check 362 s0648_zero_contract = true := by decide +kernel
def s0648_zero : CertifiedContract :=
  ⟨648, 652, 0, .none, s0648_zero_contract, 362, s0648_zero_checked⟩

def s0648_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0648_positive_checked : check 368 s0648_positive_contract = true := by decide +kernel
def s0648_positive : CertifiedContract :=
  ⟨648, 649, 1, (.dec 2), s0648_positive_contract, 368, s0648_positive_checked⟩

def s0649_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0649_plain_checked : check 381 s0649_plain_contract = true := by decide +kernel
def s0649_plain : CertifiedContract :=
  ⟨649, 650, 0, (.inc 5), s0649_plain_contract, 381, s0649_plain_checked⟩

def s0650_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0650_plain_checked : check 408 s0650_plain_contract = true := by decide +kernel
def s0650_plain : CertifiedContract :=
  ⟨650, 651, 0, (.inc 8), s0650_plain_contract, 408, s0650_plain_checked⟩

def s0651_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0651_plain_checked : check 109 s0651_plain_contract = true := by decide +kernel
def s0651_plain : CertifiedContract :=
  ⟨651, 648, 0, .none, s0651_plain_contract, 109, s0651_plain_checked⟩

def s0652_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s0652_zero_checked : check 383 s0652_zero_contract = true := by decide +kernel
def s0652_zero : CertifiedContract :=
  ⟨652, 658, 0, .none, s0652_zero_contract, 383, s0652_zero_checked⟩

def s0652_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0652_positive_checked : check 386 s0652_positive_contract = true := by decide +kernel
def s0652_positive : CertifiedContract :=
  ⟨652, 653, 1, (.dec 8), s0652_positive_contract, 386, s0652_positive_checked⟩

def s0653_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0653_plain_checked : check 381 s0653_plain_contract = true := by decide +kernel
def s0653_plain : CertifiedContract :=
  ⟨653, 654, 0, (.inc 5), s0653_plain_contract, 381, s0653_plain_checked⟩

def s0654_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s0654_zero_checked : check 401 s0654_zero_contract = true := by decide +kernel
def s0654_zero : CertifiedContract :=
  ⟨654, 657, 0, .none, s0654_zero_contract, 401, s0654_zero_checked⟩

def s0654_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0654_positive_checked : check 404 s0654_positive_contract = true := by decide +kernel
def s0654_positive : CertifiedContract :=
  ⟨654, 655, 1, (.dec 8), s0654_positive_contract, 404, s0654_positive_checked⟩

def s0655_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0655_plain_checked : check 399 s0655_plain_contract = true := by decide +kernel
def s0655_plain : CertifiedContract :=
  ⟨655, 656, 0, (.inc 2), s0655_plain_contract, 399, s0655_plain_checked⟩

def s0656_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0656_plain_checked : check 109 s0656_plain_contract = true := by decide +kernel
def s0656_plain : CertifiedContract :=
  ⟨656, 654, 0, .none, s0656_plain_contract, 109, s0656_plain_checked⟩

def s0657_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0657_plain_checked : check 112 s0657_plain_contract = true := by decide +kernel
def s0657_plain : CertifiedContract :=
  ⟨657, 648, 0, .none, s0657_plain_contract, 112, s0657_plain_checked⟩

def s0658_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s0658_zero_checked : check 371 s0658_zero_contract = true := by decide +kernel
def s0658_zero : CertifiedContract :=
  ⟨658, 661, 0, .none, s0658_zero_contract, 371, s0658_zero_checked⟩

def s0658_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0658_positive_checked : check 368 s0658_positive_contract = true := by decide +kernel
def s0658_positive : CertifiedContract :=
  ⟨658, 659, 1, (.dec 5), s0658_positive_contract, 368, s0658_positive_checked⟩

def s0659_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0659_plain_checked : check 381 s0659_plain_contract = true := by decide +kernel
def s0659_plain : CertifiedContract :=
  ⟨659, 660, 0, (.inc 0), s0659_plain_contract, 381, s0659_plain_checked⟩

def s0660_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s0660_plain_checked : check 100 s0660_plain_contract = true := by decide +kernel
def s0660_plain : CertifiedContract :=
  ⟨660, 658, 0, .none, s0660_plain_contract, 100, s0660_plain_checked⟩

def s0661_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s0661_zero_checked : check 335 s0661_zero_contract = true := by decide +kernel
def s0661_zero : CertifiedContract :=
  ⟨661, 665, 0, .none, s0661_zero_contract, 335, s0661_zero_checked⟩

def s0661_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, true, false, true, false] 1 (.dec 3)⟩
theorem s0661_positive_checked : check 341 s0661_positive_contract = true := by decide +kernel
def s0661_positive : CertifiedContract :=
  ⟨661, 662, 1, (.dec 3), s0661_positive_contract, 341, s0661_positive_checked⟩

def s0662_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0662_plain_checked : check 354 s0662_plain_contract = true := by decide +kernel
def s0662_plain : CertifiedContract :=
  ⟨662, 663, 0, (.inc 2), s0662_plain_contract, 354, s0662_plain_checked⟩

def s0663_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0663_plain_checked : check 381 s0663_plain_contract = true := by decide +kernel
def s0663_plain : CertifiedContract :=
  ⟨663, 664, 0, (.inc 8), s0663_plain_contract, 381, s0663_plain_checked⟩

def s0664_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s0664_plain_checked : check 100 s0664_plain_contract = true := by decide +kernel
def s0664_plain : CertifiedContract :=
  ⟨664, 661, 0, .none, s0664_plain_contract, 100, s0664_plain_checked⟩

def s0665_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s0665_zero_checked : check 341 s0665_zero_contract = true := by decide +kernel
def s0665_zero : CertifiedContract :=
  ⟨665, 668, 0, .none, s0665_zero_contract, 341, s0665_zero_checked⟩

def s0665_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s0665_positive_checked : check 341 s0665_positive_contract = true := by decide +kernel
def s0665_positive : CertifiedContract :=
  ⟨665, 666, 1, (.dec 8), s0665_positive_contract, 341, s0665_positive_checked⟩

def s0666_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, true, true, true, true] 0 (.inc 3)⟩
theorem s0666_plain_checked : check 357 s0666_plain_contract = true := by decide +kernel
def s0666_plain : CertifiedContract :=
  ⟨666, 667, 0, (.inc 3), s0666_plain_contract, 357, s0666_plain_checked⟩

def s0667_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s0667_plain_checked : check 91 s0667_plain_contract = true := by decide +kernel
def s0667_plain : CertifiedContract :=
  ⟨667, 665, 0, .none, s0667_plain_contract, 91, s0667_plain_checked⟩

def s0668_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s0668_zero_checked : check 335 s0668_zero_contract = true := by decide +kernel
def s0668_zero : CertifiedContract :=
  ⟨668, 671, 0, .none, s0668_zero_contract, 335, s0668_zero_checked⟩

def s0668_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0668_positive_checked : check 341 s0668_positive_contract = true := by decide +kernel
def s0668_positive : CertifiedContract :=
  ⟨668, 669, 1, (.dec 2), s0668_positive_contract, 341, s0668_positive_checked⟩

def s0669_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s0669_plain_checked : check 354 s0669_plain_contract = true := by decide +kernel
def s0669_plain : CertifiedContract :=
  ⟨669, 670, 0, (.inc 8), s0669_plain_contract, 354, s0669_plain_checked⟩

def s0670_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s0670_plain_checked : check 91 s0670_plain_contract = true := by decide +kernel
def s0670_plain : CertifiedContract :=
  ⟨670, 668, 0, .none, s0670_plain_contract, 91, s0670_plain_checked⟩

def s0671_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0671_zero_checked : check 356 s0671_zero_contract = true := by decide +kernel
def s0671_zero : CertifiedContract :=
  ⟨671, 674, 0, .none, s0671_zero_contract, 356, s0671_zero_checked⟩

def s0671_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0671_positive_checked : check 362 s0671_positive_contract = true := by decide +kernel
def s0671_positive : CertifiedContract :=
  ⟨671, 672, 1, (.dec 0), s0671_positive_contract, 362, s0671_positive_checked⟩

def s0672_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0672_plain_checked : check 354 s0672_plain_contract = true := by decide +kernel
def s0672_plain : CertifiedContract :=
  ⟨672, 673, 0, (.inc 2), s0672_plain_contract, 354, s0672_plain_checked⟩

def s0673_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s0673_plain_checked : check 94 s0673_plain_contract = true := by decide +kernel
def s0673_plain : CertifiedContract :=
  ⟨673, 671, 0, .none, s0673_plain_contract, 94, s0673_plain_checked⟩

def s0674_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0674_zero_checked : check 362 s0674_zero_contract = true := by decide +kernel
def s0674_zero : CertifiedContract :=
  ⟨674, 678, 0, .none, s0674_zero_contract, 362, s0674_zero_checked⟩

def s0674_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0674_positive_checked : check 368 s0674_positive_contract = true := by decide +kernel
def s0674_positive : CertifiedContract :=
  ⟨674, 675, 1, (.dec 2), s0674_positive_contract, 368, s0674_positive_checked⟩

def s0675_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0675_plain_checked : check 381 s0675_plain_contract = true := by decide +kernel
def s0675_plain : CertifiedContract :=
  ⟨675, 676, 0, (.inc 5), s0675_plain_contract, 381, s0675_plain_checked⟩

def s0676_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0676_plain_checked : check 408 s0676_plain_contract = true := by decide +kernel
def s0676_plain : CertifiedContract :=
  ⟨676, 677, 0, (.inc 8), s0676_plain_contract, 408, s0676_plain_checked⟩

def s0677_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0677_plain_checked : check 109 s0677_plain_contract = true := by decide +kernel
def s0677_plain : CertifiedContract :=
  ⟨677, 674, 0, .none, s0677_plain_contract, 109, s0677_plain_checked⟩

def s0678_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s0678_zero_checked : check 383 s0678_zero_contract = true := by decide +kernel
def s0678_zero : CertifiedContract :=
  ⟨678, 684, 0, .none, s0678_zero_contract, 383, s0678_zero_checked⟩

def s0678_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0678_positive_checked : check 386 s0678_positive_contract = true := by decide +kernel
def s0678_positive : CertifiedContract :=
  ⟨678, 679, 1, (.dec 8), s0678_positive_contract, 386, s0678_positive_checked⟩

def s0679_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0679_plain_checked : check 381 s0679_plain_contract = true := by decide +kernel
def s0679_plain : CertifiedContract :=
  ⟨679, 680, 0, (.inc 5), s0679_plain_contract, 381, s0679_plain_checked⟩

def s0680_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s0680_zero_checked : check 401 s0680_zero_contract = true := by decide +kernel
def s0680_zero : CertifiedContract :=
  ⟨680, 683, 0, .none, s0680_zero_contract, 401, s0680_zero_checked⟩

def s0680_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0680_positive_checked : check 404 s0680_positive_contract = true := by decide +kernel
def s0680_positive : CertifiedContract :=
  ⟨680, 681, 1, (.dec 8), s0680_positive_contract, 404, s0680_positive_checked⟩

def s0681_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0681_plain_checked : check 399 s0681_plain_contract = true := by decide +kernel
def s0681_plain : CertifiedContract :=
  ⟨681, 682, 0, (.inc 2), s0681_plain_contract, 399, s0681_plain_checked⟩

def s0682_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0682_plain_checked : check 109 s0682_plain_contract = true := by decide +kernel
def s0682_plain : CertifiedContract :=
  ⟨682, 680, 0, .none, s0682_plain_contract, 109, s0682_plain_checked⟩

def s0683_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0683_plain_checked : check 112 s0683_plain_contract = true := by decide +kernel
def s0683_plain : CertifiedContract :=
  ⟨683, 674, 0, .none, s0683_plain_contract, 112, s0683_plain_checked⟩

def s0684_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s0684_zero_checked : check 371 s0684_zero_contract = true := by decide +kernel
def s0684_zero : CertifiedContract :=
  ⟨684, 687, 0, .none, s0684_zero_contract, 371, s0684_zero_checked⟩

def s0684_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0684_positive_checked : check 368 s0684_positive_contract = true := by decide +kernel
def s0684_positive : CertifiedContract :=
  ⟨684, 685, 1, (.dec 5), s0684_positive_contract, 368, s0684_positive_checked⟩

def s0685_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0685_plain_checked : check 381 s0685_plain_contract = true := by decide +kernel
def s0685_plain : CertifiedContract :=
  ⟨685, 686, 0, (.inc 0), s0685_plain_contract, 381, s0685_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s0636_plain,
  s0637_plain,
  s0638_plain,
  s0639_plain,
  s0640_plain,
  s0641_plain,
  s0642_zero,
  s0642_positive,
  s0643_plain,
  s0644_plain,
  s0645_zero,
  s0645_positive,
  s0646_plain,
  s0647_plain,
  s0648_zero,
  s0648_positive,
  s0649_plain,
  s0650_plain,
  s0651_plain,
  s0652_zero,
  s0652_positive,
  s0653_plain,
  s0654_zero,
  s0654_positive,
  s0655_plain,
  s0656_plain,
  s0657_plain,
  s0658_zero,
  s0658_positive,
  s0659_plain,
  s0660_plain,
  s0661_zero,
  s0661_positive,
  s0662_plain,
  s0663_plain,
  s0664_plain,
  s0665_zero,
  s0665_positive,
  s0666_plain,
  s0667_plain,
  s0668_zero,
  s0668_positive,
  s0669_plain,
  s0670_plain,
  s0671_zero,
  s0671_positive,
  s0672_plain,
  s0673_plain,
  s0674_zero,
  s0674_positive,
  s0675_plain,
  s0676_plain,
  s0677_plain,
  s0678_zero,
  s0678_positive,
  s0679_plain,
  s0680_zero,
  s0680_positive,
  s0681_plain,
  s0682_plain,
  s0683_plain,
  s0684_zero,
  s0684_positive,
  s0685_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S013
