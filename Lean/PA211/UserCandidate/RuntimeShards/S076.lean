import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S076
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s3746_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, true] 0 .none⟩
theorem s3746_zero_checked : check 420 s3746_zero_contract = true := by decide +kernel
def s3746_zero : CertifiedContract :=
  ⟨3746, 3749, 0, .none, s3746_zero_contract, 420, s3746_zero_checked⟩

def s3746_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3746_positive_checked : check 423 s3746_positive_contract = true := by decide +kernel
def s3746_positive : CertifiedContract :=
  ⟨3746, 3747, 1, (.dec 5), s3746_positive_contract, 423, s3746_positive_checked⟩

def s3747_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3747_plain_checked : check 427 s3747_plain_contract = true := by decide +kernel
def s3747_plain : CertifiedContract :=
  ⟨3747, 3748, 0, (.inc 8), s3747_plain_contract, 427, s3747_plain_checked⟩

def s3748_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3748_plain_checked : check 116 s3748_plain_contract = true := by decide +kernel
def s3748_plain : CertifiedContract :=
  ⟨3748, 3746, 0, .none, s3748_plain_contract, 116, s3748_plain_checked⟩

def s3749_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s3749_plain_checked : check 107 s3749_plain_contract = true := by decide +kernel
def s3749_plain : CertifiedContract :=
  ⟨3749, 3742, 0, .none, s3749_plain_contract, 107, s3749_plain_checked⟩

def s3750_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, false, false] 0 .none⟩
theorem s3750_zero_checked : check 366 s3750_zero_contract = true := by decide +kernel
def s3750_zero : CertifiedContract :=
  ⟨3750, 3753, 0, .none, s3750_zero_contract, 366, s3750_zero_checked⟩

def s3750_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3750_positive_checked : check 369 s3750_positive_contract = true := by decide +kernel
def s3750_positive : CertifiedContract :=
  ⟨3750, 3751, 1, (.dec 5), s3750_positive_contract, 369, s3750_positive_checked⟩

def s3751_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, true] 0 (.inc 0)⟩
theorem s3751_plain_checked : check 382 s3751_plain_contract = true := by decide +kernel
def s3751_plain : CertifiedContract :=
  ⟨3751, 3752, 0, (.inc 0), s3751_plain_contract, 382, s3751_plain_checked⟩

def s3752_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3752_plain_checked : check 101 s3752_plain_contract = true := by decide +kernel
def s3752_plain : CertifiedContract :=
  ⟨3752, 3750, 0, .none, s3752_plain_contract, 101, s3752_plain_checked⟩

def s3753_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, true, false] 0 .none⟩
theorem s3753_zero_checked : check 363 s3753_zero_contract = true := by decide +kernel
def s3753_zero : CertifiedContract :=
  ⟨3753, 3757, 0, .none, s3753_zero_contract, 363, s3753_zero_checked⟩

def s3753_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3753_positive_checked : check 369 s3753_positive_contract = true := by decide +kernel
def s3753_positive : CertifiedContract :=
  ⟨3753, 3754, 1, (.dec 2), s3753_positive_contract, 369, s3753_positive_checked⟩

def s3754_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3754_plain_checked : check 382 s3754_plain_contract = true := by decide +kernel
def s3754_plain : CertifiedContract :=
  ⟨3754, 3755, 0, (.inc 5), s3754_plain_contract, 382, s3754_plain_checked⟩

def s3755_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3755_plain_checked : check 409 s3755_plain_contract = true := by decide +kernel
def s3755_plain : CertifiedContract :=
  ⟨3755, 3756, 0, (.inc 8), s3755_plain_contract, 409, s3755_plain_checked⟩

def s3756_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, false, false] 0 .none⟩
theorem s3756_plain_checked : check 110 s3756_plain_contract = true := by decide +kernel
def s3756_plain : CertifiedContract :=
  ⟨3756, 3753, 0, .none, s3756_plain_contract, 110, s3756_plain_checked⟩

def s3757_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, true, false] 0 .none⟩
theorem s3757_zero_checked : check 384 s3757_zero_contract = true := by decide +kernel
def s3757_zero : CertifiedContract :=
  ⟨3757, 3763, 0, .none, s3757_zero_contract, 384, s3757_zero_checked⟩

def s3757_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3757_positive_checked : check 387 s3757_positive_contract = true := by decide +kernel
def s3757_positive : CertifiedContract :=
  ⟨3757, 3758, 1, (.dec 8), s3757_positive_contract, 387, s3757_positive_checked⟩

def s3758_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3758_plain_checked : check 382 s3758_plain_contract = true := by decide +kernel
def s3758_plain : CertifiedContract :=
  ⟨3758, 3759, 0, (.inc 5), s3758_plain_contract, 382, s3758_plain_checked⟩

def s3759_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, true, true, true] 0 .none⟩
theorem s3759_zero_checked : check 402 s3759_zero_contract = true := by decide +kernel
def s3759_zero : CertifiedContract :=
  ⟨3759, 3762, 0, .none, s3759_zero_contract, 402, s3759_zero_checked⟩

def s3759_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3759_positive_checked : check 405 s3759_positive_contract = true := by decide +kernel
def s3759_positive : CertifiedContract :=
  ⟨3759, 3760, 1, (.dec 8), s3759_positive_contract, 405, s3759_positive_checked⟩

def s3760_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3760_plain_checked : check 400 s3760_plain_contract = true := by decide +kernel
def s3760_plain : CertifiedContract :=
  ⟨3760, 3761, 0, (.inc 2), s3760_plain_contract, 400, s3760_plain_checked⟩

def s3761_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3761_plain_checked : check 110 s3761_plain_contract = true := by decide +kernel
def s3761_plain : CertifiedContract :=
  ⟨3761, 3759, 0, .none, s3761_plain_contract, 110, s3761_plain_checked⟩

def s3762_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, false, false, false] 0 .none⟩
theorem s3762_plain_checked : check 113 s3762_plain_contract = true := by decide +kernel
def s3762_plain : CertifiedContract :=
  ⟨3762, 3753, 0, .none, s3762_plain_contract, 113, s3762_plain_checked⟩

def s3763_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, false] 0 .none⟩
theorem s3763_zero_checked : check 375 s3763_zero_contract = true := by decide +kernel
def s3763_zero : CertifiedContract :=
  ⟨3763, 3769, 0, .none, s3763_zero_contract, 375, s3763_zero_checked⟩

def s3763_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3763_positive_checked : check 369 s3763_positive_contract = true := by decide +kernel
def s3763_positive : CertifiedContract :=
  ⟨3763, 3764, 1, (.dec 5), s3763_positive_contract, 369, s3763_positive_checked⟩

def s3764_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3764_plain_checked : check 382 s3764_plain_contract = true := by decide +kernel
def s3764_plain : CertifiedContract :=
  ⟨3764, 3765, 0, (.inc 2), s3764_plain_contract, 382, s3764_plain_checked⟩

def s3765_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3765_plain_checked : check 385 s3765_plain_contract = true := by decide +kernel
def s3765_plain : CertifiedContract :=
  ⟨3765, 3766, 0, (.inc 2), s3765_plain_contract, 385, s3765_plain_checked⟩

def s3766_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3766_plain_checked : check 391 s3766_plain_contract = true := by decide +kernel
def s3766_plain : CertifiedContract :=
  ⟨3766, 3767, 0, (.inc 2), s3766_plain_contract, 391, s3766_plain_checked⟩

def s3767_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, true, true, true] 0 (.inc 2)⟩
theorem s3767_plain_checked : check 397 s3767_plain_contract = true := by decide +kernel
def s3767_plain : CertifiedContract :=
  ⟨3767, 3768, 0, (.inc 2), s3767_plain_contract, 397, s3767_plain_checked⟩

def s3768_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, true, false] 0 .none⟩
theorem s3768_plain_checked : check 98 s3768_plain_contract = true := by decide +kernel
def s3768_plain : CertifiedContract :=
  ⟨3768, 3763, 0, .none, s3768_plain_contract, 98, s3768_plain_checked⟩

def s3769_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, false, false, false] 0 .none⟩
theorem s3769_zero_checked : check 324 s3769_zero_contract = true := by decide +kernel
def s3769_zero : CertifiedContract :=
  ⟨3769, 3773, 0, .none, s3769_zero_contract, 324, s3769_zero_checked⟩

def s3769_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, true, false] 1 (.dec 4)⟩
theorem s3769_positive_checked : check 324 s3769_positive_contract = true := by decide +kernel
def s3769_positive : CertifiedContract :=
  ⟨3769, 3770, 1, (.dec 4), s3769_positive_contract, 324, s3769_positive_checked⟩

def s3770_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, true, true, false] 0 (.inc 5)⟩
theorem s3770_plain_checked : check 346 s3770_plain_contract = true := by decide +kernel
def s3770_plain : CertifiedContract :=
  ⟨3770, 3771, 0, (.inc 5), s3770_plain_contract, 346, s3770_plain_checked⟩

def s3771_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, true, true, true] 0 (.inc 8)⟩
theorem s3771_plain_checked : check 373 s3771_plain_contract = true := by decide +kernel
def s3771_plain : CertifiedContract :=
  ⟨3771, 3772, 0, (.inc 8), s3771_plain_contract, 373, s3771_plain_checked⟩

def s3772_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, true, false] 0 .none⟩
theorem s3772_plain_checked : check 98 s3772_plain_contract = true := by decide +kernel
def s3772_plain : CertifiedContract :=
  ⟨3772, 3769, 0, .none, s3772_plain_contract, 98, s3772_plain_checked⟩

def s3773_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, false, true] 0 .none⟩
theorem s3773_zero_checked : check 336 s3773_zero_contract = true := by decide +kernel
def s3773_zero : CertifiedContract :=
  ⟨3773, 3777, 0, .none, s3773_zero_contract, 336, s3773_zero_checked⟩

def s3773_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, false, false, true, false, false] 1 (.dec 7)⟩
theorem s3773_positive_checked : check 342 s3773_positive_contract = true := by decide +kernel
def s3773_positive : CertifiedContract :=
  ⟨3773, 3774, 1, (.dec 7), s3773_positive_contract, 342, s3773_positive_checked⟩

def s3774_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, false, false, true, true] 0 .none⟩
theorem s3774_zero_checked : check 354 s3774_zero_contract = true := by decide +kernel
def s3774_zero : CertifiedContract :=
  ⟨3774, 3776, 0, .none, s3774_zero_contract, 354, s3774_zero_checked⟩

def s3774_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, false, false, true, false, true] 1 (.dec 8)⟩
theorem s3774_positive_checked : check 360 s3774_positive_contract = true := by decide +kernel
def s3774_positive : CertifiedContract :=
  ⟨3774, 3775, 1, (.dec 8), s3774_positive_contract, 360, s3774_positive_checked⟩

def s3775_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, false, false, true, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, false, false, false] 0 .none⟩
theorem s3775_plain_checked : check 95 s3775_plain_contract = true := by decide +kernel
def s3775_plain : CertifiedContract :=
  ⟨3775, 3773, 0, .none, s3775_plain_contract, 95, s3775_plain_checked⟩

def s3776_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s3776_plain_checked : check 109 s3776_plain_contract = true := by decide +kernel
def s3776_plain : CertifiedContract :=
  ⟨3776, 3778, 0, .none, s3776_plain_contract, 109, s3776_plain_checked⟩

def s3777_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, true, false] 0 .none⟩
theorem s3777_zero_checked : check 330 s3777_zero_contract = true := by decide +kernel
def s3777_zero : CertifiedContract :=
  ⟨3777, 3783, 0, .none, s3777_zero_contract, 330, s3777_zero_checked⟩

def s3777_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, true, false, false] 1 (.dec 8)⟩
theorem s3777_positive_checked : check 336 s3777_positive_contract = true := by decide +kernel
def s3777_positive : CertifiedContract :=
  ⟨3777, 3778, 1, (.dec 8), s3777_positive_contract, 336, s3777_positive_checked⟩

def s3778_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s3778_zero_checked : check 345 s3778_zero_contract = true := by decide +kernel
def s3778_zero : CertifiedContract :=
  ⟨3778, 3780, 0, .none, s3778_zero_contract, 345, s3778_zero_checked⟩

def s3778_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, true, false, true] 1 (.dec 7)⟩
theorem s3778_positive_checked : check 351 s3778_positive_contract = true := by decide +kernel
def s3778_positive : CertifiedContract :=
  ⟨3778, 3779, 1, (.dec 7), s3778_positive_contract, 351, s3778_positive_checked⟩

def s3779_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, true, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s3779_plain_checked : check 89 s3779_plain_contract = true := by decide +kernel
def s3779_plain : CertifiedContract :=
  ⟨3779, 3778, 0, .none, s3779_plain_contract, 89, s3779_plain_checked⟩

def s3780_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s3780_zero_checked : check 345 s3780_zero_contract = true := by decide +kernel
def s3780_zero : CertifiedContract :=
  ⟨3780, 3782, 0, .none, s3780_zero_contract, 345, s3780_zero_checked⟩

def s3780_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, true, true, false, true] 1 (.dec 8)⟩
theorem s3780_positive_checked : check 351 s3780_positive_contract = true := by decide +kernel
def s3780_positive : CertifiedContract :=
  ⟨3780, 3781, 1, (.dec 8), s3780_positive_contract, 351, s3780_positive_checked⟩

def s3781_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, true, true, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s3781_plain_checked : check 92 s3781_plain_contract = true := by decide +kernel
def s3781_plain : CertifiedContract :=
  ⟨3781, 3778, 0, .none, s3781_plain_contract, 92, s3781_plain_checked⟩

def s3782_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, false, false] 0 .none⟩
theorem s3782_plain_checked : check 109 s3782_plain_contract = true := by decide +kernel
def s3782_plain : CertifiedContract :=
  ⟨3782, 3785, 0, .none, s3782_plain_contract, 109, s3782_plain_checked⟩

def s3783_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, false, false] 0 .none⟩
theorem s3783_zero_checked : check 330 s3783_zero_contract = true := by decide +kernel
def s3783_zero : CertifiedContract :=
  ⟨3783, 3785, 0, .none, s3783_zero_contract, 330, s3783_zero_checked⟩

def s3783_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, true, true] 1 (.dec 2)⟩
theorem s3783_positive_checked : check 333 s3783_positive_contract = true := by decide +kernel
def s3783_positive : CertifiedContract :=
  ⟨3783, 3784, 1, (.dec 2), s3783_positive_contract, 333, s3783_positive_checked⟩

def s3784_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, false, true, false] 0 .none⟩
theorem s3784_plain_checked : check 83 s3784_plain_contract = true := by decide +kernel
def s3784_plain : CertifiedContract :=
  ⟨3784, 3783, 0, .none, s3784_plain_contract, 83, s3784_plain_checked⟩

def s3785_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, true, false] 0 .none⟩
theorem s3785_zero_checked : check 336 s3785_zero_contract = true := by decide +kernel
def s3785_zero : CertifiedContract :=
  ⟨3785, 3788, 0, .none, s3785_zero_contract, 336, s3785_zero_checked⟩

def s3785_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, false, true, false] 1 (.dec 5)⟩
theorem s3785_positive_checked : check 342 s3785_positive_contract = true := by decide +kernel
def s3785_positive : CertifiedContract :=
  ⟨3785, 3786, 1, (.dec 5), s3785_positive_contract, 342, s3785_positive_checked⟩

def s3786_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, false, true, true] 0 (.inc 8)⟩
theorem s3786_plain_checked : check 346 s3786_plain_contract = true := by decide +kernel
def s3786_plain : CertifiedContract :=
  ⟨3786, 3787, 0, (.inc 8), s3786_plain_contract, 346, s3786_plain_checked⟩

def s3787_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, false, false] 0 .none⟩
theorem s3787_plain_checked : check 89 s3787_plain_contract = true := by decide +kernel
def s3787_plain : CertifiedContract :=
  ⟨3787, 3785, 0, .none, s3787_plain_contract, 89, s3787_plain_checked⟩

def s3788_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, false] 0 .none⟩
theorem s3788_zero_checked : check 330 s3788_zero_contract = true := by decide +kernel
def s3788_zero : CertifiedContract :=
  ⟨3788, 3791, 0, .none, s3788_zero_contract, 330, s3788_zero_checked⟩

def s3788_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, true, true, false] 1 (.dec 3)⟩
theorem s3788_positive_checked : check 333 s3788_positive_contract = true := by decide +kernel
def s3788_positive : CertifiedContract :=
  ⟨3788, 3789, 1, (.dec 3), s3788_positive_contract, 333, s3788_positive_checked⟩

def s3789_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true] 0 (.inc 7)⟩
theorem s3789_plain_checked : check 373 s3789_plain_contract = true := by decide +kernel
def s3789_plain : CertifiedContract :=
  ⟨3789, 3790, 0, (.inc 7), s3789_plain_contract, 373, s3789_plain_checked⟩

def s3790_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, false, true, false] 0 .none⟩
theorem s3790_plain_checked : check 92 s3790_plain_contract = true := by decide +kernel
def s3790_plain : CertifiedContract :=
  ⟨3790, 3788, 0, .none, s3790_plain_contract, 92, s3790_plain_checked⟩

def s3791_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, true] 0 .none⟩
theorem s3791_zero_checked : check 345 s3791_zero_contract = true := by decide +kernel
def s3791_zero : CertifiedContract :=
  ⟨3791, 3795, 0, .none, s3791_zero_contract, 345, s3791_zero_checked⟩

def s3791_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, false, false] 1 (.dec 7)⟩
theorem s3791_positive_checked : check 351 s3791_positive_contract = true := by decide +kernel
def s3791_positive : CertifiedContract :=
  ⟨3791, 3792, 1, (.dec 7), s3791_positive_contract, 351, s3791_positive_checked⟩

def s3792_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, true] 0 .none⟩
theorem s3792_zero_checked : check 363 s3792_zero_contract = true := by decide +kernel
def s3792_zero : CertifiedContract :=
  ⟨3792, 3794, 0, .none, s3792_zero_contract, 363, s3792_zero_checked⟩

def s3792_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, false, true] 1 (.dec 8)⟩
theorem s3792_positive_checked : check 369 s3792_positive_contract = true := by decide +kernel
def s3792_positive : CertifiedContract :=
  ⟨3792, 3793, 1, (.dec 8), s3792_positive_contract, 369, s3792_positive_checked⟩

end PA211.UserCandidate.RuntimeShards.S076
