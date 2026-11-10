import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S075
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s3697_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3697_zero_checked : check 398 s3697_zero_contract = true := by decide +kernel
def s3697_zero : CertifiedContract :=
  ⟨3697, 3699, 0, .none, s3697_zero_contract, 398, s3697_zero_checked⟩

def s3697_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3697_positive_checked : check 404 s3697_positive_contract = true := by decide +kernel
def s3697_positive : CertifiedContract :=
  ⟨3697, 3698, 1, (.dec 8), s3697_positive_contract, 404, s3697_positive_checked⟩

def s3698_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s3698_plain_checked : check 109 s3698_plain_contract = true := by decide +kernel
def s3698_plain : CertifiedContract :=
  ⟨3698, 3702, 0, .none, s3698_plain_contract, 109, s3698_plain_checked⟩

def s3699_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s3699_zero_checked : check 410 s3699_zero_contract = true := by decide +kernel
def s3699_zero : CertifiedContract :=
  ⟨3699, 3702, 0, .none, s3699_zero_contract, 410, s3699_zero_checked⟩

def s3699_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3699_positive_checked : check 413 s3699_positive_contract = true := by decide +kernel
def s3699_positive : CertifiedContract :=
  ⟨3699, 3700, 1, (.dec 5), s3699_positive_contract, 413, s3699_positive_checked⟩

def s3700_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3700_plain_checked : check 417 s3700_plain_contract = true := by decide +kernel
def s3700_plain : CertifiedContract :=
  ⟨3700, 3701, 0, (.inc 8), s3700_plain_contract, 417, s3700_plain_checked⟩

def s3701_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3701_plain_checked : check 112 s3701_plain_contract = true := by decide +kernel
def s3701_plain : CertifiedContract :=
  ⟨3701, 3699, 0, .none, s3701_plain_contract, 112, s3701_plain_checked⟩

def s3702_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, false] 0 .none⟩
theorem s3702_plain_checked : check 103 s3702_plain_contract = true := by decide +kernel
def s3702_plain : CertifiedContract :=
  ⟨3702, 3695, 0, .none, s3702_plain_contract, 103, s3702_plain_checked⟩

def s3703_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s3703_zero_checked : check 356 s3703_zero_contract = true := by decide +kernel
def s3703_zero : CertifiedContract :=
  ⟨3703, 3706, 0, .none, s3703_zero_contract, 356, s3703_zero_checked⟩

def s3703_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s3703_positive_checked : check 359 s3703_positive_contract = true := by decide +kernel
def s3703_positive : CertifiedContract :=
  ⟨3703, 3704, 1, (.dec 5), s3703_positive_contract, 359, s3703_positive_checked⟩

def s3704_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s3704_plain_checked : check 372 s3704_plain_contract = true := by decide +kernel
def s3704_plain : CertifiedContract :=
  ⟨3704, 3705, 0, (.inc 0), s3704_plain_contract, 372, s3704_plain_checked⟩

def s3705_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, true, false] 0 .none⟩
theorem s3705_plain_checked : check 97 s3705_plain_contract = true := by decide +kernel
def s3705_plain : CertifiedContract :=
  ⟨3705, 3703, 0, .none, s3705_plain_contract, 97, s3705_plain_checked⟩

def s3706_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, true, false] 0 .none⟩
theorem s3706_zero_checked : check 353 s3706_zero_contract = true := by decide +kernel
def s3706_zero : CertifiedContract :=
  ⟨3706, 3710, 0, .none, s3706_zero_contract, 353, s3706_zero_checked⟩

def s3706_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3706_positive_checked : check 359 s3706_positive_contract = true := by decide +kernel
def s3706_positive : CertifiedContract :=
  ⟨3706, 3707, 1, (.dec 2), s3706_positive_contract, 359, s3706_positive_checked⟩

def s3707_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3707_plain_checked : check 372 s3707_plain_contract = true := by decide +kernel
def s3707_plain : CertifiedContract :=
  ⟨3707, 3708, 0, (.inc 5), s3707_plain_contract, 372, s3707_plain_checked⟩

def s3708_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3708_plain_checked : check 399 s3708_plain_contract = true := by decide +kernel
def s3708_plain : CertifiedContract :=
  ⟨3708, 3709, 0, (.inc 8), s3708_plain_contract, 399, s3708_plain_checked⟩

def s3709_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s3709_plain_checked : check 106 s3709_plain_contract = true := by decide +kernel
def s3709_plain : CertifiedContract :=
  ⟨3709, 3706, 0, .none, s3709_plain_contract, 106, s3709_plain_checked⟩

def s3710_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, true, false] 0 .none⟩
theorem s3710_zero_checked : check 374 s3710_zero_contract = true := by decide +kernel
def s3710_zero : CertifiedContract :=
  ⟨3710, 3716, 0, .none, s3710_zero_contract, 374, s3710_zero_checked⟩

def s3710_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3710_positive_checked : check 377 s3710_positive_contract = true := by decide +kernel
def s3710_positive : CertifiedContract :=
  ⟨3710, 3711, 1, (.dec 8), s3710_positive_contract, 377, s3710_positive_checked⟩

def s3711_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3711_plain_checked : check 372 s3711_plain_contract = true := by decide +kernel
def s3711_plain : CertifiedContract :=
  ⟨3711, 3712, 0, (.inc 5), s3711_plain_contract, 372, s3711_plain_checked⟩

def s3712_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, true, true, true] 0 .none⟩
theorem s3712_zero_checked : check 392 s3712_zero_contract = true := by decide +kernel
def s3712_zero : CertifiedContract :=
  ⟨3712, 3715, 0, .none, s3712_zero_contract, 392, s3712_zero_checked⟩

def s3712_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3712_positive_checked : check 395 s3712_positive_contract = true := by decide +kernel
def s3712_positive : CertifiedContract :=
  ⟨3712, 3713, 1, (.dec 8), s3712_positive_contract, 395, s3712_positive_checked⟩

def s3713_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3713_plain_checked : check 390 s3713_plain_contract = true := by decide +kernel
def s3713_plain : CertifiedContract :=
  ⟨3713, 3714, 0, (.inc 2), s3713_plain_contract, 390, s3713_plain_checked⟩

def s3714_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3714_plain_checked : check 106 s3714_plain_contract = true := by decide +kernel
def s3714_plain : CertifiedContract :=
  ⟨3714, 3712, 0, .none, s3714_plain_contract, 106, s3714_plain_checked⟩

def s3715_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s3715_plain_checked : check 109 s3715_plain_contract = true := by decide +kernel
def s3715_plain : CertifiedContract :=
  ⟨3715, 3706, 0, .none, s3715_plain_contract, 109, s3715_plain_checked⟩

def s3716_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s3716_zero_checked : check 359 s3716_zero_contract = true := by decide +kernel
def s3716_zero : CertifiedContract :=
  ⟨3716, 3722, 0, .none, s3716_zero_contract, 359, s3716_zero_checked⟩

def s3716_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3716_positive_checked : check 359 s3716_positive_contract = true := by decide +kernel
def s3716_positive : CertifiedContract :=
  ⟨3716, 3717, 1, (.dec 5), s3716_positive_contract, 359, s3716_positive_checked⟩

def s3717_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3717_plain_checked : check 372 s3717_plain_contract = true := by decide +kernel
def s3717_plain : CertifiedContract :=
  ⟨3717, 3718, 0, (.inc 2), s3717_plain_contract, 372, s3717_plain_checked⟩

def s3718_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3718_plain_checked : check 375 s3718_plain_contract = true := by decide +kernel
def s3718_plain : CertifiedContract :=
  ⟨3718, 3719, 0, (.inc 2), s3718_plain_contract, 375, s3718_plain_checked⟩

def s3719_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3719_plain_checked : check 372 s3719_plain_contract = true := by decide +kernel
def s3719_plain : CertifiedContract :=
  ⟨3719, 3720, 0, (.inc 2), s3719_plain_contract, 372, s3719_plain_checked⟩

def s3720_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s3720_plain_checked : check 378 s3720_plain_contract = true := by decide +kernel
def s3720_plain : CertifiedContract :=
  ⟨3720, 3721, 0, (.inc 2), s3720_plain_contract, 378, s3720_plain_checked⟩

def s3721_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, true, false] 0 .none⟩
theorem s3721_plain_checked : check 94 s3721_plain_contract = true := by decide +kernel
def s3721_plain : CertifiedContract :=
  ⟨3721, 3716, 0, .none, s3721_plain_contract, 94, s3721_plain_checked⟩

def s3722_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, false, false] 0 .none⟩
theorem s3722_zero_checked : check 362 s3722_zero_contract = true := by decide +kernel
def s3722_zero : CertifiedContract :=
  ⟨3722, 3725, 0, .none, s3722_zero_contract, 362, s3722_zero_checked⟩

def s3722_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, false, true, false] 1 (.dec 2)⟩
theorem s3722_positive_checked : check 368 s3722_positive_contract = true := by decide +kernel
def s3722_positive : CertifiedContract :=
  ⟨3722, 3723, 1, (.dec 2), s3722_positive_contract, 368, s3722_positive_checked⟩

def s3723_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, false, true, true] 0 (.inc 8)⟩
theorem s3723_plain_checked : check 381 s3723_plain_contract = true := by decide +kernel
def s3723_plain : CertifiedContract :=
  ⟨3723, 3724, 0, (.inc 8), s3723_plain_contract, 381, s3723_plain_checked⟩

def s3724_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s3724_plain_checked : check 100 s3724_plain_contract = true := by decide +kernel
def s3724_plain : CertifiedContract :=
  ⟨3724, 3722, 0, .none, s3724_plain_contract, 100, s3724_plain_checked⟩

def s3725_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s3725_zero_checked : check 383 s3725_zero_contract = true := by decide +kernel
def s3725_zero : CertifiedContract :=
  ⟨3725, 3728, 0, .none, s3725_zero_contract, 383, s3725_zero_checked⟩

def s3725_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s3725_positive_checked : check 389 s3725_positive_contract = true := by decide +kernel
def s3725_positive : CertifiedContract :=
  ⟨3725, 3726, 1, (.dec 0), s3725_positive_contract, 389, s3725_positive_checked⟩

def s3726_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s3726_plain_checked : check 381 s3726_plain_contract = true := by decide +kernel
def s3726_plain : CertifiedContract :=
  ⟨3726, 3727, 0, (.inc 2), s3726_plain_contract, 381, s3726_plain_checked⟩

def s3727_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, false, false] 0 .none⟩
theorem s3727_plain_checked : check 103 s3727_plain_contract = true := by decide +kernel
def s3727_plain : CertifiedContract :=
  ⟨3727, 3725, 0, .none, s3727_plain_contract, 103, s3727_plain_checked⟩

def s3728_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3728_zero_checked : check 389 s3728_zero_contract = true := by decide +kernel
def s3728_zero : CertifiedContract :=
  ⟨3728, 3732, 0, .none, s3728_zero_contract, 389, s3728_zero_checked⟩

def s3728_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3728_positive_checked : check 395 s3728_positive_contract = true := by decide +kernel
def s3728_positive : CertifiedContract :=
  ⟨3728, 3729, 1, (.dec 2), s3728_positive_contract, 395, s3728_positive_checked⟩

def s3729_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3729_plain_checked : check 408 s3729_plain_contract = true := by decide +kernel
def s3729_plain : CertifiedContract :=
  ⟨3729, 3730, 0, (.inc 5), s3729_plain_contract, 408, s3729_plain_checked⟩

def s3730_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3730_plain_checked : check 435 s3730_plain_contract = true := by decide +kernel
def s3730_plain : CertifiedContract :=
  ⟨3730, 3731, 0, (.inc 8), s3730_plain_contract, 435, s3730_plain_checked⟩

def s3731_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s3731_plain_checked : check 118 s3731_plain_contract = true := by decide +kernel
def s3731_plain : CertifiedContract :=
  ⟨3731, 3728, 0, .none, s3731_plain_contract, 118, s3731_plain_checked⟩

def s3732_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s3732_zero_checked : check 410 s3732_zero_contract = true := by decide +kernel
def s3732_zero : CertifiedContract :=
  ⟨3732, 3738, 0, .none, s3732_zero_contract, 410, s3732_zero_checked⟩

def s3732_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3732_positive_checked : check 413 s3732_positive_contract = true := by decide +kernel
def s3732_positive : CertifiedContract :=
  ⟨3732, 3733, 1, (.dec 8), s3732_positive_contract, 413, s3732_positive_checked⟩

def s3733_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3733_plain_checked : check 408 s3733_plain_contract = true := by decide +kernel
def s3733_plain : CertifiedContract :=
  ⟨3733, 3734, 0, (.inc 5), s3733_plain_contract, 408, s3733_plain_checked⟩

def s3734_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s3734_zero_checked : check 428 s3734_zero_contract = true := by decide +kernel
def s3734_zero : CertifiedContract :=
  ⟨3734, 3737, 0, .none, s3734_zero_contract, 428, s3734_zero_checked⟩

def s3734_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3734_positive_checked : check 431 s3734_positive_contract = true := by decide +kernel
def s3734_positive : CertifiedContract :=
  ⟨3734, 3735, 1, (.dec 8), s3734_positive_contract, 431, s3734_positive_checked⟩

def s3735_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3735_plain_checked : check 426 s3735_plain_contract = true := by decide +kernel
def s3735_plain : CertifiedContract :=
  ⟨3735, 3736, 0, (.inc 2), s3735_plain_contract, 426, s3735_plain_checked⟩

def s3736_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3736_plain_checked : check 118 s3736_plain_contract = true := by decide +kernel
def s3736_plain : CertifiedContract :=
  ⟨3736, 3734, 0, .none, s3736_plain_contract, 118, s3736_plain_checked⟩

def s3737_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s3737_plain_checked : check 121 s3737_plain_contract = true := by decide +kernel
def s3737_plain : CertifiedContract :=
  ⟨3737, 3728, 0, .none, s3737_plain_contract, 121, s3737_plain_checked⟩

def s3738_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, true] 0 .none⟩
theorem s3738_zero_checked : check 398 s3738_zero_contract = true := by decide +kernel
def s3738_zero : CertifiedContract :=
  ⟨3738, 3741, 0, .none, s3738_zero_contract, 398, s3738_zero_checked⟩

def s3738_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s3738_positive_checked : check 395 s3738_positive_contract = true := by decide +kernel
def s3738_positive : CertifiedContract :=
  ⟨3738, 3739, 1, (.dec 5), s3738_positive_contract, 395, s3738_positive_checked⟩

def s3739_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s3739_plain_checked : check 408 s3739_plain_contract = true := by decide +kernel
def s3739_plain : CertifiedContract :=
  ⟨3739, 3740, 0, (.inc 0), s3739_plain_contract, 408, s3739_plain_checked⟩

def s3740_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s3740_plain_checked : check 109 s3740_plain_contract = true := by decide +kernel
def s3740_plain : CertifiedContract :=
  ⟨3740, 3738, 0, .none, s3740_plain_contract, 109, s3740_plain_checked⟩

def s3741_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, false] 0 (.inc 2)⟩
theorem s3741_plain_checked : check 348 s3741_plain_contract = true := by decide +kernel
def s3741_plain : CertifiedContract :=
  ⟨3741, 3742, 0, (.inc 2), s3741_plain_contract, 348, s3741_plain_checked⟩

def s3742_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3742_zero_checked : check 365 s3742_zero_contract = true := by decide +kernel
def s3742_zero : CertifiedContract :=
  ⟨3742, 3750, 0, .none, s3742_zero_contract, 365, s3742_zero_checked⟩

def s3742_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, false] 1 (.dec 0)⟩
theorem s3742_positive_checked : check 371 s3742_positive_contract = true := by decide +kernel
def s3742_positive : CertifiedContract :=
  ⟨3742, 3743, 1, (.dec 0), s3742_positive_contract, 371, s3742_positive_checked⟩

def s3743_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3743_plain_checked : check 381 s3743_plain_contract = true := by decide +kernel
def s3743_plain : CertifiedContract :=
  ⟨3743, 3744, 0, (.inc 5), s3743_plain_contract, 381, s3743_plain_checked⟩

def s3744_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3744_zero_checked : check 407 s3744_zero_contract = true := by decide +kernel
def s3744_zero : CertifiedContract :=
  ⟨3744, 3746, 0, .none, s3744_zero_contract, 407, s3744_zero_checked⟩

def s3744_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3744_positive_checked : check 413 s3744_positive_contract = true := by decide +kernel
def s3744_positive : CertifiedContract :=
  ⟨3744, 3745, 1, (.dec 8), s3744_positive_contract, 413, s3744_positive_checked⟩

def s3745_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, true] 0 .none⟩
theorem s3745_plain_checked : check 112 s3745_plain_contract = true := by decide +kernel
def s3745_plain : CertifiedContract :=
  ⟨3745, 3749, 0, .none, s3745_plain_contract, 112, s3745_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s3697_zero,
  s3697_positive,
  s3698_plain,
  s3699_zero,
  s3699_positive,
  s3700_plain,
  s3701_plain,
  s3702_plain,
  s3703_zero,
  s3703_positive,
  s3704_plain,
  s3705_plain,
  s3706_zero,
  s3706_positive,
  s3707_plain,
  s3708_plain,
  s3709_plain,
  s3710_zero,
  s3710_positive,
  s3711_plain,
  s3712_zero,
  s3712_positive,
  s3713_plain,
  s3714_plain,
  s3715_plain,
  s3716_zero,
  s3716_positive,
  s3717_plain,
  s3718_plain,
  s3719_plain,
  s3720_plain,
  s3721_plain,
  s3722_zero,
  s3722_positive,
  s3723_plain,
  s3724_plain,
  s3725_zero,
  s3725_positive,
  s3726_plain,
  s3727_plain,
  s3728_zero,
  s3728_positive,
  s3729_plain,
  s3730_plain,
  s3731_plain,
  s3732_zero,
  s3732_positive,
  s3733_plain,
  s3734_zero,
  s3734_positive,
  s3735_plain,
  s3736_plain,
  s3737_plain,
  s3738_zero,
  s3738_positive,
  s3739_plain,
  s3740_plain,
  s3741_plain,
  s3742_zero,
  s3742_positive,
  s3743_plain,
  s3744_zero,
  s3744_positive,
  s3745_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S075
