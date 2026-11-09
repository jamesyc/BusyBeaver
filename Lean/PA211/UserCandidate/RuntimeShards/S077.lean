import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S077
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s3793_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, false] 0 .none⟩
theorem s3793_plain_checked : check 98 s3793_plain_contract = true := by decide +kernel
def s3793_plain : CertifiedContract :=
  ⟨3793, 3791, 0, .none, s3793_plain_contract, 98, s3793_plain_checked⟩

def s3794_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, false, false] 0 .none⟩
theorem s3794_plain_checked : check 112 s3794_plain_contract = true := by decide +kernel
def s3794_plain : CertifiedContract :=
  ⟨3794, 3796, 0, .none, s3794_plain_contract, 112, s3794_plain_checked⟩

def s3795_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, true, false] 0 .none⟩
theorem s3795_zero_checked : check 339 s3795_zero_contract = true := by decide +kernel
def s3795_zero : CertifiedContract :=
  ⟨3795, 3801, 0, .none, s3795_zero_contract, 339, s3795_zero_checked⟩

def s3795_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, false, false] 1 (.dec 8)⟩
theorem s3795_positive_checked : check 345 s3795_positive_contract = true := by decide +kernel
def s3795_positive : CertifiedContract :=
  ⟨3795, 3796, 1, (.dec 8), s3795_positive_contract, 345, s3795_positive_checked⟩

def s3796_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, false, false] 0 .none⟩
theorem s3796_zero_checked : check 354 s3796_zero_contract = true := by decide +kernel
def s3796_zero : CertifiedContract :=
  ⟨3796, 3798, 0, .none, s3796_zero_contract, 354, s3796_zero_checked⟩

def s3796_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, false, true] 1 (.dec 7)⟩
theorem s3796_positive_checked : check 360 s3796_positive_contract = true := by decide +kernel
def s3796_positive : CertifiedContract :=
  ⟨3796, 3797, 1, (.dec 7), s3796_positive_contract, 360, s3796_positive_checked⟩

def s3797_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, false, false] 0 .none⟩
theorem s3797_plain_checked : check 92 s3797_plain_contract = true := by decide +kernel
def s3797_plain : CertifiedContract :=
  ⟨3797, 3796, 0, .none, s3797_plain_contract, 92, s3797_plain_checked⟩

def s3798_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true] 0 .none⟩
theorem s3798_zero_checked : check 354 s3798_zero_contract = true := by decide +kernel
def s3798_zero : CertifiedContract :=
  ⟨3798, 3800, 0, .none, s3798_zero_contract, 354, s3798_zero_checked⟩

def s3798_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, false, true] 1 (.dec 8)⟩
theorem s3798_positive_checked : check 360 s3798_positive_contract = true := by decide +kernel
def s3798_positive : CertifiedContract :=
  ⟨3798, 3799, 1, (.dec 8), s3798_positive_contract, 360, s3798_positive_checked⟩

def s3799_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, false, false] 0 .none⟩
theorem s3799_plain_checked : check 95 s3799_plain_contract = true := by decide +kernel
def s3799_plain : CertifiedContract :=
  ⟨3799, 3796, 0, .none, s3799_plain_contract, 95, s3799_plain_checked⟩

def s3800_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, true] 0 .none⟩
theorem s3800_plain_checked : check 133 s3800_plain_contract = true := by decide +kernel
def s3800_plain : CertifiedContract :=
  ⟨3800, 3803, 0, .none, s3800_plain_contract, 133, s3800_plain_checked⟩

def s3801_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, true] 0 .none⟩
theorem s3801_zero_checked : check 360 s3801_zero_contract = true := by decide +kernel
def s3801_zero : CertifiedContract :=
  ⟨3801, 3803, 0, .none, s3801_zero_contract, 360, s3801_zero_checked⟩

def s3801_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, true, true] 1 (.dec 2)⟩
theorem s3801_positive_checked : check 342 s3801_positive_contract = true := by decide +kernel
def s3801_positive : CertifiedContract :=
  ⟨3801, 3802, 1, (.dec 2), s3801_positive_contract, 342, s3801_positive_checked⟩

def s3802_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, true, false] 0 .none⟩
theorem s3802_plain_checked : check 86 s3802_plain_contract = true := by decide +kernel
def s3802_plain : CertifiedContract :=
  ⟨3802, 3801, 0, .none, s3802_plain_contract, 86, s3802_plain_checked⟩

def s3803_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, true] 0 .none⟩
theorem s3803_plain_checked : check 85 s3803_plain_contract = true := by decide +kernel
def s3803_plain : CertifiedContract :=
  ⟨3803, 3910, 0, .none, s3803_plain_contract, 85, s3803_plain_checked⟩

def s3804_zero_contract : Contract :=
  ⟨(some (1, true)), rootFrame [true, false, true, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, true, false, false, false, false, true, false] 0 .none⟩
theorem s3804_zero_checked : check 267 s3804_zero_contract = true := by decide +kernel
def s3804_zero : CertifiedContract :=
  ⟨3804, 3812, 0, .none, s3804_zero_contract, 267, s3804_zero_checked⟩

def s3804_positive_contract : Contract :=
  ⟨(some (1, false)), rootFrame [true, false, true, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, true, false, false, false, false, false, true, false] 1 (.dec 1)⟩
theorem s3804_positive_checked : check 273 s3804_positive_contract = true := by decide +kernel
def s3804_positive : CertifiedContract :=
  ⟨3804, 3805, 1, (.dec 1), s3804_positive_contract, 273, s3804_positive_checked⟩

def s3805_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3805_plain_checked : check 265 s3805_plain_contract = true := by decide +kernel
def s3805_plain : CertifiedContract :=
  ⟨3805, 3806, 0, (.inc 5), s3805_plain_contract, 265, s3805_plain_checked⟩

def s3806_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3806_zero_checked : check 291 s3806_zero_contract = true := by decide +kernel
def s3806_zero : CertifiedContract :=
  ⟨3806, 3808, 0, .none, s3806_zero_contract, 291, s3806_zero_checked⟩

def s3806_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3806_positive_checked : check 297 s3806_positive_contract = true := by decide +kernel
def s3806_positive : CertifiedContract :=
  ⟨3806, 3807, 1, (.dec 8), s3806_positive_contract, 297, s3806_positive_checked⟩

def s3807_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s3807_plain_checked : check 74 s3807_plain_contract = true := by decide +kernel
def s3807_plain : CertifiedContract :=
  ⟨3807, 3811, 0, .none, s3807_plain_contract, 74, s3807_plain_checked⟩

def s3808_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s3808_zero_checked : check 303 s3808_zero_contract = true := by decide +kernel
def s3808_zero : CertifiedContract :=
  ⟨3808, 3811, 0, .none, s3808_zero_contract, 303, s3808_zero_checked⟩

def s3808_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3808_positive_checked : check 306 s3808_positive_contract = true := by decide +kernel
def s3808_positive : CertifiedContract :=
  ⟨3808, 3809, 1, (.dec 5), s3808_positive_contract, 306, s3808_positive_checked⟩

def s3809_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3809_plain_checked : check 310 s3809_plain_contract = true := by decide +kernel
def s3809_plain : CertifiedContract :=
  ⟨3809, 3810, 0, (.inc 8), s3809_plain_contract, 310, s3809_plain_checked⟩

def s3810_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3810_plain_checked : check 77 s3810_plain_contract = true := by decide +kernel
def s3810_plain : CertifiedContract :=
  ⟨3810, 3808, 0, .none, s3810_plain_contract, 77, s3810_plain_checked⟩

def s3811_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, true], rootFrame [true, false, true, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s3811_plain_checked : check 68 s3811_plain_contract = true := by decide +kernel
def s3811_plain : CertifiedContract :=
  ⟨3811, 3804, 0, .none, s3811_plain_contract, 68, s3811_plain_checked⟩

def s3812_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, true, false, false, false, false, true, false], rootFrame [true, false, true, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s3812_zero_checked : check 267 s3812_zero_contract = true := by decide +kernel
def s3812_zero : CertifiedContract :=
  ⟨3812, 3815, 0, .none, s3812_zero_contract, 267, s3812_zero_checked⟩

def s3812_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, true, false, false, false, false, true, false], rootFrame [true, false, true, false, true, false, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s3812_positive_checked : check 270 s3812_positive_contract = true := by decide +kernel
def s3812_positive : CertifiedContract :=
  ⟨3812, 3813, 1, (.dec 5), s3812_positive_contract, 270, s3812_positive_checked⟩

def s3813_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, false, true, true, false], rootFrame [true, false, true, false, true, false, false, false, false, true, true, true] 0 (.inc 1)⟩
theorem s3813_plain_checked : check 283 s3813_plain_contract = true := by decide +kernel
def s3813_plain : CertifiedContract :=
  ⟨3813, 3814, 0, (.inc 1), s3813_plain_contract, 283, s3813_plain_checked⟩

def s3814_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, true, false, false, false, false, true, false] 0 .none⟩
theorem s3814_plain_checked : check 71 s3814_plain_contract = true := by decide +kernel
def s3814_plain : CertifiedContract :=
  ⟨3814, 3812, 0, .none, s3814_plain_contract, 71, s3814_plain_checked⟩

def s3815_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s3815_zero_checked : check 255 s3815_zero_contract = true := by decide +kernel
def s3815_zero : CertifiedContract :=
  ⟨3815, 3818, 0, .none, s3815_zero_contract, 255, s3815_zero_checked⟩

def s3815_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, true, false, false, false, true, false, true, false] 1 (.dec 8)⟩
theorem s3815_positive_checked : check 261 s3815_positive_contract = true := by decide +kernel
def s3815_positive : CertifiedContract :=
  ⟨3815, 3816, 1, (.dec 8), s3815_positive_contract, 261, s3815_positive_checked⟩

def s3816_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, true, false, false, false, true, false, true, true] 0 (.inc 3)⟩
theorem s3816_plain_checked : check 277 s3816_plain_contract = true := by decide +kernel
def s3816_plain : CertifiedContract :=
  ⟨3816, 3817, 0, (.inc 3), s3816_plain_contract, 277, s3816_plain_checked⟩

def s3817_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, false, true, true], rootFrame [true, false, true, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s3817_plain_checked : check 65 s3817_plain_contract = true := by decide +kernel
def s3817_plain : CertifiedContract :=
  ⟨3817, 3815, 0, .none, s3817_plain_contract, 65, s3817_plain_checked⟩

def s3818_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, false, false] 0 .none⟩
theorem s3818_zero_checked : check 273 s3818_zero_contract = true := by decide +kernel
def s3818_zero : CertifiedContract :=
  ⟨3818, 3821, 0, .none, s3818_zero_contract, 273, s3818_zero_checked⟩

def s3818_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3818_positive_checked : check 279 s3818_positive_contract = true := by decide +kernel
def s3818_positive : CertifiedContract :=
  ⟨3818, 3819, 1, (.dec 2), s3818_positive_contract, 279, s3818_positive_checked⟩

def s3819_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, false, true, true] 0 (.inc 8)⟩
theorem s3819_plain_checked : check 292 s3819_plain_contract = true := by decide +kernel
def s3819_plain : CertifiedContract :=
  ⟨3819, 3820, 0, (.inc 8), s3819_plain_contract, 292, s3819_plain_checked⟩

def s3820_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, false, true, true], rootFrame [true, false, true, false, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s3820_plain_checked : check 71 s3820_plain_contract = true := by decide +kernel
def s3820_plain : CertifiedContract :=
  ⟨3820, 3818, 0, .none, s3820_plain_contract, 71, s3820_plain_checked⟩

def s3821_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, false, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s3821_zero_checked : check 294 s3821_zero_contract = true := by decide +kernel
def s3821_zero : CertifiedContract :=
  ⟨3821, 3824, 0, .none, s3821_zero_contract, 294, s3821_zero_checked⟩

def s3821_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, false, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s3821_positive_checked : check 300 s3821_positive_contract = true := by decide +kernel
def s3821_positive : CertifiedContract :=
  ⟨3821, 3822, 1, (.dec 0), s3821_positive_contract, 300, s3821_positive_checked⟩

def s3822_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, false, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s3822_plain_checked : check 292 s3822_plain_contract = true := by decide +kernel
def s3822_plain : CertifiedContract :=
  ⟨3822, 3823, 0, (.inc 2), s3822_plain_contract, 292, s3822_plain_checked⟩

def s3823_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, false, true, true], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, false, false] 0 .none⟩
theorem s3823_plain_checked : check 74 s3823_plain_contract = true := by decide +kernel
def s3823_plain : CertifiedContract :=
  ⟨3823, 3821, 0, .none, s3823_plain_contract, 74, s3823_plain_checked⟩

def s3824_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3824_zero_checked : check 300 s3824_zero_contract = true := by decide +kernel
def s3824_zero : CertifiedContract :=
  ⟨3824, 3828, 0, .none, s3824_zero_contract, 300, s3824_zero_checked⟩

def s3824_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3824_positive_checked : check 306 s3824_positive_contract = true := by decide +kernel
def s3824_positive : CertifiedContract :=
  ⟨3824, 3825, 1, (.dec 2), s3824_positive_contract, 306, s3824_positive_checked⟩

def s3825_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3825_plain_checked : check 319 s3825_plain_contract = true := by decide +kernel
def s3825_plain : CertifiedContract :=
  ⟨3825, 3826, 0, (.inc 5), s3825_plain_contract, 319, s3825_plain_checked⟩

def s3826_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3826_plain_checked : check 346 s3826_plain_contract = true := by decide +kernel
def s3826_plain : CertifiedContract :=
  ⟨3826, 3827, 0, (.inc 8), s3826_plain_contract, 346, s3826_plain_checked⟩

def s3827_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s3827_plain_checked : check 89 s3827_plain_contract = true := by decide +kernel
def s3827_plain : CertifiedContract :=
  ⟨3827, 3824, 0, .none, s3827_plain_contract, 89, s3827_plain_checked⟩

def s3828_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s3828_zero_checked : check 321 s3828_zero_contract = true := by decide +kernel
def s3828_zero : CertifiedContract :=
  ⟨3828, 3834, 0, .none, s3828_zero_contract, 321, s3828_zero_checked⟩

def s3828_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3828_positive_checked : check 324 s3828_positive_contract = true := by decide +kernel
def s3828_positive : CertifiedContract :=
  ⟨3828, 3829, 1, (.dec 8), s3828_positive_contract, 324, s3828_positive_checked⟩

def s3829_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3829_plain_checked : check 319 s3829_plain_contract = true := by decide +kernel
def s3829_plain : CertifiedContract :=
  ⟨3829, 3830, 0, (.inc 5), s3829_plain_contract, 319, s3829_plain_checked⟩

def s3830_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s3830_zero_checked : check 339 s3830_zero_contract = true := by decide +kernel
def s3830_zero : CertifiedContract :=
  ⟨3830, 3833, 0, .none, s3830_zero_contract, 339, s3830_zero_checked⟩

def s3830_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3830_positive_checked : check 342 s3830_positive_contract = true := by decide +kernel
def s3830_positive : CertifiedContract :=
  ⟨3830, 3831, 1, (.dec 8), s3830_positive_contract, 342, s3830_positive_checked⟩

def s3831_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3831_plain_checked : check 337 s3831_plain_contract = true := by decide +kernel
def s3831_plain : CertifiedContract :=
  ⟨3831, 3832, 0, (.inc 2), s3831_plain_contract, 337, s3831_plain_checked⟩

def s3832_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3832_plain_checked : check 89 s3832_plain_contract = true := by decide +kernel
def s3832_plain : CertifiedContract :=
  ⟨3832, 3830, 0, .none, s3832_plain_contract, 89, s3832_plain_checked⟩

def s3833_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s3833_plain_checked : check 92 s3833_plain_contract = true := by decide +kernel
def s3833_plain : CertifiedContract :=
  ⟨3833, 3824, 0, .none, s3833_plain_contract, 92, s3833_plain_checked⟩

def s3834_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, true, false, false] 0 .none⟩
theorem s3834_zero_checked : check 309 s3834_zero_contract = true := by decide +kernel
def s3834_zero : CertifiedContract :=
  ⟨3834, 3837, 0, .none, s3834_zero_contract, 309, s3834_zero_checked⟩

def s3834_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s3834_positive_checked : check 306 s3834_positive_contract = true := by decide +kernel
def s3834_positive : CertifiedContract :=
  ⟨3834, 3835, 1, (.dec 5), s3834_positive_contract, 306, s3834_positive_checked⟩

def s3835_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s3835_plain_checked : check 319 s3835_plain_contract = true := by decide +kernel
def s3835_plain : CertifiedContract :=
  ⟨3835, 3836, 0, (.inc 0), s3835_plain_contract, 319, s3835_plain_checked⟩

def s3836_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s3836_plain_checked : check 80 s3836_plain_contract = true := by decide +kernel
def s3836_plain : CertifiedContract :=
  ⟨3836, 3834, 0, .none, s3836_plain_contract, 80, s3836_plain_checked⟩

def s3837_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, true, false, false, false, true, true, true, false, false], rootFrame [true, false, true, false, true, false, false, false, true, true, true, true, false] 0 .none⟩
theorem s3837_zero_checked : check 273 s3837_zero_contract = true := by decide +kernel
def s3837_zero : CertifiedContract :=
  ⟨3837, 3841, 0, .none, s3837_zero_contract, 273, s3837_zero_checked⟩

def s3837_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, true, false, false, false, true, true, true, false, false], rootFrame [true, false, true, false, true, false, false, false, true, true, true, false, true, false] 1 (.dec 3)⟩
theorem s3837_positive_checked : check 279 s3837_positive_contract = true := by decide +kernel
def s3837_positive : CertifiedContract :=
  ⟨3837, 3838, 1, (.dec 3), s3837_positive_contract, 279, s3837_positive_checked⟩

def s3838_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s3838_plain_checked : check 292 s3838_plain_contract = true := by decide +kernel
def s3838_plain : CertifiedContract :=
  ⟨3838, 3839, 0, (.inc 2), s3838_plain_contract, 292, s3838_plain_checked⟩

def s3839_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3839_plain_checked : check 319 s3839_plain_contract = true := by decide +kernel
def s3839_plain : CertifiedContract :=
  ⟨3839, 3840, 0, (.inc 8), s3839_plain_contract, 319, s3839_plain_checked⟩

def s3840_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, true, false, true, true, true], rootFrame [true, false, true, false, true, false, false, false, true, true, true, false, false] 0 .none⟩
theorem s3840_plain_checked : check 80 s3840_plain_contract = true := by decide +kernel
def s3840_plain : CertifiedContract :=
  ⟨3840, 3837, 0, .none, s3840_plain_contract, 80, s3840_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S077
