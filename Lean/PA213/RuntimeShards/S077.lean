import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S077
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s3793_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, false] 0 .none⟩
theorem s3793_plain_checked : check 97 s3793_plain_contract = true := by decide +kernel
def s3793_plain : CertifiedContract :=
  ⟨3793, 3791, 0, .none, s3793_plain_contract, 97, s3793_plain_checked⟩

def s3794_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, false, false] 0 .none⟩
theorem s3794_plain_checked : check 111 s3794_plain_contract = true := by decide +kernel
def s3794_plain : CertifiedContract :=
  ⟨3794, 3796, 0, .none, s3794_plain_contract, 111, s3794_plain_checked⟩

def s3795_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, true, false] 0 .none⟩
theorem s3795_zero_checked : check 338 s3795_zero_contract = true := by decide +kernel
def s3795_zero : CertifiedContract :=
  ⟨3795, 3801, 0, .none, s3795_zero_contract, 338, s3795_zero_checked⟩

def s3795_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, false, false] 1 (.dec 8)⟩
theorem s3795_positive_checked : check 344 s3795_positive_contract = true := by decide +kernel
def s3795_positive : CertifiedContract :=
  ⟨3795, 3796, 1, (.dec 8), s3795_positive_contract, 344, s3795_positive_checked⟩

def s3796_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, false, false] 0 .none⟩
theorem s3796_zero_checked : check 353 s3796_zero_contract = true := by decide +kernel
def s3796_zero : CertifiedContract :=
  ⟨3796, 3798, 0, .none, s3796_zero_contract, 353, s3796_zero_checked⟩

def s3796_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, false, true] 1 (.dec 7)⟩
theorem s3796_positive_checked : check 359 s3796_positive_contract = true := by decide +kernel
def s3796_positive : CertifiedContract :=
  ⟨3796, 3797, 1, (.dec 7), s3796_positive_contract, 359, s3796_positive_checked⟩

def s3797_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, false, false] 0 .none⟩
theorem s3797_plain_checked : check 91 s3797_plain_contract = true := by decide +kernel
def s3797_plain : CertifiedContract :=
  ⟨3797, 3796, 0, .none, s3797_plain_contract, 91, s3797_plain_checked⟩

def s3798_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true] 0 .none⟩
theorem s3798_zero_checked : check 353 s3798_zero_contract = true := by decide +kernel
def s3798_zero : CertifiedContract :=
  ⟨3798, 3800, 0, .none, s3798_zero_contract, 353, s3798_zero_checked⟩

def s3798_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, false, true] 1 (.dec 8)⟩
theorem s3798_positive_checked : check 359 s3798_positive_contract = true := by decide +kernel
def s3798_positive : CertifiedContract :=
  ⟨3798, 3799, 1, (.dec 8), s3798_positive_contract, 359, s3798_positive_checked⟩

def s3799_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, false, false] 0 .none⟩
theorem s3799_plain_checked : check 94 s3799_plain_contract = true := by decide +kernel
def s3799_plain : CertifiedContract :=
  ⟨3799, 3796, 0, .none, s3799_plain_contract, 94, s3799_plain_checked⟩

def s3800_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, true] 0 .none⟩
theorem s3800_plain_checked : check 132 s3800_plain_contract = true := by decide +kernel
def s3800_plain : CertifiedContract :=
  ⟨3800, 3803, 0, .none, s3800_plain_contract, 132, s3800_plain_checked⟩

def s3801_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, true] 0 .none⟩
theorem s3801_zero_checked : check 359 s3801_zero_contract = true := by decide +kernel
def s3801_zero : CertifiedContract :=
  ⟨3801, 3803, 0, .none, s3801_zero_contract, 359, s3801_zero_checked⟩

def s3801_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, true, true] 1 (.dec 2)⟩
theorem s3801_positive_checked : check 341 s3801_positive_contract = true := by decide +kernel
def s3801_positive : CertifiedContract :=
  ⟨3801, 3802, 1, (.dec 2), s3801_positive_contract, 341, s3801_positive_checked⟩

def s3802_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, true, false] 0 .none⟩
theorem s3802_plain_checked : check 85 s3802_plain_contract = true := by decide +kernel
def s3802_plain : CertifiedContract :=
  ⟨3802, 3801, 0, .none, s3802_plain_contract, 85, s3802_plain_checked⟩

def s3803_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, true] 0 .none⟩
theorem s3803_plain_checked : check 84 s3803_plain_contract = true := by decide +kernel
def s3803_plain : CertifiedContract :=
  ⟨3803, 3910, 0, .none, s3803_plain_contract, 84, s3803_plain_checked⟩

def s3804_zero_contract : Contract :=
  ⟨(some (1, true)), rootFrame [true, false, true, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, true, false, false, false, false, true, false] 0 .none⟩
theorem s3804_zero_checked : check 266 s3804_zero_contract = true := by decide +kernel
def s3804_zero : CertifiedContract :=
  ⟨3804, 3812, 0, .none, s3804_zero_contract, 266, s3804_zero_checked⟩

def s3804_positive_contract : Contract :=
  ⟨(some (1, false)), rootFrame [true, false, true, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, true, false, false, false, false, false, true, false] 1 (.dec 1)⟩
theorem s3804_positive_checked : check 272 s3804_positive_contract = true := by decide +kernel
def s3804_positive : CertifiedContract :=
  ⟨3804, 3805, 1, (.dec 1), s3804_positive_contract, 272, s3804_positive_checked⟩

def s3805_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3805_plain_checked : check 264 s3805_plain_contract = true := by decide +kernel
def s3805_plain : CertifiedContract :=
  ⟨3805, 3806, 0, (.inc 5), s3805_plain_contract, 264, s3805_plain_checked⟩

def s3806_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3806_zero_checked : check 290 s3806_zero_contract = true := by decide +kernel
def s3806_zero : CertifiedContract :=
  ⟨3806, 3808, 0, .none, s3806_zero_contract, 290, s3806_zero_checked⟩

def s3806_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3806_positive_checked : check 296 s3806_positive_contract = true := by decide +kernel
def s3806_positive : CertifiedContract :=
  ⟨3806, 3807, 1, (.dec 8), s3806_positive_contract, 296, s3806_positive_checked⟩

def s3807_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s3807_plain_checked : check 73 s3807_plain_contract = true := by decide +kernel
def s3807_plain : CertifiedContract :=
  ⟨3807, 3811, 0, .none, s3807_plain_contract, 73, s3807_plain_checked⟩

def s3808_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s3808_zero_checked : check 302 s3808_zero_contract = true := by decide +kernel
def s3808_zero : CertifiedContract :=
  ⟨3808, 3811, 0, .none, s3808_zero_contract, 302, s3808_zero_checked⟩

def s3808_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3808_positive_checked : check 305 s3808_positive_contract = true := by decide +kernel
def s3808_positive : CertifiedContract :=
  ⟨3808, 3809, 1, (.dec 5), s3808_positive_contract, 305, s3808_positive_checked⟩

def s3809_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3809_plain_checked : check 309 s3809_plain_contract = true := by decide +kernel
def s3809_plain : CertifiedContract :=
  ⟨3809, 3810, 0, (.inc 8), s3809_plain_contract, 309, s3809_plain_checked⟩

def s3810_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3810_plain_checked : check 76 s3810_plain_contract = true := by decide +kernel
def s3810_plain : CertifiedContract :=
  ⟨3810, 3808, 0, .none, s3810_plain_contract, 76, s3810_plain_checked⟩

def s3811_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, false, false, true, true, true], rootFrame [true, false, true, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s3811_plain_checked : check 67 s3811_plain_contract = true := by decide +kernel
def s3811_plain : CertifiedContract :=
  ⟨3811, 3804, 0, .none, s3811_plain_contract, 67, s3811_plain_checked⟩

def s3812_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, true, false, false, false, false, true, false], rootFrame [true, false, true, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s3812_zero_checked : check 266 s3812_zero_contract = true := by decide +kernel
def s3812_zero : CertifiedContract :=
  ⟨3812, 3815, 0, .none, s3812_zero_contract, 266, s3812_zero_checked⟩

def s3812_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, true, false, false, false, false, true, false], rootFrame [true, false, true, false, true, false, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s3812_positive_checked : check 269 s3812_positive_contract = true := by decide +kernel
def s3812_positive : CertifiedContract :=
  ⟨3812, 3813, 1, (.dec 5), s3812_positive_contract, 269, s3812_positive_checked⟩

def s3813_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, false, true, true, false], rootFrame [true, false, true, false, true, false, false, false, false, true, true, true] 0 (.inc 1)⟩
theorem s3813_plain_checked : check 282 s3813_plain_contract = true := by decide +kernel
def s3813_plain : CertifiedContract :=
  ⟨3813, 3814, 0, (.inc 1), s3813_plain_contract, 282, s3813_plain_checked⟩

def s3814_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, true, false, false, false, false, true, false] 0 .none⟩
theorem s3814_plain_checked : check 70 s3814_plain_contract = true := by decide +kernel
def s3814_plain : CertifiedContract :=
  ⟨3814, 3812, 0, .none, s3814_plain_contract, 70, s3814_plain_checked⟩

def s3815_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s3815_zero_checked : check 254 s3815_zero_contract = true := by decide +kernel
def s3815_zero : CertifiedContract :=
  ⟨3815, 3818, 0, .none, s3815_zero_contract, 254, s3815_zero_checked⟩

def s3815_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, true, false, false, false, true, false, true, false] 1 (.dec 8)⟩
theorem s3815_positive_checked : check 260 s3815_positive_contract = true := by decide +kernel
def s3815_positive : CertifiedContract :=
  ⟨3815, 3816, 1, (.dec 8), s3815_positive_contract, 260, s3815_positive_checked⟩

def s3816_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, true, false, false, false, true, false, true, true] 0 (.inc 3)⟩
theorem s3816_plain_checked : check 276 s3816_plain_contract = true := by decide +kernel
def s3816_plain : CertifiedContract :=
  ⟨3816, 3817, 0, (.inc 3), s3816_plain_contract, 276, s3816_plain_checked⟩

def s3817_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, false, true, true], rootFrame [true, false, true, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s3817_plain_checked : check 64 s3817_plain_contract = true := by decide +kernel
def s3817_plain : CertifiedContract :=
  ⟨3817, 3815, 0, .none, s3817_plain_contract, 64, s3817_plain_checked⟩

def s3818_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, false, false] 0 .none⟩
theorem s3818_zero_checked : check 272 s3818_zero_contract = true := by decide +kernel
def s3818_zero : CertifiedContract :=
  ⟨3818, 3821, 0, .none, s3818_zero_contract, 272, s3818_zero_checked⟩

def s3818_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3818_positive_checked : check 278 s3818_positive_contract = true := by decide +kernel
def s3818_positive : CertifiedContract :=
  ⟨3818, 3819, 1, (.dec 2), s3818_positive_contract, 278, s3818_positive_checked⟩

def s3819_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, false, true, true] 0 (.inc 8)⟩
theorem s3819_plain_checked : check 291 s3819_plain_contract = true := by decide +kernel
def s3819_plain : CertifiedContract :=
  ⟨3819, 3820, 0, (.inc 8), s3819_plain_contract, 291, s3819_plain_checked⟩

def s3820_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, false, true, true], rootFrame [true, false, true, false, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s3820_plain_checked : check 70 s3820_plain_contract = true := by decide +kernel
def s3820_plain : CertifiedContract :=
  ⟨3820, 3818, 0, .none, s3820_plain_contract, 70, s3820_plain_checked⟩

def s3821_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, false, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s3821_zero_checked : check 293 s3821_zero_contract = true := by decide +kernel
def s3821_zero : CertifiedContract :=
  ⟨3821, 3824, 0, .none, s3821_zero_contract, 293, s3821_zero_checked⟩

def s3821_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, false, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s3821_positive_checked : check 299 s3821_positive_contract = true := by decide +kernel
def s3821_positive : CertifiedContract :=
  ⟨3821, 3822, 1, (.dec 0), s3821_positive_contract, 299, s3821_positive_checked⟩

def s3822_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, false, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s3822_plain_checked : check 291 s3822_plain_contract = true := by decide +kernel
def s3822_plain : CertifiedContract :=
  ⟨3822, 3823, 0, (.inc 2), s3822_plain_contract, 291, s3822_plain_checked⟩

def s3823_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, false, true, true], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, false, false] 0 .none⟩
theorem s3823_plain_checked : check 73 s3823_plain_contract = true := by decide +kernel
def s3823_plain : CertifiedContract :=
  ⟨3823, 3821, 0, .none, s3823_plain_contract, 73, s3823_plain_checked⟩

def s3824_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3824_zero_checked : check 299 s3824_zero_contract = true := by decide +kernel
def s3824_zero : CertifiedContract :=
  ⟨3824, 3828, 0, .none, s3824_zero_contract, 299, s3824_zero_checked⟩

def s3824_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3824_positive_checked : check 305 s3824_positive_contract = true := by decide +kernel
def s3824_positive : CertifiedContract :=
  ⟨3824, 3825, 1, (.dec 2), s3824_positive_contract, 305, s3824_positive_checked⟩

def s3825_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3825_plain_checked : check 318 s3825_plain_contract = true := by decide +kernel
def s3825_plain : CertifiedContract :=
  ⟨3825, 3826, 0, (.inc 5), s3825_plain_contract, 318, s3825_plain_checked⟩

def s3826_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3826_plain_checked : check 345 s3826_plain_contract = true := by decide +kernel
def s3826_plain : CertifiedContract :=
  ⟨3826, 3827, 0, (.inc 8), s3826_plain_contract, 345, s3826_plain_checked⟩

def s3827_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s3827_plain_checked : check 88 s3827_plain_contract = true := by decide +kernel
def s3827_plain : CertifiedContract :=
  ⟨3827, 3824, 0, .none, s3827_plain_contract, 88, s3827_plain_checked⟩

def s3828_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s3828_zero_checked : check 320 s3828_zero_contract = true := by decide +kernel
def s3828_zero : CertifiedContract :=
  ⟨3828, 3834, 0, .none, s3828_zero_contract, 320, s3828_zero_checked⟩

def s3828_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3828_positive_checked : check 323 s3828_positive_contract = true := by decide +kernel
def s3828_positive : CertifiedContract :=
  ⟨3828, 3829, 1, (.dec 8), s3828_positive_contract, 323, s3828_positive_checked⟩

def s3829_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3829_plain_checked : check 318 s3829_plain_contract = true := by decide +kernel
def s3829_plain : CertifiedContract :=
  ⟨3829, 3830, 0, (.inc 5), s3829_plain_contract, 318, s3829_plain_checked⟩

def s3830_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s3830_zero_checked : check 338 s3830_zero_contract = true := by decide +kernel
def s3830_zero : CertifiedContract :=
  ⟨3830, 3833, 0, .none, s3830_zero_contract, 338, s3830_zero_checked⟩

def s3830_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3830_positive_checked : check 341 s3830_positive_contract = true := by decide +kernel
def s3830_positive : CertifiedContract :=
  ⟨3830, 3831, 1, (.dec 8), s3830_positive_contract, 341, s3830_positive_checked⟩

def s3831_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3831_plain_checked : check 336 s3831_plain_contract = true := by decide +kernel
def s3831_plain : CertifiedContract :=
  ⟨3831, 3832, 0, (.inc 2), s3831_plain_contract, 336, s3831_plain_checked⟩

def s3832_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3832_plain_checked : check 88 s3832_plain_contract = true := by decide +kernel
def s3832_plain : CertifiedContract :=
  ⟨3832, 3830, 0, .none, s3832_plain_contract, 88, s3832_plain_checked⟩

def s3833_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s3833_plain_checked : check 91 s3833_plain_contract = true := by decide +kernel
def s3833_plain : CertifiedContract :=
  ⟨3833, 3824, 0, .none, s3833_plain_contract, 91, s3833_plain_checked⟩

def s3834_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, true, false, false] 0 .none⟩
theorem s3834_zero_checked : check 308 s3834_zero_contract = true := by decide +kernel
def s3834_zero : CertifiedContract :=
  ⟨3834, 3837, 0, .none, s3834_zero_contract, 308, s3834_zero_checked⟩

def s3834_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s3834_positive_checked : check 305 s3834_positive_contract = true := by decide +kernel
def s3834_positive : CertifiedContract :=
  ⟨3834, 3835, 1, (.dec 5), s3834_positive_contract, 305, s3834_positive_checked⟩

def s3835_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s3835_plain_checked : check 318 s3835_plain_contract = true := by decide +kernel
def s3835_plain : CertifiedContract :=
  ⟨3835, 3836, 0, (.inc 0), s3835_plain_contract, 318, s3835_plain_checked⟩

def s3836_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, true, false, false, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s3836_plain_checked : check 79 s3836_plain_contract = true := by decide +kernel
def s3836_plain : CertifiedContract :=
  ⟨3836, 3834, 0, .none, s3836_plain_contract, 79, s3836_plain_checked⟩

def s3837_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, true, false, false, false, true, true, true, false, false], rootFrame [true, false, true, false, true, false, false, false, true, true, true, true, false] 0 .none⟩
theorem s3837_zero_checked : check 272 s3837_zero_contract = true := by decide +kernel
def s3837_zero : CertifiedContract :=
  ⟨3837, 3841, 0, .none, s3837_zero_contract, 272, s3837_zero_checked⟩

def s3837_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, true, false, false, false, true, true, true, false, false], rootFrame [true, false, true, false, true, false, false, false, true, true, true, false, true, false] 1 (.dec 3)⟩
theorem s3837_positive_checked : check 278 s3837_positive_contract = true := by decide +kernel
def s3837_positive : CertifiedContract :=
  ⟨3837, 3838, 1, (.dec 3), s3837_positive_contract, 278, s3837_positive_checked⟩

def s3838_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s3838_plain_checked : check 291 s3838_plain_contract = true := by decide +kernel
def s3838_plain : CertifiedContract :=
  ⟨3838, 3839, 0, (.inc 2), s3838_plain_contract, 291, s3838_plain_checked⟩

def s3839_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, true, false, false, false, true, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3839_plain_checked : check 318 s3839_plain_contract = true := by decide +kernel
def s3839_plain : CertifiedContract :=
  ⟨3839, 3840, 0, (.inc 8), s3839_plain_contract, 318, s3839_plain_checked⟩

def s3840_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, true, false, false, false, true, true, true, false, true, true, true], rootFrame [true, false, true, false, true, false, false, false, true, true, true, false, false] 0 .none⟩
theorem s3840_plain_checked : check 79 s3840_plain_contract = true := by decide +kernel
def s3840_plain : CertifiedContract :=
  ⟨3840, 3837, 0, .none, s3840_plain_contract, 79, s3840_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s3793_plain,
  s3794_plain,
  s3795_zero,
  s3795_positive,
  s3796_zero,
  s3796_positive,
  s3797_plain,
  s3798_zero,
  s3798_positive,
  s3799_plain,
  s3800_plain,
  s3801_zero,
  s3801_positive,
  s3802_plain,
  s3803_plain,
  s3804_zero,
  s3804_positive,
  s3805_plain,
  s3806_zero,
  s3806_positive,
  s3807_plain,
  s3808_zero,
  s3808_positive,
  s3809_plain,
  s3810_plain,
  s3811_plain,
  s3812_zero,
  s3812_positive,
  s3813_plain,
  s3814_plain,
  s3815_zero,
  s3815_positive,
  s3816_plain,
  s3817_plain,
  s3818_zero,
  s3818_positive,
  s3819_plain,
  s3820_plain,
  s3821_zero,
  s3821_positive,
  s3822_plain,
  s3823_plain,
  s3824_zero,
  s3824_positive,
  s3825_plain,
  s3826_plain,
  s3827_plain,
  s3828_zero,
  s3828_positive,
  s3829_plain,
  s3830_zero,
  s3830_positive,
  s3831_plain,
  s3832_plain,
  s3833_plain,
  s3834_zero,
  s3834_positive,
  s3835_plain,
  s3836_plain,
  s3837_zero,
  s3837_positive,
  s3838_plain,
  s3839_plain,
  s3840_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S077
