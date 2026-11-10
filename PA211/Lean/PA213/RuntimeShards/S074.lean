import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S074
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s3647_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s3647_zero_checked : check 356 s3647_zero_contract = true := by decide +kernel
def s3647_zero : CertifiedContract :=
  ⟨3647, 3650, 0, .none, s3647_zero_contract, 356, s3647_zero_checked⟩

def s3647_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s3647_positive_checked : check 359 s3647_positive_contract = true := by decide +kernel
def s3647_positive : CertifiedContract :=
  ⟨3647, 3648, 1, (.dec 5), s3647_positive_contract, 359, s3647_positive_checked⟩

def s3648_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s3648_plain_checked : check 372 s3648_plain_contract = true := by decide +kernel
def s3648_plain : CertifiedContract :=
  ⟨3648, 3649, 0, (.inc 0), s3648_plain_contract, 372, s3648_plain_checked⟩

def s3649_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, true, false] 0 .none⟩
theorem s3649_plain_checked : check 97 s3649_plain_contract = true := by decide +kernel
def s3649_plain : CertifiedContract :=
  ⟨3649, 3647, 0, .none, s3649_plain_contract, 97, s3649_plain_checked⟩

def s3650_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, true, false] 0 .none⟩
theorem s3650_zero_checked : check 353 s3650_zero_contract = true := by decide +kernel
def s3650_zero : CertifiedContract :=
  ⟨3650, 3654, 0, .none, s3650_zero_contract, 353, s3650_zero_checked⟩

def s3650_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3650_positive_checked : check 359 s3650_positive_contract = true := by decide +kernel
def s3650_positive : CertifiedContract :=
  ⟨3650, 3651, 1, (.dec 2), s3650_positive_contract, 359, s3650_positive_checked⟩

def s3651_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3651_plain_checked : check 372 s3651_plain_contract = true := by decide +kernel
def s3651_plain : CertifiedContract :=
  ⟨3651, 3652, 0, (.inc 5), s3651_plain_contract, 372, s3651_plain_checked⟩

def s3652_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3652_plain_checked : check 399 s3652_plain_contract = true := by decide +kernel
def s3652_plain : CertifiedContract :=
  ⟨3652, 3653, 0, (.inc 8), s3652_plain_contract, 399, s3652_plain_checked⟩

def s3653_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s3653_plain_checked : check 106 s3653_plain_contract = true := by decide +kernel
def s3653_plain : CertifiedContract :=
  ⟨3653, 3650, 0, .none, s3653_plain_contract, 106, s3653_plain_checked⟩

def s3654_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s3654_zero_checked : check 374 s3654_zero_contract = true := by decide +kernel
def s3654_zero : CertifiedContract :=
  ⟨3654, 3660, 0, .none, s3654_zero_contract, 374, s3654_zero_checked⟩

def s3654_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3654_positive_checked : check 377 s3654_positive_contract = true := by decide +kernel
def s3654_positive : CertifiedContract :=
  ⟨3654, 3655, 1, (.dec 8), s3654_positive_contract, 377, s3654_positive_checked⟩

def s3655_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3655_plain_checked : check 372 s3655_plain_contract = true := by decide +kernel
def s3655_plain : CertifiedContract :=
  ⟨3655, 3656, 0, (.inc 5), s3655_plain_contract, 372, s3655_plain_checked⟩

def s3656_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, true, true, true] 0 .none⟩
theorem s3656_zero_checked : check 392 s3656_zero_contract = true := by decide +kernel
def s3656_zero : CertifiedContract :=
  ⟨3656, 3659, 0, .none, s3656_zero_contract, 392, s3656_zero_checked⟩

def s3656_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3656_positive_checked : check 395 s3656_positive_contract = true := by decide +kernel
def s3656_positive : CertifiedContract :=
  ⟨3656, 3657, 1, (.dec 8), s3656_positive_contract, 395, s3656_positive_checked⟩

def s3657_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3657_plain_checked : check 390 s3657_plain_contract = true := by decide +kernel
def s3657_plain : CertifiedContract :=
  ⟨3657, 3658, 0, (.inc 2), s3657_plain_contract, 390, s3657_plain_checked⟩

def s3658_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3658_plain_checked : check 106 s3658_plain_contract = true := by decide +kernel
def s3658_plain : CertifiedContract :=
  ⟨3658, 3656, 0, .none, s3658_plain_contract, 106, s3658_plain_checked⟩

def s3659_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s3659_plain_checked : check 109 s3659_plain_contract = true := by decide +kernel
def s3659_plain : CertifiedContract :=
  ⟨3659, 3650, 0, .none, s3659_plain_contract, 109, s3659_plain_checked⟩

def s3660_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, false] 0 .none⟩
theorem s3660_zero_checked : check 359 s3660_zero_contract = true := by decide +kernel
def s3660_zero : CertifiedContract :=
  ⟨3660, 3666, 0, .none, s3660_zero_contract, 359, s3660_zero_checked⟩

def s3660_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3660_positive_checked : check 359 s3660_positive_contract = true := by decide +kernel
def s3660_positive : CertifiedContract :=
  ⟨3660, 3661, 1, (.dec 5), s3660_positive_contract, 359, s3660_positive_checked⟩

def s3661_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3661_plain_checked : check 372 s3661_plain_contract = true := by decide +kernel
def s3661_plain : CertifiedContract :=
  ⟨3661, 3662, 0, (.inc 2), s3661_plain_contract, 372, s3661_plain_checked⟩

def s3662_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3662_plain_checked : check 375 s3662_plain_contract = true := by decide +kernel
def s3662_plain : CertifiedContract :=
  ⟨3662, 3663, 0, (.inc 2), s3662_plain_contract, 375, s3662_plain_checked⟩

def s3663_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3663_plain_checked : check 372 s3663_plain_contract = true := by decide +kernel
def s3663_plain : CertifiedContract :=
  ⟨3663, 3664, 0, (.inc 2), s3663_plain_contract, 372, s3663_plain_checked⟩

def s3664_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s3664_plain_checked : check 378 s3664_plain_contract = true := by decide +kernel
def s3664_plain : CertifiedContract :=
  ⟨3664, 3665, 0, (.inc 2), s3664_plain_contract, 378, s3664_plain_checked⟩

def s3665_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s3665_plain_checked : check 94 s3665_plain_contract = true := by decide +kernel
def s3665_plain : CertifiedContract :=
  ⟨3665, 3660, 0, .none, s3665_plain_contract, 94, s3665_plain_checked⟩

def s3666_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, true, false] 0 .none⟩
theorem s3666_zero_checked : check 365 s3666_zero_contract = true := by decide +kernel
def s3666_zero : CertifiedContract :=
  ⟨3666, 3674, 0, .none, s3666_zero_contract, 365, s3666_zero_checked⟩

def s3666_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s3666_positive_checked : check 371 s3666_positive_contract = true := by decide +kernel
def s3666_positive : CertifiedContract :=
  ⟨3666, 3667, 1, (.dec 0), s3666_positive_contract, 371, s3666_positive_checked⟩

def s3667_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3667_plain_checked : check 381 s3667_plain_contract = true := by decide +kernel
def s3667_plain : CertifiedContract :=
  ⟨3667, 3668, 0, (.inc 5), s3667_plain_contract, 381, s3667_plain_checked⟩

def s3668_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3668_zero_checked : check 407 s3668_zero_contract = true := by decide +kernel
def s3668_zero : CertifiedContract :=
  ⟨3668, 3670, 0, .none, s3668_zero_contract, 407, s3668_zero_checked⟩

def s3668_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3668_positive_checked : check 413 s3668_positive_contract = true := by decide +kernel
def s3668_positive : CertifiedContract :=
  ⟨3668, 3669, 1, (.dec 8), s3668_positive_contract, 413, s3668_positive_checked⟩

def s3669_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s3669_plain_checked : check 112 s3669_plain_contract = true := by decide +kernel
def s3669_plain : CertifiedContract :=
  ⟨3669, 3673, 0, .none, s3669_plain_contract, 112, s3669_plain_checked⟩

def s3670_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s3670_zero_checked : check 419 s3670_zero_contract = true := by decide +kernel
def s3670_zero : CertifiedContract :=
  ⟨3670, 3673, 0, .none, s3670_zero_contract, 419, s3670_zero_checked⟩

def s3670_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3670_positive_checked : check 422 s3670_positive_contract = true := by decide +kernel
def s3670_positive : CertifiedContract :=
  ⟨3670, 3671, 1, (.dec 5), s3670_positive_contract, 422, s3670_positive_checked⟩

def s3671_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3671_plain_checked : check 426 s3671_plain_contract = true := by decide +kernel
def s3671_plain : CertifiedContract :=
  ⟨3671, 3672, 0, (.inc 8), s3671_plain_contract, 426, s3671_plain_checked⟩

def s3672_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3672_plain_checked : check 115 s3672_plain_contract = true := by decide +kernel
def s3672_plain : CertifiedContract :=
  ⟨3672, 3670, 0, .none, s3672_plain_contract, 115, s3672_plain_checked⟩

def s3673_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, false, false] 0 .none⟩
theorem s3673_plain_checked : check 106 s3673_plain_contract = true := by decide +kernel
def s3673_plain : CertifiedContract :=
  ⟨3673, 3666, 0, .none, s3673_plain_contract, 106, s3673_plain_checked⟩

def s3674_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, false, false] 0 .none⟩
theorem s3674_zero_checked : check 365 s3674_zero_contract = true := by decide +kernel
def s3674_zero : CertifiedContract :=
  ⟨3674, 3677, 0, .none, s3674_zero_contract, 365, s3674_zero_checked⟩

def s3674_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s3674_positive_checked : check 368 s3674_positive_contract = true := by decide +kernel
def s3674_positive : CertifiedContract :=
  ⟨3674, 3675, 1, (.dec 5), s3674_positive_contract, 368, s3674_positive_checked⟩

def s3675_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s3675_plain_checked : check 381 s3675_plain_contract = true := by decide +kernel
def s3675_plain : CertifiedContract :=
  ⟨3675, 3676, 0, (.inc 0), s3675_plain_contract, 381, s3675_plain_checked⟩

def s3676_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, false, true, false] 0 .none⟩
theorem s3676_plain_checked : check 100 s3676_plain_contract = true := by decide +kernel
def s3676_plain : CertifiedContract :=
  ⟨3676, 3674, 0, .none, s3676_plain_contract, 100, s3676_plain_checked⟩

def s3677_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, true, false] 0 .none⟩
theorem s3677_zero_checked : check 362 s3677_zero_contract = true := by decide +kernel
def s3677_zero : CertifiedContract :=
  ⟨3677, 3681, 0, .none, s3677_zero_contract, 362, s3677_zero_checked⟩

def s3677_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3677_positive_checked : check 368 s3677_positive_contract = true := by decide +kernel
def s3677_positive : CertifiedContract :=
  ⟨3677, 3678, 1, (.dec 2), s3677_positive_contract, 368, s3677_positive_checked⟩

def s3678_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3678_plain_checked : check 381 s3678_plain_contract = true := by decide +kernel
def s3678_plain : CertifiedContract :=
  ⟨3678, 3679, 0, (.inc 5), s3678_plain_contract, 381, s3678_plain_checked⟩

def s3679_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3679_plain_checked : check 408 s3679_plain_contract = true := by decide +kernel
def s3679_plain : CertifiedContract :=
  ⟨3679, 3680, 0, (.inc 8), s3679_plain_contract, 408, s3679_plain_checked⟩

def s3680_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, false, false] 0 .none⟩
theorem s3680_plain_checked : check 109 s3680_plain_contract = true := by decide +kernel
def s3680_plain : CertifiedContract :=
  ⟨3680, 3677, 0, .none, s3680_plain_contract, 109, s3680_plain_checked⟩

def s3681_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, true, false] 0 .none⟩
theorem s3681_zero_checked : check 383 s3681_zero_contract = true := by decide +kernel
def s3681_zero : CertifiedContract :=
  ⟨3681, 3687, 0, .none, s3681_zero_contract, 383, s3681_zero_checked⟩

def s3681_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3681_positive_checked : check 386 s3681_positive_contract = true := by decide +kernel
def s3681_positive : CertifiedContract :=
  ⟨3681, 3682, 1, (.dec 8), s3681_positive_contract, 386, s3681_positive_checked⟩

def s3682_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3682_plain_checked : check 381 s3682_plain_contract = true := by decide +kernel
def s3682_plain : CertifiedContract :=
  ⟨3682, 3683, 0, (.inc 5), s3682_plain_contract, 381, s3682_plain_checked⟩

def s3683_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s3683_zero_checked : check 401 s3683_zero_contract = true := by decide +kernel
def s3683_zero : CertifiedContract :=
  ⟨3683, 3686, 0, .none, s3683_zero_contract, 401, s3683_zero_checked⟩

def s3683_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3683_positive_checked : check 404 s3683_positive_contract = true := by decide +kernel
def s3683_positive : CertifiedContract :=
  ⟨3683, 3684, 1, (.dec 8), s3683_positive_contract, 404, s3683_positive_checked⟩

def s3684_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3684_plain_checked : check 399 s3684_plain_contract = true := by decide +kernel
def s3684_plain : CertifiedContract :=
  ⟨3684, 3685, 0, (.inc 2), s3684_plain_contract, 399, s3684_plain_checked⟩

def s3685_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3685_plain_checked : check 109 s3685_plain_contract = true := by decide +kernel
def s3685_plain : CertifiedContract :=
  ⟨3685, 3683, 0, .none, s3685_plain_contract, 109, s3685_plain_checked⟩

def s3686_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, false, false, false] 0 .none⟩
theorem s3686_plain_checked : check 112 s3686_plain_contract = true := by decide +kernel
def s3686_plain : CertifiedContract :=
  ⟨3686, 3677, 0, .none, s3686_plain_contract, 112, s3686_plain_checked⟩

def s3687_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, true, false] 0 .none⟩
theorem s3687_zero_checked : check 368 s3687_zero_contract = true := by decide +kernel
def s3687_zero : CertifiedContract :=
  ⟨3687, 3693, 0, .none, s3687_zero_contract, 368, s3687_zero_checked⟩

def s3687_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3687_positive_checked : check 368 s3687_positive_contract = true := by decide +kernel
def s3687_positive : CertifiedContract :=
  ⟨3687, 3688, 1, (.dec 5), s3687_positive_contract, 368, s3687_positive_checked⟩

def s3688_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3688_plain_checked : check 381 s3688_plain_contract = true := by decide +kernel
def s3688_plain : CertifiedContract :=
  ⟨3688, 3689, 0, (.inc 2), s3688_plain_contract, 381, s3688_plain_checked⟩

def s3689_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3689_plain_checked : check 384 s3689_plain_contract = true := by decide +kernel
def s3689_plain : CertifiedContract :=
  ⟨3689, 3690, 0, (.inc 2), s3689_plain_contract, 384, s3689_plain_checked⟩

def s3690_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3690_plain_checked : check 381 s3690_plain_contract = true := by decide +kernel
def s3690_plain : CertifiedContract :=
  ⟨3690, 3691, 0, (.inc 2), s3690_plain_contract, 381, s3690_plain_checked⟩

def s3691_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s3691_plain_checked : check 387 s3691_plain_contract = true := by decide +kernel
def s3691_plain : CertifiedContract :=
  ⟨3691, 3692, 0, (.inc 2), s3691_plain_contract, 387, s3691_plain_checked⟩

def s3692_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, false, true, true, false] 0 .none⟩
theorem s3692_plain_checked : check 97 s3692_plain_contract = true := by decide +kernel
def s3692_plain : CertifiedContract :=
  ⟨3692, 3687, 0, .none, s3692_plain_contract, 97, s3692_plain_checked⟩

def s3693_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, true, true] 0 (.inc 2)⟩
theorem s3693_plain_checked : check 336 s3693_plain_contract = true := by decide +kernel
def s3693_plain : CertifiedContract :=
  ⟨3693, 3694, 0, (.inc 2), s3693_plain_contract, 336, s3693_plain_checked⟩

def s3694_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, false] 0 (.inc 2)⟩
theorem s3694_plain_checked : check 345 s3694_plain_contract = true := by decide +kernel
def s3694_plain : CertifiedContract :=
  ⟨3694, 3695, 0, (.inc 2), s3694_plain_contract, 345, s3694_plain_checked⟩

def s3695_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, true, false] 0 .none⟩
theorem s3695_zero_checked : check 356 s3695_zero_contract = true := by decide +kernel
def s3695_zero : CertifiedContract :=
  ⟨3695, 3703, 0, .none, s3695_zero_contract, 356, s3695_zero_checked⟩

def s3695_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s3695_positive_checked : check 362 s3695_positive_contract = true := by decide +kernel
def s3695_positive : CertifiedContract :=
  ⟨3695, 3696, 1, (.dec 0), s3695_positive_contract, 362, s3695_positive_checked⟩

def s3696_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3696_plain_checked : check 372 s3696_plain_contract = true := by decide +kernel
def s3696_plain : CertifiedContract :=
  ⟨3696, 3697, 0, (.inc 5), s3696_plain_contract, 372, s3696_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s3647_zero,
  s3647_positive,
  s3648_plain,
  s3649_plain,
  s3650_zero,
  s3650_positive,
  s3651_plain,
  s3652_plain,
  s3653_plain,
  s3654_zero,
  s3654_positive,
  s3655_plain,
  s3656_zero,
  s3656_positive,
  s3657_plain,
  s3658_plain,
  s3659_plain,
  s3660_zero,
  s3660_positive,
  s3661_plain,
  s3662_plain,
  s3663_plain,
  s3664_plain,
  s3665_plain,
  s3666_zero,
  s3666_positive,
  s3667_plain,
  s3668_zero,
  s3668_positive,
  s3669_plain,
  s3670_zero,
  s3670_positive,
  s3671_plain,
  s3672_plain,
  s3673_plain,
  s3674_zero,
  s3674_positive,
  s3675_plain,
  s3676_plain,
  s3677_zero,
  s3677_positive,
  s3678_plain,
  s3679_plain,
  s3680_plain,
  s3681_zero,
  s3681_positive,
  s3682_plain,
  s3683_zero,
  s3683_positive,
  s3684_plain,
  s3685_plain,
  s3686_plain,
  s3687_zero,
  s3687_positive,
  s3688_plain,
  s3689_plain,
  s3690_plain,
  s3691_plain,
  s3692_plain,
  s3693_plain,
  s3694_plain,
  s3695_zero,
  s3695_positive,
  s3696_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S074
