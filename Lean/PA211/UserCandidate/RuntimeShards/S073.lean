import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S073
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s3598_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3598_zero_checked : check 381 s3598_zero_contract = true := by decide +kernel
def s3598_zero : CertifiedContract :=
  ⟨3598, 3602, 0, .none, s3598_zero_contract, 381, s3598_zero_checked⟩

def s3598_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3598_positive_checked : check 387 s3598_positive_contract = true := by decide +kernel
def s3598_positive : CertifiedContract :=
  ⟨3598, 3599, 1, (.dec 2), s3598_positive_contract, 387, s3598_positive_checked⟩

def s3599_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3599_plain_checked : check 400 s3599_plain_contract = true := by decide +kernel
def s3599_plain : CertifiedContract :=
  ⟨3599, 3600, 0, (.inc 5), s3599_plain_contract, 400, s3599_plain_checked⟩

def s3600_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3600_plain_checked : check 427 s3600_plain_contract = true := by decide +kernel
def s3600_plain : CertifiedContract :=
  ⟨3600, 3601, 0, (.inc 8), s3600_plain_contract, 427, s3600_plain_checked⟩

def s3601_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s3601_plain_checked : check 116 s3601_plain_contract = true := by decide +kernel
def s3601_plain : CertifiedContract :=
  ⟨3601, 3598, 0, .none, s3601_plain_contract, 116, s3601_plain_checked⟩

def s3602_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s3602_zero_checked : check 402 s3602_zero_contract = true := by decide +kernel
def s3602_zero : CertifiedContract :=
  ⟨3602, 3608, 0, .none, s3602_zero_contract, 402, s3602_zero_checked⟩

def s3602_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3602_positive_checked : check 405 s3602_positive_contract = true := by decide +kernel
def s3602_positive : CertifiedContract :=
  ⟨3602, 3603, 1, (.dec 8), s3602_positive_contract, 405, s3602_positive_checked⟩

def s3603_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3603_plain_checked : check 400 s3603_plain_contract = true := by decide +kernel
def s3603_plain : CertifiedContract :=
  ⟨3603, 3604, 0, (.inc 5), s3603_plain_contract, 400, s3603_plain_checked⟩

def s3604_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s3604_zero_checked : check 420 s3604_zero_contract = true := by decide +kernel
def s3604_zero : CertifiedContract :=
  ⟨3604, 3607, 0, .none, s3604_zero_contract, 420, s3604_zero_checked⟩

def s3604_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3604_positive_checked : check 423 s3604_positive_contract = true := by decide +kernel
def s3604_positive : CertifiedContract :=
  ⟨3604, 3605, 1, (.dec 8), s3604_positive_contract, 423, s3604_positive_checked⟩

def s3605_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3605_plain_checked : check 418 s3605_plain_contract = true := by decide +kernel
def s3605_plain : CertifiedContract :=
  ⟨3605, 3606, 0, (.inc 2), s3605_plain_contract, 418, s3605_plain_checked⟩

def s3606_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3606_plain_checked : check 116 s3606_plain_contract = true := by decide +kernel
def s3606_plain : CertifiedContract :=
  ⟨3606, 3604, 0, .none, s3606_plain_contract, 116, s3606_plain_checked⟩

def s3607_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s3607_plain_checked : check 119 s3607_plain_contract = true := by decide +kernel
def s3607_plain : CertifiedContract :=
  ⟨3607, 3598, 0, .none, s3607_plain_contract, 119, s3607_plain_checked⟩

def s3608_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true] 0 .none⟩
theorem s3608_zero_checked : check 390 s3608_zero_contract = true := by decide +kernel
def s3608_zero : CertifiedContract :=
  ⟨3608, 3611, 0, .none, s3608_zero_contract, 390, s3608_zero_checked⟩

def s3608_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s3608_positive_checked : check 387 s3608_positive_contract = true := by decide +kernel
def s3608_positive : CertifiedContract :=
  ⟨3608, 3609, 1, (.dec 5), s3608_positive_contract, 387, s3608_positive_checked⟩

def s3609_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s3609_plain_checked : check 400 s3609_plain_contract = true := by decide +kernel
def s3609_plain : CertifiedContract :=
  ⟨3609, 3610, 0, (.inc 0), s3609_plain_contract, 400, s3609_plain_checked⟩

def s3610_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s3610_plain_checked : check 107 s3610_plain_contract = true := by decide +kernel
def s3610_plain : CertifiedContract :=
  ⟨3610, 3608, 0, .none, s3610_plain_contract, 107, s3610_plain_checked⟩

def s3611_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, false] 0 (.inc 2)⟩
theorem s3611_plain_checked : check 340 s3611_plain_contract = true := by decide +kernel
def s3611_plain : CertifiedContract :=
  ⟨3611, 3612, 0, (.inc 2), s3611_plain_contract, 340, s3611_plain_checked⟩

def s3612_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, true, false] 0 .none⟩
theorem s3612_zero_checked : check 357 s3612_zero_contract = true := by decide +kernel
def s3612_zero : CertifiedContract :=
  ⟨3612, 3620, 0, .none, s3612_zero_contract, 357, s3612_zero_checked⟩

def s3612_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, false] 1 (.dec 0)⟩
theorem s3612_positive_checked : check 363 s3612_positive_contract = true := by decide +kernel
def s3612_positive : CertifiedContract :=
  ⟨3612, 3613, 1, (.dec 0), s3612_positive_contract, 363, s3612_positive_checked⟩

def s3613_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3613_plain_checked : check 373 s3613_plain_contract = true := by decide +kernel
def s3613_plain : CertifiedContract :=
  ⟨3613, 3614, 0, (.inc 5), s3613_plain_contract, 373, s3613_plain_checked⟩

def s3614_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3614_zero_checked : check 399 s3614_zero_contract = true := by decide +kernel
def s3614_zero : CertifiedContract :=
  ⟨3614, 3616, 0, .none, s3614_zero_contract, 399, s3614_zero_checked⟩

def s3614_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3614_positive_checked : check 405 s3614_positive_contract = true := by decide +kernel
def s3614_positive : CertifiedContract :=
  ⟨3614, 3615, 1, (.dec 8), s3614_positive_contract, 405, s3614_positive_checked⟩

def s3615_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s3615_plain_checked : check 110 s3615_plain_contract = true := by decide +kernel
def s3615_plain : CertifiedContract :=
  ⟨3615, 3619, 0, .none, s3615_plain_contract, 110, s3615_plain_checked⟩

def s3616_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s3616_zero_checked : check 411 s3616_zero_contract = true := by decide +kernel
def s3616_zero : CertifiedContract :=
  ⟨3616, 3619, 0, .none, s3616_zero_contract, 411, s3616_zero_checked⟩

def s3616_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3616_positive_checked : check 414 s3616_positive_contract = true := by decide +kernel
def s3616_positive : CertifiedContract :=
  ⟨3616, 3617, 1, (.dec 5), s3616_positive_contract, 414, s3616_positive_checked⟩

def s3617_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3617_plain_checked : check 418 s3617_plain_contract = true := by decide +kernel
def s3617_plain : CertifiedContract :=
  ⟨3617, 3618, 0, (.inc 8), s3617_plain_contract, 418, s3617_plain_checked⟩

def s3618_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3618_plain_checked : check 113 s3618_plain_contract = true := by decide +kernel
def s3618_plain : CertifiedContract :=
  ⟨3618, 3616, 0, .none, s3618_plain_contract, 113, s3618_plain_checked⟩

def s3619_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s3619_plain_checked : check 104 s3619_plain_contract = true := by decide +kernel
def s3619_plain : CertifiedContract :=
  ⟨3619, 3612, 0, .none, s3619_plain_contract, 104, s3619_plain_checked⟩

def s3620_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, false, false] 0 .none⟩
theorem s3620_zero_checked : check 357 s3620_zero_contract = true := by decide +kernel
def s3620_zero : CertifiedContract :=
  ⟨3620, 3623, 0, .none, s3620_zero_contract, 357, s3620_zero_checked⟩

def s3620_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3620_positive_checked : check 360 s3620_positive_contract = true := by decide +kernel
def s3620_positive : CertifiedContract :=
  ⟨3620, 3621, 1, (.dec 5), s3620_positive_contract, 360, s3620_positive_checked⟩

def s3621_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, true, true, true] 0 (.inc 0)⟩
theorem s3621_plain_checked : check 373 s3621_plain_contract = true := by decide +kernel
def s3621_plain : CertifiedContract :=
  ⟨3621, 3622, 0, (.inc 0), s3621_plain_contract, 373, s3621_plain_checked⟩

def s3622_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, true, false] 0 .none⟩
theorem s3622_plain_checked : check 98 s3622_plain_contract = true := by decide +kernel
def s3622_plain : CertifiedContract :=
  ⟨3622, 3620, 0, .none, s3622_plain_contract, 98, s3622_plain_checked⟩

def s3623_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, true, false] 0 .none⟩
theorem s3623_zero_checked : check 354 s3623_zero_contract = true := by decide +kernel
def s3623_zero : CertifiedContract :=
  ⟨3623, 3627, 0, .none, s3623_zero_contract, 354, s3623_zero_checked⟩

def s3623_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3623_positive_checked : check 360 s3623_positive_contract = true := by decide +kernel
def s3623_positive : CertifiedContract :=
  ⟨3623, 3624, 1, (.dec 2), s3623_positive_contract, 360, s3623_positive_checked⟩

def s3624_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3624_plain_checked : check 373 s3624_plain_contract = true := by decide +kernel
def s3624_plain : CertifiedContract :=
  ⟨3624, 3625, 0, (.inc 5), s3624_plain_contract, 373, s3624_plain_checked⟩

def s3625_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3625_plain_checked : check 400 s3625_plain_contract = true := by decide +kernel
def s3625_plain : CertifiedContract :=
  ⟨3625, 3626, 0, (.inc 8), s3625_plain_contract, 400, s3625_plain_checked⟩

def s3626_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, false, false] 0 .none⟩
theorem s3626_plain_checked : check 107 s3626_plain_contract = true := by decide +kernel
def s3626_plain : CertifiedContract :=
  ⟨3626, 3623, 0, .none, s3626_plain_contract, 107, s3626_plain_checked⟩

def s3627_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, false] 0 .none⟩
theorem s3627_zero_checked : check 375 s3627_zero_contract = true := by decide +kernel
def s3627_zero : CertifiedContract :=
  ⟨3627, 3633, 0, .none, s3627_zero_contract, 375, s3627_zero_checked⟩

def s3627_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3627_positive_checked : check 378 s3627_positive_contract = true := by decide +kernel
def s3627_positive : CertifiedContract :=
  ⟨3627, 3628, 1, (.dec 8), s3627_positive_contract, 378, s3627_positive_checked⟩

def s3628_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3628_plain_checked : check 373 s3628_plain_contract = true := by decide +kernel
def s3628_plain : CertifiedContract :=
  ⟨3628, 3629, 0, (.inc 5), s3628_plain_contract, 373, s3628_plain_checked⟩

def s3629_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, true, true, true] 0 .none⟩
theorem s3629_zero_checked : check 393 s3629_zero_contract = true := by decide +kernel
def s3629_zero : CertifiedContract :=
  ⟨3629, 3632, 0, .none, s3629_zero_contract, 393, s3629_zero_checked⟩

def s3629_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3629_positive_checked : check 396 s3629_positive_contract = true := by decide +kernel
def s3629_positive : CertifiedContract :=
  ⟨3629, 3630, 1, (.dec 8), s3629_positive_contract, 396, s3629_positive_checked⟩

def s3630_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3630_plain_checked : check 391 s3630_plain_contract = true := by decide +kernel
def s3630_plain : CertifiedContract :=
  ⟨3630, 3631, 0, (.inc 2), s3630_plain_contract, 391, s3630_plain_checked⟩

def s3631_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3631_plain_checked : check 107 s3631_plain_contract = true := by decide +kernel
def s3631_plain : CertifiedContract :=
  ⟨3631, 3629, 0, .none, s3631_plain_contract, 107, s3631_plain_checked⟩

def s3632_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, false, false, false] 0 .none⟩
theorem s3632_plain_checked : check 110 s3632_plain_contract = true := by decide +kernel
def s3632_plain : CertifiedContract :=
  ⟨3632, 3623, 0, .none, s3632_plain_contract, 110, s3632_plain_checked⟩

def s3633_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s3633_zero_checked : check 372 s3633_zero_contract = true := by decide +kernel
def s3633_zero : CertifiedContract :=
  ⟨3633, 3639, 0, .none, s3633_zero_contract, 372, s3633_zero_checked⟩

def s3633_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3633_positive_checked : check 360 s3633_positive_contract = true := by decide +kernel
def s3633_positive : CertifiedContract :=
  ⟨3633, 3634, 1, (.dec 5), s3633_positive_contract, 360, s3633_positive_checked⟩

def s3634_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3634_plain_checked : check 373 s3634_plain_contract = true := by decide +kernel
def s3634_plain : CertifiedContract :=
  ⟨3634, 3635, 0, (.inc 2), s3634_plain_contract, 373, s3634_plain_checked⟩

def s3635_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3635_plain_checked : check 376 s3635_plain_contract = true := by decide +kernel
def s3635_plain : CertifiedContract :=
  ⟨3635, 3636, 0, (.inc 2), s3635_plain_contract, 376, s3635_plain_checked⟩

def s3636_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3636_plain_checked : check 382 s3636_plain_contract = true := by decide +kernel
def s3636_plain : CertifiedContract :=
  ⟨3636, 3637, 0, (.inc 2), s3636_plain_contract, 382, s3636_plain_checked⟩

def s3637_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, true] 0 (.inc 2)⟩
theorem s3637_plain_checked : check 388 s3637_plain_contract = true := by decide +kernel
def s3637_plain : CertifiedContract :=
  ⟨3637, 3638, 0, (.inc 2), s3637_plain_contract, 388, s3637_plain_checked⟩

def s3638_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, false] 0 .none⟩
theorem s3638_plain_checked : check 95 s3638_plain_contract = true := by decide +kernel
def s3638_plain : CertifiedContract :=
  ⟨3638, 3633, 0, .none, s3638_plain_contract, 95, s3638_plain_checked⟩

def s3639_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, true, false] 0 .none⟩
theorem s3639_zero_checked : check 357 s3639_zero_contract = true := by decide +kernel
def s3639_zero : CertifiedContract :=
  ⟨3639, 3647, 0, .none, s3639_zero_contract, 357, s3639_zero_checked⟩

def s3639_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s3639_positive_checked : check 363 s3639_positive_contract = true := by decide +kernel
def s3639_positive : CertifiedContract :=
  ⟨3639, 3640, 1, (.dec 0), s3639_positive_contract, 363, s3639_positive_checked⟩

def s3640_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3640_plain_checked : check 373 s3640_plain_contract = true := by decide +kernel
def s3640_plain : CertifiedContract :=
  ⟨3640, 3641, 0, (.inc 5), s3640_plain_contract, 373, s3640_plain_checked⟩

def s3641_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3641_zero_checked : check 399 s3641_zero_contract = true := by decide +kernel
def s3641_zero : CertifiedContract :=
  ⟨3641, 3643, 0, .none, s3641_zero_contract, 399, s3641_zero_checked⟩

def s3641_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3641_positive_checked : check 405 s3641_positive_contract = true := by decide +kernel
def s3641_positive : CertifiedContract :=
  ⟨3641, 3642, 1, (.dec 8), s3641_positive_contract, 405, s3641_positive_checked⟩

def s3642_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s3642_plain_checked : check 110 s3642_plain_contract = true := by decide +kernel
def s3642_plain : CertifiedContract :=
  ⟨3642, 3646, 0, .none, s3642_plain_contract, 110, s3642_plain_checked⟩

def s3643_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s3643_zero_checked : check 411 s3643_zero_contract = true := by decide +kernel
def s3643_zero : CertifiedContract :=
  ⟨3643, 3646, 0, .none, s3643_zero_contract, 411, s3643_zero_checked⟩

def s3643_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3643_positive_checked : check 414 s3643_positive_contract = true := by decide +kernel
def s3643_positive : CertifiedContract :=
  ⟨3643, 3644, 1, (.dec 5), s3643_positive_contract, 414, s3643_positive_checked⟩

def s3644_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3644_plain_checked : check 418 s3644_plain_contract = true := by decide +kernel
def s3644_plain : CertifiedContract :=
  ⟨3644, 3645, 0, (.inc 8), s3644_plain_contract, 418, s3644_plain_checked⟩

def s3645_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3645_plain_checked : check 113 s3645_plain_contract = true := by decide +kernel
def s3645_plain : CertifiedContract :=
  ⟨3645, 3643, 0, .none, s3645_plain_contract, 113, s3645_plain_checked⟩

def s3646_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s3646_plain_checked : check 104 s3646_plain_contract = true := by decide +kernel
def s3646_plain : CertifiedContract :=
  ⟨3646, 3639, 0, .none, s3646_plain_contract, 104, s3646_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S073
