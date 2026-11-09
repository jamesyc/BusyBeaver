module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S072
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s3548_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, true, false] 0 .none⟩
theorem s3548_zero_checked : check 372 s3548_zero_contract = true := by decide +kernel
def s3548_zero : CertifiedContract :=
  ⟨3548, 3552, 0, .none, s3548_zero_contract, 372, s3548_zero_checked⟩

def s3548_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3548_positive_checked : check 378 s3548_positive_contract = true := by decide +kernel
def s3548_positive : CertifiedContract :=
  ⟨3548, 3549, 1, (.dec 2), s3548_positive_contract, 378, s3548_positive_checked⟩

def s3549_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3549_plain_checked : check 391 s3549_plain_contract = true := by decide +kernel
def s3549_plain : CertifiedContract :=
  ⟨3549, 3550, 0, (.inc 5), s3549_plain_contract, 391, s3549_plain_checked⟩

def s3550_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3550_plain_checked : check 418 s3550_plain_contract = true := by decide +kernel
def s3550_plain : CertifiedContract :=
  ⟨3550, 3551, 0, (.inc 8), s3550_plain_contract, 418, s3550_plain_checked⟩

def s3551_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s3551_plain_checked : check 113 s3551_plain_contract = true := by decide +kernel
def s3551_plain : CertifiedContract :=
  ⟨3551, 3548, 0, .none, s3551_plain_contract, 113, s3551_plain_checked⟩

def s3552_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, true, false] 0 .none⟩
theorem s3552_zero_checked : check 393 s3552_zero_contract = true := by decide +kernel
def s3552_zero : CertifiedContract :=
  ⟨3552, 3558, 0, .none, s3552_zero_contract, 393, s3552_zero_checked⟩

def s3552_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3552_positive_checked : check 396 s3552_positive_contract = true := by decide +kernel
def s3552_positive : CertifiedContract :=
  ⟨3552, 3553, 1, (.dec 8), s3552_positive_contract, 396, s3552_positive_checked⟩

def s3553_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3553_plain_checked : check 391 s3553_plain_contract = true := by decide +kernel
def s3553_plain : CertifiedContract :=
  ⟨3553, 3554, 0, (.inc 5), s3553_plain_contract, 391, s3553_plain_checked⟩

def s3554_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, true, true, true] 0 .none⟩
theorem s3554_zero_checked : check 411 s3554_zero_contract = true := by decide +kernel
def s3554_zero : CertifiedContract :=
  ⟨3554, 3557, 0, .none, s3554_zero_contract, 411, s3554_zero_checked⟩

def s3554_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3554_positive_checked : check 414 s3554_positive_contract = true := by decide +kernel
def s3554_positive : CertifiedContract :=
  ⟨3554, 3555, 1, (.dec 8), s3554_positive_contract, 414, s3554_positive_checked⟩

def s3555_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3555_plain_checked : check 409 s3555_plain_contract = true := by decide +kernel
def s3555_plain : CertifiedContract :=
  ⟨3555, 3556, 0, (.inc 2), s3555_plain_contract, 409, s3555_plain_checked⟩

def s3556_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3556_plain_checked : check 113 s3556_plain_contract = true := by decide +kernel
def s3556_plain : CertifiedContract :=
  ⟨3556, 3554, 0, .none, s3556_plain_contract, 113, s3556_plain_checked⟩

def s3557_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s3557_plain_checked : check 116 s3557_plain_contract = true := by decide +kernel
def s3557_plain : CertifiedContract :=
  ⟨3557, 3548, 0, .none, s3557_plain_contract, 116, s3557_plain_checked⟩

def s3558_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, true] 0 .none⟩
theorem s3558_zero_checked : check 378 s3558_zero_contract = true := by decide +kernel
def s3558_zero : CertifiedContract :=
  ⟨3558, 3564, 0, .none, s3558_zero_contract, 378, s3558_zero_checked⟩

def s3558_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3558_positive_checked : check 378 s3558_positive_contract = true := by decide +kernel
def s3558_positive : CertifiedContract :=
  ⟨3558, 3559, 1, (.dec 5), s3558_positive_contract, 378, s3558_positive_checked⟩

def s3559_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3559_plain_checked : check 391 s3559_plain_contract = true := by decide +kernel
def s3559_plain : CertifiedContract :=
  ⟨3559, 3560, 0, (.inc 2), s3559_plain_contract, 391, s3559_plain_checked⟩

def s3560_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3560_plain_checked : check 394 s3560_plain_contract = true := by decide +kernel
def s3560_plain : CertifiedContract :=
  ⟨3560, 3561, 0, (.inc 2), s3560_plain_contract, 394, s3560_plain_checked⟩

def s3561_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3561_plain_checked : check 400 s3561_plain_contract = true := by decide +kernel
def s3561_plain : CertifiedContract :=
  ⟨3561, 3562, 0, (.inc 2), s3561_plain_contract, 400, s3561_plain_checked⟩

def s3562_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s3562_plain_checked : check 406 s3562_plain_contract = true := by decide +kernel
def s3562_plain : CertifiedContract :=
  ⟨3562, 3563, 0, (.inc 2), s3562_plain_contract, 406, s3562_plain_checked⟩

def s3563_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, false, true, true, false] 0 .none⟩
theorem s3563_plain_checked : check 101 s3563_plain_contract = true := by decide +kernel
def s3563_plain : CertifiedContract :=
  ⟨3563, 3558, 0, .none, s3563_plain_contract, 101, s3563_plain_checked⟩

def s3564_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, false] 0 (.inc 2)⟩
theorem s3564_plain_checked : check 358 s3564_plain_contract = true := by decide +kernel
def s3564_plain : CertifiedContract :=
  ⟨3564, 3565, 0, (.inc 2), s3564_plain_contract, 358, s3564_plain_checked⟩

def s3565_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false] 0 .none⟩
theorem s3565_zero_checked : check 348 s3565_zero_contract = true := by decide +kernel
def s3565_zero : CertifiedContract :=
  ⟨3565, 3573, 0, .none, s3565_zero_contract, 348, s3565_zero_checked⟩

def s3565_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s3565_positive_checked : check 354 s3565_positive_contract = true := by decide +kernel
def s3565_positive : CertifiedContract :=
  ⟨3565, 3566, 1, (.dec 0), s3565_positive_contract, 354, s3565_positive_checked⟩

def s3566_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3566_plain_checked : check 364 s3566_plain_contract = true := by decide +kernel
def s3566_plain : CertifiedContract :=
  ⟨3566, 3567, 0, (.inc 5), s3566_plain_contract, 364, s3566_plain_checked⟩

def s3567_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3567_zero_checked : check 390 s3567_zero_contract = true := by decide +kernel
def s3567_zero : CertifiedContract :=
  ⟨3567, 3569, 0, .none, s3567_zero_contract, 390, s3567_zero_checked⟩

def s3567_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3567_positive_checked : check 396 s3567_positive_contract = true := by decide +kernel
def s3567_positive : CertifiedContract :=
  ⟨3567, 3568, 1, (.dec 8), s3567_positive_contract, 396, s3567_positive_checked⟩

def s3568_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s3568_plain_checked : check 107 s3568_plain_contract = true := by decide +kernel
def s3568_plain : CertifiedContract :=
  ⟨3568, 3572, 0, .none, s3568_plain_contract, 107, s3568_plain_checked⟩

def s3569_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s3569_zero_checked : check 402 s3569_zero_contract = true := by decide +kernel
def s3569_zero : CertifiedContract :=
  ⟨3569, 3572, 0, .none, s3569_zero_contract, 402, s3569_zero_checked⟩

def s3569_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3569_positive_checked : check 405 s3569_positive_contract = true := by decide +kernel
def s3569_positive : CertifiedContract :=
  ⟨3569, 3570, 1, (.dec 5), s3569_positive_contract, 405, s3569_positive_checked⟩

def s3570_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3570_plain_checked : check 409 s3570_plain_contract = true := by decide +kernel
def s3570_plain : CertifiedContract :=
  ⟨3570, 3571, 0, (.inc 8), s3570_plain_contract, 409, s3570_plain_checked⟩

def s3571_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3571_plain_checked : check 110 s3571_plain_contract = true := by decide +kernel
def s3571_plain : CertifiedContract :=
  ⟨3571, 3569, 0, .none, s3571_plain_contract, 110, s3571_plain_checked⟩

def s3572_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, false] 0 .none⟩
theorem s3572_plain_checked : check 101 s3572_plain_contract = true := by decide +kernel
def s3572_plain : CertifiedContract :=
  ⟨3572, 3565, 0, .none, s3572_plain_contract, 101, s3572_plain_checked⟩

def s3573_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s3573_zero_checked : check 348 s3573_zero_contract = true := by decide +kernel
def s3573_zero : CertifiedContract :=
  ⟨3573, 3576, 0, .none, s3573_zero_contract, 348, s3573_zero_checked⟩

def s3573_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s3573_positive_checked : check 351 s3573_positive_contract = true := by decide +kernel
def s3573_positive : CertifiedContract :=
  ⟨3573, 3574, 1, (.dec 5), s3573_positive_contract, 351, s3573_positive_checked⟩

def s3574_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s3574_plain_checked : check 364 s3574_plain_contract = true := by decide +kernel
def s3574_plain : CertifiedContract :=
  ⟨3574, 3575, 0, (.inc 0), s3574_plain_contract, 364, s3574_plain_checked⟩

def s3575_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false] 0 .none⟩
theorem s3575_plain_checked : check 95 s3575_plain_contract = true := by decide +kernel
def s3575_plain : CertifiedContract :=
  ⟨3575, 3573, 0, .none, s3575_plain_contract, 95, s3575_plain_checked⟩

def s3576_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false] 0 .none⟩
theorem s3576_zero_checked : check 345 s3576_zero_contract = true := by decide +kernel
def s3576_zero : CertifiedContract :=
  ⟨3576, 3580, 0, .none, s3576_zero_contract, 345, s3576_zero_checked⟩

def s3576_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3576_positive_checked : check 351 s3576_positive_contract = true := by decide +kernel
def s3576_positive : CertifiedContract :=
  ⟨3576, 3577, 1, (.dec 2), s3576_positive_contract, 351, s3576_positive_checked⟩

def s3577_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3577_plain_checked : check 364 s3577_plain_contract = true := by decide +kernel
def s3577_plain : CertifiedContract :=
  ⟨3577, 3578, 0, (.inc 5), s3577_plain_contract, 364, s3577_plain_checked⟩

def s3578_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3578_plain_checked : check 391 s3578_plain_contract = true := by decide +kernel
def s3578_plain : CertifiedContract :=
  ⟨3578, 3579, 0, (.inc 8), s3578_plain_contract, 391, s3578_plain_checked⟩

def s3579_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s3579_plain_checked : check 104 s3579_plain_contract = true := by decide +kernel
def s3579_plain : CertifiedContract :=
  ⟨3579, 3576, 0, .none, s3579_plain_contract, 104, s3579_plain_checked⟩

def s3580_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, true, false] 0 .none⟩
theorem s3580_zero_checked : check 366 s3580_zero_contract = true := by decide +kernel
def s3580_zero : CertifiedContract :=
  ⟨3580, 3586, 0, .none, s3580_zero_contract, 366, s3580_zero_checked⟩

def s3580_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3580_positive_checked : check 369 s3580_positive_contract = true := by decide +kernel
def s3580_positive : CertifiedContract :=
  ⟨3580, 3581, 1, (.dec 8), s3580_positive_contract, 369, s3580_positive_checked⟩

def s3581_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3581_plain_checked : check 364 s3581_plain_contract = true := by decide +kernel
def s3581_plain : CertifiedContract :=
  ⟨3581, 3582, 0, (.inc 5), s3581_plain_contract, 364, s3581_plain_checked⟩

def s3582_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, true] 0 .none⟩
theorem s3582_zero_checked : check 384 s3582_zero_contract = true := by decide +kernel
def s3582_zero : CertifiedContract :=
  ⟨3582, 3585, 0, .none, s3582_zero_contract, 384, s3582_zero_checked⟩

def s3582_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3582_positive_checked : check 387 s3582_positive_contract = true := by decide +kernel
def s3582_positive : CertifiedContract :=
  ⟨3582, 3583, 1, (.dec 8), s3582_positive_contract, 387, s3582_positive_checked⟩

def s3583_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3583_plain_checked : check 382 s3583_plain_contract = true := by decide +kernel
def s3583_plain : CertifiedContract :=
  ⟨3583, 3584, 0, (.inc 2), s3583_plain_contract, 382, s3583_plain_checked⟩

def s3584_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3584_plain_checked : check 104 s3584_plain_contract = true := by decide +kernel
def s3584_plain : CertifiedContract :=
  ⟨3584, 3582, 0, .none, s3584_plain_contract, 104, s3584_plain_checked⟩

def s3585_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s3585_plain_checked : check 107 s3585_plain_contract = true := by decide +kernel
def s3585_plain : CertifiedContract :=
  ⟨3585, 3576, 0, .none, s3585_plain_contract, 107, s3585_plain_checked⟩

def s3586_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, false] 0 .none⟩
theorem s3586_zero_checked : check 351 s3586_zero_contract = true := by decide +kernel
def s3586_zero : CertifiedContract :=
  ⟨3586, 3592, 0, .none, s3586_zero_contract, 351, s3586_zero_checked⟩

def s3586_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3586_positive_checked : check 351 s3586_positive_contract = true := by decide +kernel
def s3586_positive : CertifiedContract :=
  ⟨3586, 3587, 1, (.dec 5), s3586_positive_contract, 351, s3586_positive_checked⟩

def s3587_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3587_plain_checked : check 364 s3587_plain_contract = true := by decide +kernel
def s3587_plain : CertifiedContract :=
  ⟨3587, 3588, 0, (.inc 2), s3587_plain_contract, 364, s3587_plain_checked⟩

def s3588_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3588_plain_checked : check 367 s3588_plain_contract = true := by decide +kernel
def s3588_plain : CertifiedContract :=
  ⟨3588, 3589, 0, (.inc 2), s3588_plain_contract, 367, s3588_plain_checked⟩

def s3589_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3589_plain_checked : check 373 s3589_plain_contract = true := by decide +kernel
def s3589_plain : CertifiedContract :=
  ⟨3589, 3590, 0, (.inc 2), s3589_plain_contract, 373, s3589_plain_checked⟩

def s3590_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s3590_plain_checked : check 379 s3590_plain_contract = true := by decide +kernel
def s3590_plain : CertifiedContract :=
  ⟨3590, 3591, 0, (.inc 2), s3590_plain_contract, 379, s3590_plain_checked⟩

def s3591_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, true, false] 0 .none⟩
theorem s3591_plain_checked : check 92 s3591_plain_contract = true := by decide +kernel
def s3591_plain : CertifiedContract :=
  ⟨3591, 3586, 0, .none, s3591_plain_contract, 92, s3591_plain_checked⟩

def s3592_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s3592_zero_checked : check 354 s3592_zero_contract = true := by decide +kernel
def s3592_zero : CertifiedContract :=
  ⟨3592, 3595, 0, .none, s3592_zero_contract, 354, s3592_zero_checked⟩

def s3592_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, false] 1 (.dec 2)⟩
theorem s3592_positive_checked : check 360 s3592_positive_contract = true := by decide +kernel
def s3592_positive : CertifiedContract :=
  ⟨3592, 3593, 1, (.dec 2), s3592_positive_contract, 360, s3592_positive_checked⟩

def s3593_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true] 0 (.inc 8)⟩
theorem s3593_plain_checked : check 373 s3593_plain_contract = true := by decide +kernel
def s3593_plain : CertifiedContract :=
  ⟨3593, 3594, 0, (.inc 8), s3593_plain_contract, 373, s3593_plain_checked⟩

def s3594_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, false] 0 .none⟩
theorem s3594_plain_checked : check 98 s3594_plain_contract = true := by decide +kernel
def s3594_plain : CertifiedContract :=
  ⟨3594, 3592, 0, .none, s3594_plain_contract, 98, s3594_plain_checked⟩

def s3595_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s3595_zero_checked : check 375 s3595_zero_contract = true := by decide +kernel
def s3595_zero : CertifiedContract :=
  ⟨3595, 3598, 0, .none, s3595_zero_contract, 375, s3595_zero_checked⟩

def s3595_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s3595_positive_checked : check 381 s3595_positive_contract = true := by decide +kernel
def s3595_positive : CertifiedContract :=
  ⟨3595, 3596, 1, (.dec 0), s3595_positive_contract, 381, s3595_positive_checked⟩

def s3596_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s3596_plain_checked : check 373 s3596_plain_contract = true := by decide +kernel
def s3596_plain : CertifiedContract :=
  ⟨3596, 3597, 0, (.inc 2), s3596_plain_contract, 373, s3596_plain_checked⟩

def s3597_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s3597_plain_checked : check 101 s3597_plain_contract = true := by decide +kernel
def s3597_plain : CertifiedContract :=
  ⟨3597, 3595, 0, .none, s3597_plain_contract, 101, s3597_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S072
