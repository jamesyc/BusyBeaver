module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S072
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s3548_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s3548_zero_checked : check 362 s3548_zero_contract = true := by decide +kernel
def s3548_zero : CertifiedContract :=
  ⟨3548, 3552, 0, .none, s3548_zero_contract, 362, s3548_zero_checked⟩

def s3548_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3548_positive_checked : check 368 s3548_positive_contract = true := by decide +kernel
def s3548_positive : CertifiedContract :=
  ⟨3548, 3549, 1, (.dec 2), s3548_positive_contract, 368, s3548_positive_checked⟩

def s3549_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3549_plain_checked : check 381 s3549_plain_contract = true := by decide +kernel
def s3549_plain : CertifiedContract :=
  ⟨3549, 3550, 0, (.inc 5), s3549_plain_contract, 381, s3549_plain_checked⟩

def s3550_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3550_plain_checked : check 408 s3550_plain_contract = true := by decide +kernel
def s3550_plain : CertifiedContract :=
  ⟨3550, 3551, 0, (.inc 8), s3550_plain_contract, 408, s3550_plain_checked⟩

def s3551_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s3551_plain_checked : check 109 s3551_plain_contract = true := by decide +kernel
def s3551_plain : CertifiedContract :=
  ⟨3551, 3548, 0, .none, s3551_plain_contract, 109, s3551_plain_checked⟩

def s3552_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s3552_zero_checked : check 383 s3552_zero_contract = true := by decide +kernel
def s3552_zero : CertifiedContract :=
  ⟨3552, 3558, 0, .none, s3552_zero_contract, 383, s3552_zero_checked⟩

def s3552_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3552_positive_checked : check 386 s3552_positive_contract = true := by decide +kernel
def s3552_positive : CertifiedContract :=
  ⟨3552, 3553, 1, (.dec 8), s3552_positive_contract, 386, s3552_positive_checked⟩

def s3553_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3553_plain_checked : check 381 s3553_plain_contract = true := by decide +kernel
def s3553_plain : CertifiedContract :=
  ⟨3553, 3554, 0, (.inc 5), s3553_plain_contract, 381, s3553_plain_checked⟩

def s3554_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s3554_zero_checked : check 401 s3554_zero_contract = true := by decide +kernel
def s3554_zero : CertifiedContract :=
  ⟨3554, 3557, 0, .none, s3554_zero_contract, 401, s3554_zero_checked⟩

def s3554_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3554_positive_checked : check 404 s3554_positive_contract = true := by decide +kernel
def s3554_positive : CertifiedContract :=
  ⟨3554, 3555, 1, (.dec 8), s3554_positive_contract, 404, s3554_positive_checked⟩

def s3555_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3555_plain_checked : check 399 s3555_plain_contract = true := by decide +kernel
def s3555_plain : CertifiedContract :=
  ⟨3555, 3556, 0, (.inc 2), s3555_plain_contract, 399, s3555_plain_checked⟩

def s3556_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3556_plain_checked : check 109 s3556_plain_contract = true := by decide +kernel
def s3556_plain : CertifiedContract :=
  ⟨3556, 3554, 0, .none, s3556_plain_contract, 109, s3556_plain_checked⟩

def s3557_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s3557_plain_checked : check 112 s3557_plain_contract = true := by decide +kernel
def s3557_plain : CertifiedContract :=
  ⟨3557, 3548, 0, .none, s3557_plain_contract, 112, s3557_plain_checked⟩

def s3558_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, true] 0 .none⟩
theorem s3558_zero_checked : check 368 s3558_zero_contract = true := by decide +kernel
def s3558_zero : CertifiedContract :=
  ⟨3558, 3564, 0, .none, s3558_zero_contract, 368, s3558_zero_checked⟩

def s3558_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3558_positive_checked : check 368 s3558_positive_contract = true := by decide +kernel
def s3558_positive : CertifiedContract :=
  ⟨3558, 3559, 1, (.dec 5), s3558_positive_contract, 368, s3558_positive_checked⟩

def s3559_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3559_plain_checked : check 381 s3559_plain_contract = true := by decide +kernel
def s3559_plain : CertifiedContract :=
  ⟨3559, 3560, 0, (.inc 2), s3559_plain_contract, 381, s3559_plain_checked⟩

def s3560_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3560_plain_checked : check 384 s3560_plain_contract = true := by decide +kernel
def s3560_plain : CertifiedContract :=
  ⟨3560, 3561, 0, (.inc 2), s3560_plain_contract, 384, s3560_plain_checked⟩

def s3561_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3561_plain_checked : check 381 s3561_plain_contract = true := by decide +kernel
def s3561_plain : CertifiedContract :=
  ⟨3561, 3562, 0, (.inc 2), s3561_plain_contract, 381, s3561_plain_checked⟩

def s3562_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s3562_plain_checked : check 387 s3562_plain_contract = true := by decide +kernel
def s3562_plain : CertifiedContract :=
  ⟨3562, 3563, 0, (.inc 2), s3562_plain_contract, 387, s3562_plain_checked⟩

def s3563_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s3563_plain_checked : check 97 s3563_plain_contract = true := by decide +kernel
def s3563_plain : CertifiedContract :=
  ⟨3563, 3558, 0, .none, s3563_plain_contract, 97, s3563_plain_checked⟩

def s3564_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, false] 0 (.inc 2)⟩
theorem s3564_plain_checked : check 342 s3564_plain_contract = true := by decide +kernel
def s3564_plain : CertifiedContract :=
  ⟨3564, 3565, 0, (.inc 2), s3564_plain_contract, 342, s3564_plain_checked⟩

def s3565_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, false] 0 .none⟩
theorem s3565_zero_checked : check 356 s3565_zero_contract = true := by decide +kernel
def s3565_zero : CertifiedContract :=
  ⟨3565, 3573, 0, .none, s3565_zero_contract, 356, s3565_zero_checked⟩

def s3565_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s3565_positive_checked : check 362 s3565_positive_contract = true := by decide +kernel
def s3565_positive : CertifiedContract :=
  ⟨3565, 3566, 1, (.dec 0), s3565_positive_contract, 362, s3565_positive_checked⟩

def s3566_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3566_plain_checked : check 372 s3566_plain_contract = true := by decide +kernel
def s3566_plain : CertifiedContract :=
  ⟨3566, 3567, 0, (.inc 5), s3566_plain_contract, 372, s3566_plain_checked⟩

def s3567_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3567_zero_checked : check 398 s3567_zero_contract = true := by decide +kernel
def s3567_zero : CertifiedContract :=
  ⟨3567, 3569, 0, .none, s3567_zero_contract, 398, s3567_zero_checked⟩

def s3567_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3567_positive_checked : check 404 s3567_positive_contract = true := by decide +kernel
def s3567_positive : CertifiedContract :=
  ⟨3567, 3568, 1, (.dec 8), s3567_positive_contract, 404, s3567_positive_checked⟩

def s3568_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s3568_plain_checked : check 109 s3568_plain_contract = true := by decide +kernel
def s3568_plain : CertifiedContract :=
  ⟨3568, 3572, 0, .none, s3568_plain_contract, 109, s3568_plain_checked⟩

def s3569_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s3569_zero_checked : check 410 s3569_zero_contract = true := by decide +kernel
def s3569_zero : CertifiedContract :=
  ⟨3569, 3572, 0, .none, s3569_zero_contract, 410, s3569_zero_checked⟩

def s3569_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3569_positive_checked : check 413 s3569_positive_contract = true := by decide +kernel
def s3569_positive : CertifiedContract :=
  ⟨3569, 3570, 1, (.dec 5), s3569_positive_contract, 413, s3569_positive_checked⟩

def s3570_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3570_plain_checked : check 417 s3570_plain_contract = true := by decide +kernel
def s3570_plain : CertifiedContract :=
  ⟨3570, 3571, 0, (.inc 8), s3570_plain_contract, 417, s3570_plain_checked⟩

def s3571_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3571_plain_checked : check 112 s3571_plain_contract = true := by decide +kernel
def s3571_plain : CertifiedContract :=
  ⟨3571, 3569, 0, .none, s3571_plain_contract, 112, s3571_plain_checked⟩

def s3572_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, false, false] 0 .none⟩
theorem s3572_plain_checked : check 103 s3572_plain_contract = true := by decide +kernel
def s3572_plain : CertifiedContract :=
  ⟨3572, 3565, 0, .none, s3572_plain_contract, 103, s3572_plain_checked⟩

def s3573_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s3573_zero_checked : check 356 s3573_zero_contract = true := by decide +kernel
def s3573_zero : CertifiedContract :=
  ⟨3573, 3576, 0, .none, s3573_zero_contract, 356, s3573_zero_checked⟩

def s3573_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s3573_positive_checked : check 359 s3573_positive_contract = true := by decide +kernel
def s3573_positive : CertifiedContract :=
  ⟨3573, 3574, 1, (.dec 5), s3573_positive_contract, 359, s3573_positive_checked⟩

def s3574_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s3574_plain_checked : check 372 s3574_plain_contract = true := by decide +kernel
def s3574_plain : CertifiedContract :=
  ⟨3574, 3575, 0, (.inc 0), s3574_plain_contract, 372, s3574_plain_checked⟩

def s3575_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, false] 0 .none⟩
theorem s3575_plain_checked : check 97 s3575_plain_contract = true := by decide +kernel
def s3575_plain : CertifiedContract :=
  ⟨3575, 3573, 0, .none, s3575_plain_contract, 97, s3575_plain_checked⟩

def s3576_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, true, false] 0 .none⟩
theorem s3576_zero_checked : check 353 s3576_zero_contract = true := by decide +kernel
def s3576_zero : CertifiedContract :=
  ⟨3576, 3580, 0, .none, s3576_zero_contract, 353, s3576_zero_checked⟩

def s3576_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3576_positive_checked : check 359 s3576_positive_contract = true := by decide +kernel
def s3576_positive : CertifiedContract :=
  ⟨3576, 3577, 1, (.dec 2), s3576_positive_contract, 359, s3576_positive_checked⟩

def s3577_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3577_plain_checked : check 372 s3577_plain_contract = true := by decide +kernel
def s3577_plain : CertifiedContract :=
  ⟨3577, 3578, 0, (.inc 5), s3577_plain_contract, 372, s3577_plain_checked⟩

def s3578_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3578_plain_checked : check 399 s3578_plain_contract = true := by decide +kernel
def s3578_plain : CertifiedContract :=
  ⟨3578, 3579, 0, (.inc 8), s3578_plain_contract, 399, s3578_plain_checked⟩

def s3579_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s3579_plain_checked : check 106 s3579_plain_contract = true := by decide +kernel
def s3579_plain : CertifiedContract :=
  ⟨3579, 3576, 0, .none, s3579_plain_contract, 106, s3579_plain_checked⟩

def s3580_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, true, false] 0 .none⟩
theorem s3580_zero_checked : check 374 s3580_zero_contract = true := by decide +kernel
def s3580_zero : CertifiedContract :=
  ⟨3580, 3586, 0, .none, s3580_zero_contract, 374, s3580_zero_checked⟩

def s3580_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3580_positive_checked : check 377 s3580_positive_contract = true := by decide +kernel
def s3580_positive : CertifiedContract :=
  ⟨3580, 3581, 1, (.dec 8), s3580_positive_contract, 377, s3580_positive_checked⟩

def s3581_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3581_plain_checked : check 372 s3581_plain_contract = true := by decide +kernel
def s3581_plain : CertifiedContract :=
  ⟨3581, 3582, 0, (.inc 5), s3581_plain_contract, 372, s3581_plain_checked⟩

def s3582_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, true, true, true] 0 .none⟩
theorem s3582_zero_checked : check 392 s3582_zero_contract = true := by decide +kernel
def s3582_zero : CertifiedContract :=
  ⟨3582, 3585, 0, .none, s3582_zero_contract, 392, s3582_zero_checked⟩

def s3582_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3582_positive_checked : check 395 s3582_positive_contract = true := by decide +kernel
def s3582_positive : CertifiedContract :=
  ⟨3582, 3583, 1, (.dec 8), s3582_positive_contract, 395, s3582_positive_checked⟩

def s3583_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3583_plain_checked : check 390 s3583_plain_contract = true := by decide +kernel
def s3583_plain : CertifiedContract :=
  ⟨3583, 3584, 0, (.inc 2), s3583_plain_contract, 390, s3583_plain_checked⟩

def s3584_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3584_plain_checked : check 106 s3584_plain_contract = true := by decide +kernel
def s3584_plain : CertifiedContract :=
  ⟨3584, 3582, 0, .none, s3584_plain_contract, 106, s3584_plain_checked⟩

def s3585_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s3585_plain_checked : check 109 s3585_plain_contract = true := by decide +kernel
def s3585_plain : CertifiedContract :=
  ⟨3585, 3576, 0, .none, s3585_plain_contract, 109, s3585_plain_checked⟩

def s3586_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, false, false] 0 .none⟩
theorem s3586_zero_checked : check 359 s3586_zero_contract = true := by decide +kernel
def s3586_zero : CertifiedContract :=
  ⟨3586, 3592, 0, .none, s3586_zero_contract, 359, s3586_zero_checked⟩

def s3586_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3586_positive_checked : check 359 s3586_positive_contract = true := by decide +kernel
def s3586_positive : CertifiedContract :=
  ⟨3586, 3587, 1, (.dec 5), s3586_positive_contract, 359, s3586_positive_checked⟩

def s3587_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3587_plain_checked : check 372 s3587_plain_contract = true := by decide +kernel
def s3587_plain : CertifiedContract :=
  ⟨3587, 3588, 0, (.inc 2), s3587_plain_contract, 372, s3587_plain_checked⟩

def s3588_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3588_plain_checked : check 375 s3588_plain_contract = true := by decide +kernel
def s3588_plain : CertifiedContract :=
  ⟨3588, 3589, 0, (.inc 2), s3588_plain_contract, 375, s3588_plain_checked⟩

def s3589_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3589_plain_checked : check 372 s3589_plain_contract = true := by decide +kernel
def s3589_plain : CertifiedContract :=
  ⟨3589, 3590, 0, (.inc 2), s3589_plain_contract, 372, s3589_plain_checked⟩

def s3590_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s3590_plain_checked : check 378 s3590_plain_contract = true := by decide +kernel
def s3590_plain : CertifiedContract :=
  ⟨3590, 3591, 0, (.inc 2), s3590_plain_contract, 378, s3590_plain_checked⟩

def s3591_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, false, true, true, false] 0 .none⟩
theorem s3591_plain_checked : check 94 s3591_plain_contract = true := by decide +kernel
def s3591_plain : CertifiedContract :=
  ⟨3591, 3586, 0, .none, s3591_plain_contract, 94, s3591_plain_checked⟩

def s3592_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s3592_zero_checked : check 362 s3592_zero_contract = true := by decide +kernel
def s3592_zero : CertifiedContract :=
  ⟨3592, 3595, 0, .none, s3592_zero_contract, 362, s3592_zero_checked⟩

def s3592_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, false, true, false] 1 (.dec 2)⟩
theorem s3592_positive_checked : check 368 s3592_positive_contract = true := by decide +kernel
def s3592_positive : CertifiedContract :=
  ⟨3592, 3593, 1, (.dec 2), s3592_positive_contract, 368, s3592_positive_checked⟩

def s3593_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, false, true, true] 0 (.inc 8)⟩
theorem s3593_plain_checked : check 381 s3593_plain_contract = true := by decide +kernel
def s3593_plain : CertifiedContract :=
  ⟨3593, 3594, 0, (.inc 8), s3593_plain_contract, 381, s3593_plain_checked⟩

def s3594_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, false, false] 0 .none⟩
theorem s3594_plain_checked : check 100 s3594_plain_contract = true := by decide +kernel
def s3594_plain : CertifiedContract :=
  ⟨3594, 3592, 0, .none, s3594_plain_contract, 100, s3594_plain_checked⟩

def s3595_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s3595_zero_checked : check 383 s3595_zero_contract = true := by decide +kernel
def s3595_zero : CertifiedContract :=
  ⟨3595, 3598, 0, .none, s3595_zero_contract, 383, s3595_zero_checked⟩

def s3595_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s3595_positive_checked : check 389 s3595_positive_contract = true := by decide +kernel
def s3595_positive : CertifiedContract :=
  ⟨3595, 3596, 1, (.dec 0), s3595_positive_contract, 389, s3595_positive_checked⟩

def s3596_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s3596_plain_checked : check 381 s3596_plain_contract = true := by decide +kernel
def s3596_plain : CertifiedContract :=
  ⟨3596, 3597, 0, (.inc 2), s3596_plain_contract, 381, s3596_plain_checked⟩

def s3597_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s3597_plain_checked : check 103 s3597_plain_contract = true := by decide +kernel
def s3597_plain : CertifiedContract :=
  ⟨3597, 3595, 0, .none, s3597_plain_contract, 103, s3597_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s3548_zero,
  s3548_positive,
  s3549_plain,
  s3550_plain,
  s3551_plain,
  s3552_zero,
  s3552_positive,
  s3553_plain,
  s3554_zero,
  s3554_positive,
  s3555_plain,
  s3556_plain,
  s3557_plain,
  s3558_zero,
  s3558_positive,
  s3559_plain,
  s3560_plain,
  s3561_plain,
  s3562_plain,
  s3563_plain,
  s3564_plain,
  s3565_zero,
  s3565_positive,
  s3566_plain,
  s3567_zero,
  s3567_positive,
  s3568_plain,
  s3569_zero,
  s3569_positive,
  s3570_plain,
  s3571_plain,
  s3572_plain,
  s3573_zero,
  s3573_positive,
  s3574_plain,
  s3575_plain,
  s3576_zero,
  s3576_positive,
  s3577_plain,
  s3578_plain,
  s3579_plain,
  s3580_zero,
  s3580_positive,
  s3581_plain,
  s3582_zero,
  s3582_positive,
  s3583_plain,
  s3584_plain,
  s3585_plain,
  s3586_zero,
  s3586_positive,
  s3587_plain,
  s3588_plain,
  s3589_plain,
  s3590_plain,
  s3591_plain,
  s3592_zero,
  s3592_positive,
  s3593_plain,
  s3594_plain,
  s3595_zero,
  s3595_positive,
  s3596_plain,
  s3597_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S072
