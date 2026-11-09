module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S071
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s3499_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3499_plain_checked : check 115 s3499_plain_contract = true := by decide +kernel
def s3499_plain : CertifiedContract :=
  ⟨3499, 3497, 0, .none, s3499_plain_contract, 115, s3499_plain_checked⟩

def s3500_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s3500_plain_checked : check 118 s3500_plain_contract = true := by decide +kernel
def s3500_plain : CertifiedContract :=
  ⟨3500, 3491, 0, .none, s3500_plain_contract, 118, s3500_plain_checked⟩

def s3501_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s3501_zero_checked : check 389 s3501_zero_contract = true := by decide +kernel
def s3501_zero : CertifiedContract :=
  ⟨3501, 3504, 0, .none, s3501_zero_contract, 389, s3501_zero_checked⟩

def s3501_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s3501_positive_checked : check 386 s3501_positive_contract = true := by decide +kernel
def s3501_positive : CertifiedContract :=
  ⟨3501, 3502, 1, (.dec 5), s3501_positive_contract, 386, s3501_positive_checked⟩

def s3502_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s3502_plain_checked : check 399 s3502_plain_contract = true := by decide +kernel
def s3502_plain : CertifiedContract :=
  ⟨3502, 3503, 0, (.inc 0), s3502_plain_contract, 399, s3502_plain_checked⟩

def s3503_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s3503_plain_checked : check 106 s3503_plain_contract = true := by decide +kernel
def s3503_plain : CertifiedContract :=
  ⟨3503, 3501, 0, .none, s3503_plain_contract, 106, s3503_plain_checked⟩

def s3504_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s3504_zero_checked : check 353 s3504_zero_contract = true := by decide +kernel
def s3504_zero : CertifiedContract :=
  ⟨3504, 3508, 0, .none, s3504_zero_contract, 353, s3504_zero_checked⟩

def s3504_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false] 1 (.dec 4)⟩
theorem s3504_positive_checked : check 359 s3504_positive_contract = true := by decide +kernel
def s3504_positive : CertifiedContract :=
  ⟨3504, 3505, 1, (.dec 4), s3504_positive_contract, 359, s3504_positive_checked⟩

def s3505_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s3505_plain_checked : check 372 s3505_plain_contract = true := by decide +kernel
def s3505_plain : CertifiedContract :=
  ⟨3505, 3506, 0, (.inc 2), s3505_plain_contract, 372, s3505_plain_checked⟩

def s3506_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3506_plain_checked : check 399 s3506_plain_contract = true := by decide +kernel
def s3506_plain : CertifiedContract :=
  ⟨3506, 3507, 0, (.inc 8), s3506_plain_contract, 399, s3506_plain_checked⟩

def s3507_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s3507_plain_checked : check 106 s3507_plain_contract = true := by decide +kernel
def s3507_plain : CertifiedContract :=
  ⟨3507, 3504, 0, .none, s3507_plain_contract, 106, s3507_plain_checked⟩

def s3508_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s3508_zero_checked : check 359 s3508_zero_contract = true := by decide +kernel
def s3508_zero : CertifiedContract :=
  ⟨3508, 3511, 0, .none, s3508_zero_contract, 359, s3508_zero_checked⟩

def s3508_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s3508_positive_checked : check 359 s3508_positive_contract = true := by decide +kernel
def s3508_positive : CertifiedContract :=
  ⟨3508, 3509, 1, (.dec 8), s3508_positive_contract, 359, s3508_positive_checked⟩

def s3509_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, true, true] 0 (.inc 4)⟩
theorem s3509_plain_checked : check 363 s3509_plain_contract = true := by decide +kernel
def s3509_plain : CertifiedContract :=
  ⟨3509, 3510, 0, (.inc 4), s3509_plain_contract, 363, s3509_plain_checked⟩

def s3510_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s3510_plain_checked : check 97 s3510_plain_contract = true := by decide +kernel
def s3510_plain : CertifiedContract :=
  ⟨3510, 3508, 0, .none, s3510_plain_contract, 97, s3510_plain_checked⟩

def s3511_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s3511_zero_checked : check 353 s3511_zero_contract = true := by decide +kernel
def s3511_zero : CertifiedContract :=
  ⟨3511, 3514, 0, .none, s3511_zero_contract, 353, s3511_zero_checked⟩

def s3511_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3511_positive_checked : check 359 s3511_positive_contract = true := by decide +kernel
def s3511_positive : CertifiedContract :=
  ⟨3511, 3512, 1, (.dec 2), s3511_positive_contract, 359, s3511_positive_checked⟩

def s3512_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s3512_plain_checked : check 372 s3512_plain_contract = true := by decide +kernel
def s3512_plain : CertifiedContract :=
  ⟨3512, 3513, 0, (.inc 8), s3512_plain_contract, 372, s3512_plain_checked⟩

def s3513_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s3513_plain_checked : check 97 s3513_plain_contract = true := by decide +kernel
def s3513_plain : CertifiedContract :=
  ⟨3513, 3511, 0, .none, s3513_plain_contract, 97, s3513_plain_checked⟩

def s3514_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s3514_zero_checked : check 374 s3514_zero_contract = true := by decide +kernel
def s3514_zero : CertifiedContract :=
  ⟨3514, 3517, 0, .none, s3514_zero_contract, 374, s3514_zero_checked⟩

def s3514_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s3514_positive_checked : check 380 s3514_positive_contract = true := by decide +kernel
def s3514_positive : CertifiedContract :=
  ⟨3514, 3515, 1, (.dec 0), s3514_positive_contract, 380, s3514_positive_checked⟩

def s3515_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s3515_plain_checked : check 372 s3515_plain_contract = true := by decide +kernel
def s3515_plain : CertifiedContract :=
  ⟨3515, 3516, 0, (.inc 2), s3515_plain_contract, 372, s3515_plain_checked⟩

def s3516_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s3516_plain_checked : check 100 s3516_plain_contract = true := by decide +kernel
def s3516_plain : CertifiedContract :=
  ⟨3516, 3514, 0, .none, s3516_plain_contract, 100, s3516_plain_checked⟩

def s3517_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3517_zero_checked : check 380 s3517_zero_contract = true := by decide +kernel
def s3517_zero : CertifiedContract :=
  ⟨3517, 3521, 0, .none, s3517_zero_contract, 380, s3517_zero_checked⟩

def s3517_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3517_positive_checked : check 386 s3517_positive_contract = true := by decide +kernel
def s3517_positive : CertifiedContract :=
  ⟨3517, 3518, 1, (.dec 2), s3517_positive_contract, 386, s3517_positive_checked⟩

def s3518_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3518_plain_checked : check 399 s3518_plain_contract = true := by decide +kernel
def s3518_plain : CertifiedContract :=
  ⟨3518, 3519, 0, (.inc 5), s3518_plain_contract, 399, s3518_plain_checked⟩

def s3519_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3519_plain_checked : check 426 s3519_plain_contract = true := by decide +kernel
def s3519_plain : CertifiedContract :=
  ⟨3519, 3520, 0, (.inc 8), s3519_plain_contract, 426, s3519_plain_checked⟩

def s3520_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s3520_plain_checked : check 115 s3520_plain_contract = true := by decide +kernel
def s3520_plain : CertifiedContract :=
  ⟨3520, 3517, 0, .none, s3520_plain_contract, 115, s3520_plain_checked⟩

def s3521_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s3521_zero_checked : check 401 s3521_zero_contract = true := by decide +kernel
def s3521_zero : CertifiedContract :=
  ⟨3521, 3527, 0, .none, s3521_zero_contract, 401, s3521_zero_checked⟩

def s3521_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3521_positive_checked : check 404 s3521_positive_contract = true := by decide +kernel
def s3521_positive : CertifiedContract :=
  ⟨3521, 3522, 1, (.dec 8), s3521_positive_contract, 404, s3521_positive_checked⟩

def s3522_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3522_plain_checked : check 399 s3522_plain_contract = true := by decide +kernel
def s3522_plain : CertifiedContract :=
  ⟨3522, 3523, 0, (.inc 5), s3522_plain_contract, 399, s3522_plain_checked⟩

def s3523_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s3523_zero_checked : check 419 s3523_zero_contract = true := by decide +kernel
def s3523_zero : CertifiedContract :=
  ⟨3523, 3526, 0, .none, s3523_zero_contract, 419, s3523_zero_checked⟩

def s3523_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3523_positive_checked : check 422 s3523_positive_contract = true := by decide +kernel
def s3523_positive : CertifiedContract :=
  ⟨3523, 3524, 1, (.dec 8), s3523_positive_contract, 422, s3523_positive_checked⟩

def s3524_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3524_plain_checked : check 417 s3524_plain_contract = true := by decide +kernel
def s3524_plain : CertifiedContract :=
  ⟨3524, 3525, 0, (.inc 2), s3524_plain_contract, 417, s3524_plain_checked⟩

def s3525_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3525_plain_checked : check 115 s3525_plain_contract = true := by decide +kernel
def s3525_plain : CertifiedContract :=
  ⟨3525, 3523, 0, .none, s3525_plain_contract, 115, s3525_plain_checked⟩

def s3526_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s3526_plain_checked : check 118 s3526_plain_contract = true := by decide +kernel
def s3526_plain : CertifiedContract :=
  ⟨3526, 3517, 0, .none, s3526_plain_contract, 118, s3526_plain_checked⟩

def s3527_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s3527_zero_checked : check 389 s3527_zero_contract = true := by decide +kernel
def s3527_zero : CertifiedContract :=
  ⟨3527, 3530, 0, .none, s3527_zero_contract, 389, s3527_zero_checked⟩

def s3527_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s3527_positive_checked : check 386 s3527_positive_contract = true := by decide +kernel
def s3527_positive : CertifiedContract :=
  ⟨3527, 3528, 1, (.dec 5), s3527_positive_contract, 386, s3527_positive_checked⟩

def s3528_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s3528_plain_checked : check 399 s3528_plain_contract = true := by decide +kernel
def s3528_plain : CertifiedContract :=
  ⟨3528, 3529, 0, (.inc 0), s3528_plain_contract, 399, s3528_plain_checked⟩

def s3529_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s3529_plain_checked : check 106 s3529_plain_contract = true := by decide +kernel
def s3529_plain : CertifiedContract :=
  ⟨3529, 3527, 0, .none, s3529_plain_contract, 106, s3529_plain_checked⟩

def s3530_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s3530_zero_checked : check 353 s3530_zero_contract = true := by decide +kernel
def s3530_zero : CertifiedContract :=
  ⟨3530, 3534, 0, .none, s3530_zero_contract, 353, s3530_zero_checked⟩

def s3530_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s3530_positive_checked : check 359 s3530_positive_contract = true := by decide +kernel
def s3530_positive : CertifiedContract :=
  ⟨3530, 3531, 1, (.dec 7), s3530_positive_contract, 359, s3530_positive_checked⟩

def s3531_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s3531_plain_checked : check 363 s3531_plain_contract = true := by decide +kernel
def s3531_plain : CertifiedContract :=
  ⟨3531, 3532, 0, (.inc 2), s3531_plain_contract, 363, s3531_plain_checked⟩

def s3532_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3532_plain_checked : check 390 s3532_plain_contract = true := by decide +kernel
def s3532_plain : CertifiedContract :=
  ⟨3532, 3533, 0, (.inc 8), s3532_plain_contract, 390, s3532_plain_checked⟩

def s3533_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s3533_plain_checked : check 103 s3533_plain_contract = true := by decide +kernel
def s3533_plain : CertifiedContract :=
  ⟨3533, 3530, 0, .none, s3533_plain_contract, 103, s3533_plain_checked⟩

def s3534_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s3534_zero_checked : check 362 s3534_zero_contract = true := by decide +kernel
def s3534_zero : CertifiedContract :=
  ⟨3534, 3537, 0, .none, s3534_zero_contract, 362, s3534_zero_checked⟩

def s3534_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s3534_positive_checked : check 359 s3534_positive_contract = true := by decide +kernel
def s3534_positive : CertifiedContract :=
  ⟨3534, 3535, 1, (.dec 8), s3534_positive_contract, 359, s3534_positive_checked⟩

def s3535_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s3535_plain_checked : check 390 s3535_plain_contract = true := by decide +kernel
def s3535_plain : CertifiedContract :=
  ⟨3535, 3536, 0, (.inc 7), s3535_plain_contract, 390, s3535_plain_checked⟩

def s3536_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s3536_plain_checked : check 97 s3536_plain_contract = true := by decide +kernel
def s3536_plain : CertifiedContract :=
  ⟨3536, 3534, 0, .none, s3536_plain_contract, 97, s3536_plain_checked⟩

def s3537_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s3537_zero_checked : check 365 s3537_zero_contract = true := by decide +kernel
def s3537_zero : CertifiedContract :=
  ⟨3537, 3545, 0, .none, s3537_zero_contract, 365, s3537_zero_checked⟩

def s3537_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s3537_positive_checked : check 371 s3537_positive_contract = true := by decide +kernel
def s3537_positive : CertifiedContract :=
  ⟨3537, 3538, 1, (.dec 0), s3537_positive_contract, 371, s3537_positive_checked⟩

def s3538_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3538_plain_checked : check 381 s3538_plain_contract = true := by decide +kernel
def s3538_plain : CertifiedContract :=
  ⟨3538, 3539, 0, (.inc 5), s3538_plain_contract, 381, s3538_plain_checked⟩

def s3539_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3539_zero_checked : check 407 s3539_zero_contract = true := by decide +kernel
def s3539_zero : CertifiedContract :=
  ⟨3539, 3541, 0, .none, s3539_zero_contract, 407, s3539_zero_checked⟩

def s3539_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3539_positive_checked : check 413 s3539_positive_contract = true := by decide +kernel
def s3539_positive : CertifiedContract :=
  ⟨3539, 3540, 1, (.dec 8), s3539_positive_contract, 413, s3539_positive_checked⟩

def s3540_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s3540_plain_checked : check 112 s3540_plain_contract = true := by decide +kernel
def s3540_plain : CertifiedContract :=
  ⟨3540, 3544, 0, .none, s3540_plain_contract, 112, s3540_plain_checked⟩

def s3541_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s3541_zero_checked : check 419 s3541_zero_contract = true := by decide +kernel
def s3541_zero : CertifiedContract :=
  ⟨3541, 3544, 0, .none, s3541_zero_contract, 419, s3541_zero_checked⟩

def s3541_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3541_positive_checked : check 422 s3541_positive_contract = true := by decide +kernel
def s3541_positive : CertifiedContract :=
  ⟨3541, 3542, 1, (.dec 5), s3541_positive_contract, 422, s3541_positive_checked⟩

def s3542_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3542_plain_checked : check 426 s3542_plain_contract = true := by decide +kernel
def s3542_plain : CertifiedContract :=
  ⟨3542, 3543, 0, (.inc 8), s3542_plain_contract, 426, s3542_plain_checked⟩

def s3543_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3543_plain_checked : check 115 s3543_plain_contract = true := by decide +kernel
def s3543_plain : CertifiedContract :=
  ⟨3543, 3541, 0, .none, s3543_plain_contract, 115, s3543_plain_checked⟩

def s3544_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s3544_plain_checked : check 106 s3544_plain_contract = true := by decide +kernel
def s3544_plain : CertifiedContract :=
  ⟨3544, 3537, 0, .none, s3544_plain_contract, 106, s3544_plain_checked⟩

def s3545_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s3545_zero_checked : check 365 s3545_zero_contract = true := by decide +kernel
def s3545_zero : CertifiedContract :=
  ⟨3545, 3548, 0, .none, s3545_zero_contract, 365, s3545_zero_checked⟩

def s3545_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s3545_positive_checked : check 368 s3545_positive_contract = true := by decide +kernel
def s3545_positive : CertifiedContract :=
  ⟨3545, 3546, 1, (.dec 5), s3545_positive_contract, 368, s3545_positive_checked⟩

def s3546_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s3546_plain_checked : check 381 s3546_plain_contract = true := by decide +kernel
def s3546_plain : CertifiedContract :=
  ⟨3546, 3547, 0, (.inc 0), s3546_plain_contract, 381, s3546_plain_checked⟩

def s3547_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s3547_plain_checked : check 100 s3547_plain_contract = true := by decide +kernel
def s3547_plain : CertifiedContract :=
  ⟨3547, 3545, 0, .none, s3547_plain_contract, 100, s3547_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s3499_plain,
  s3500_plain,
  s3501_zero,
  s3501_positive,
  s3502_plain,
  s3503_plain,
  s3504_zero,
  s3504_positive,
  s3505_plain,
  s3506_plain,
  s3507_plain,
  s3508_zero,
  s3508_positive,
  s3509_plain,
  s3510_plain,
  s3511_zero,
  s3511_positive,
  s3512_plain,
  s3513_plain,
  s3514_zero,
  s3514_positive,
  s3515_plain,
  s3516_plain,
  s3517_zero,
  s3517_positive,
  s3518_plain,
  s3519_plain,
  s3520_plain,
  s3521_zero,
  s3521_positive,
  s3522_plain,
  s3523_zero,
  s3523_positive,
  s3524_plain,
  s3525_plain,
  s3526_plain,
  s3527_zero,
  s3527_positive,
  s3528_plain,
  s3529_plain,
  s3530_zero,
  s3530_positive,
  s3531_plain,
  s3532_plain,
  s3533_plain,
  s3534_zero,
  s3534_positive,
  s3535_plain,
  s3536_plain,
  s3537_zero,
  s3537_positive,
  s3538_plain,
  s3539_zero,
  s3539_positive,
  s3540_plain,
  s3541_zero,
  s3541_positive,
  s3542_plain,
  s3543_plain,
  s3544_plain,
  s3545_zero,
  s3545_positive,
  s3546_plain,
  s3547_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S071
