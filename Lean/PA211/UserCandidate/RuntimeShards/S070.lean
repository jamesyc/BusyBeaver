module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S070
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s3449_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3449_plain_checked : check 107 s3449_plain_contract = true := by decide +kernel
def s3449_plain : CertifiedContract :=
  ⟨3449, 3447, 0, .none, s3449_plain_contract, 107, s3449_plain_checked⟩

def s3450_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s3450_plain_checked : check 110 s3450_plain_contract = true := by decide +kernel
def s3450_plain : CertifiedContract :=
  ⟨3450, 3441, 0, .none, s3450_plain_contract, 110, s3450_plain_checked⟩

def s3451_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s3451_zero_checked : check 360 s3451_zero_contract = true := by decide +kernel
def s3451_zero : CertifiedContract :=
  ⟨3451, 3457, 0, .none, s3451_zero_contract, 360, s3451_zero_checked⟩

def s3451_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3451_positive_checked : check 360 s3451_positive_contract = true := by decide +kernel
def s3451_positive : CertifiedContract :=
  ⟨3451, 3452, 1, (.dec 5), s3451_positive_contract, 360, s3451_positive_checked⟩

def s3452_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3452_plain_checked : check 373 s3452_plain_contract = true := by decide +kernel
def s3452_plain : CertifiedContract :=
  ⟨3452, 3453, 0, (.inc 2), s3452_plain_contract, 373, s3452_plain_checked⟩

def s3453_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3453_plain_checked : check 376 s3453_plain_contract = true := by decide +kernel
def s3453_plain : CertifiedContract :=
  ⟨3453, 3454, 0, (.inc 2), s3453_plain_contract, 376, s3453_plain_checked⟩

def s3454_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3454_plain_checked : check 382 s3454_plain_contract = true := by decide +kernel
def s3454_plain : CertifiedContract :=
  ⟨3454, 3455, 0, (.inc 2), s3454_plain_contract, 382, s3454_plain_checked⟩

def s3455_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s3455_plain_checked : check 388 s3455_plain_contract = true := by decide +kernel
def s3455_plain : CertifiedContract :=
  ⟨3455, 3456, 0, (.inc 2), s3455_plain_contract, 388, s3455_plain_checked⟩

def s3456_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s3456_plain_checked : check 95 s3456_plain_contract = true := by decide +kernel
def s3456_plain : CertifiedContract :=
  ⟨3456, 3451, 0, .none, s3456_plain_contract, 95, s3456_plain_checked⟩

def s3457_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, true, true] 0 (.inc 2)⟩
theorem s3457_plain_checked : check 328 s3457_plain_contract = true := by decide +kernel
def s3457_plain : CertifiedContract :=
  ⟨3457, 3458, 0, (.inc 2), s3457_plain_contract, 328, s3457_plain_checked⟩

def s3458_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, false, false] 0 (.inc 2)⟩
theorem s3458_plain_checked : check 334 s3458_plain_contract = true := by decide +kernel
def s3458_plain : CertifiedContract :=
  ⟨3458, 3459, 0, (.inc 2), s3458_plain_contract, 334, s3458_plain_checked⟩

def s3459_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, false, false] 0 .none⟩
theorem s3459_zero_checked : check 345 s3459_zero_contract = true := by decide +kernel
def s3459_zero : CertifiedContract :=
  ⟨3459, 3462, 0, .none, s3459_zero_contract, 345, s3459_zero_checked⟩

def s3459_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, false, true, false] 1 (.dec 2)⟩
theorem s3459_positive_checked : check 351 s3459_positive_contract = true := by decide +kernel
def s3459_positive : CertifiedContract :=
  ⟨3459, 3460, 1, (.dec 2), s3459_positive_contract, 351, s3459_positive_checked⟩

def s3460_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, false, true, true] 0 (.inc 8)⟩
theorem s3460_plain_checked : check 364 s3460_plain_contract = true := by decide +kernel
def s3460_plain : CertifiedContract :=
  ⟨3460, 3461, 0, (.inc 8), s3460_plain_contract, 364, s3460_plain_checked⟩

def s3461_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s3461_plain_checked : check 95 s3461_plain_contract = true := by decide +kernel
def s3461_plain : CertifiedContract :=
  ⟨3461, 3459, 0, .none, s3461_plain_contract, 95, s3461_plain_checked⟩

def s3462_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s3462_zero_checked : check 366 s3462_zero_contract = true := by decide +kernel
def s3462_zero : CertifiedContract :=
  ⟨3462, 3465, 0, .none, s3462_zero_contract, 366, s3462_zero_checked⟩

def s3462_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s3462_positive_checked : check 372 s3462_positive_contract = true := by decide +kernel
def s3462_positive : CertifiedContract :=
  ⟨3462, 3463, 1, (.dec 0), s3462_positive_contract, 372, s3462_positive_checked⟩

def s3463_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s3463_plain_checked : check 364 s3463_plain_contract = true := by decide +kernel
def s3463_plain : CertifiedContract :=
  ⟨3463, 3464, 0, (.inc 2), s3463_plain_contract, 364, s3463_plain_checked⟩

def s3464_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, false, false] 0 .none⟩
theorem s3464_plain_checked : check 98 s3464_plain_contract = true := by decide +kernel
def s3464_plain : CertifiedContract :=
  ⟨3464, 3462, 0, .none, s3464_plain_contract, 98, s3464_plain_checked⟩

def s3465_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3465_zero_checked : check 372 s3465_zero_contract = true := by decide +kernel
def s3465_zero : CertifiedContract :=
  ⟨3465, 3469, 0, .none, s3465_zero_contract, 372, s3465_zero_checked⟩

def s3465_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3465_positive_checked : check 378 s3465_positive_contract = true := by decide +kernel
def s3465_positive : CertifiedContract :=
  ⟨3465, 3466, 1, (.dec 2), s3465_positive_contract, 378, s3465_positive_checked⟩

def s3466_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3466_plain_checked : check 391 s3466_plain_contract = true := by decide +kernel
def s3466_plain : CertifiedContract :=
  ⟨3466, 3467, 0, (.inc 5), s3466_plain_contract, 391, s3466_plain_checked⟩

def s3467_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3467_plain_checked : check 418 s3467_plain_contract = true := by decide +kernel
def s3467_plain : CertifiedContract :=
  ⟨3467, 3468, 0, (.inc 8), s3467_plain_contract, 418, s3467_plain_checked⟩

def s3468_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s3468_plain_checked : check 113 s3468_plain_contract = true := by decide +kernel
def s3468_plain : CertifiedContract :=
  ⟨3468, 3465, 0, .none, s3468_plain_contract, 113, s3468_plain_checked⟩

def s3469_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s3469_zero_checked : check 393 s3469_zero_contract = true := by decide +kernel
def s3469_zero : CertifiedContract :=
  ⟨3469, 3475, 0, .none, s3469_zero_contract, 393, s3469_zero_checked⟩

def s3469_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3469_positive_checked : check 396 s3469_positive_contract = true := by decide +kernel
def s3469_positive : CertifiedContract :=
  ⟨3469, 3470, 1, (.dec 8), s3469_positive_contract, 396, s3469_positive_checked⟩

def s3470_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3470_plain_checked : check 391 s3470_plain_contract = true := by decide +kernel
def s3470_plain : CertifiedContract :=
  ⟨3470, 3471, 0, (.inc 5), s3470_plain_contract, 391, s3470_plain_checked⟩

def s3471_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s3471_zero_checked : check 411 s3471_zero_contract = true := by decide +kernel
def s3471_zero : CertifiedContract :=
  ⟨3471, 3474, 0, .none, s3471_zero_contract, 411, s3471_zero_checked⟩

def s3471_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3471_positive_checked : check 414 s3471_positive_contract = true := by decide +kernel
def s3471_positive : CertifiedContract :=
  ⟨3471, 3472, 1, (.dec 8), s3471_positive_contract, 414, s3471_positive_checked⟩

def s3472_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3472_plain_checked : check 409 s3472_plain_contract = true := by decide +kernel
def s3472_plain : CertifiedContract :=
  ⟨3472, 3473, 0, (.inc 2), s3472_plain_contract, 409, s3472_plain_checked⟩

def s3473_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3473_plain_checked : check 113 s3473_plain_contract = true := by decide +kernel
def s3473_plain : CertifiedContract :=
  ⟨3473, 3471, 0, .none, s3473_plain_contract, 113, s3473_plain_checked⟩

def s3474_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s3474_plain_checked : check 116 s3474_plain_contract = true := by decide +kernel
def s3474_plain : CertifiedContract :=
  ⟨3474, 3465, 0, .none, s3474_plain_contract, 116, s3474_plain_checked⟩

def s3475_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, true, false, false] 0 .none⟩
theorem s3475_zero_checked : check 381 s3475_zero_contract = true := by decide +kernel
def s3475_zero : CertifiedContract :=
  ⟨3475, 3478, 0, .none, s3475_zero_contract, 381, s3475_zero_checked⟩

def s3475_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s3475_positive_checked : check 378 s3475_positive_contract = true := by decide +kernel
def s3475_positive : CertifiedContract :=
  ⟨3475, 3476, 1, (.dec 5), s3475_positive_contract, 378, s3475_positive_checked⟩

def s3476_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s3476_plain_checked : check 391 s3476_plain_contract = true := by decide +kernel
def s3476_plain : CertifiedContract :=
  ⟨3476, 3477, 0, (.inc 0), s3476_plain_contract, 391, s3476_plain_checked⟩

def s3477_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s3477_plain_checked : check 104 s3477_plain_contract = true := by decide +kernel
def s3477_plain : CertifiedContract :=
  ⟨3477, 3475, 0, .none, s3477_plain_contract, 104, s3477_plain_checked⟩

def s3478_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s3478_zero_checked : check 345 s3478_zero_contract = true := by decide +kernel
def s3478_zero : CertifiedContract :=
  ⟨3478, 3482, 0, .none, s3478_zero_contract, 345, s3478_zero_checked⟩

def s3478_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, true, false, true, false] 1 (.dec 4)⟩
theorem s3478_positive_checked : check 351 s3478_positive_contract = true := by decide +kernel
def s3478_positive : CertifiedContract :=
  ⟨3478, 3479, 1, (.dec 4), s3478_positive_contract, 351, s3478_positive_checked⟩

def s3479_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s3479_plain_checked : check 364 s3479_plain_contract = true := by decide +kernel
def s3479_plain : CertifiedContract :=
  ⟨3479, 3480, 0, (.inc 2), s3479_plain_contract, 364, s3479_plain_checked⟩

def s3480_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3480_plain_checked : check 391 s3480_plain_contract = true := by decide +kernel
def s3480_plain : CertifiedContract :=
  ⟨3480, 3481, 0, (.inc 8), s3480_plain_contract, 391, s3480_plain_checked⟩

def s3481_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, true, false, false] 0 .none⟩
theorem s3481_plain_checked : check 104 s3481_plain_contract = true := by decide +kernel
def s3481_plain : CertifiedContract :=
  ⟨3481, 3478, 0, .none, s3481_plain_contract, 104, s3481_plain_checked⟩

def s3482_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, false, false] 0 .none⟩
theorem s3482_zero_checked : check 351 s3482_zero_contract = true := by decide +kernel
def s3482_zero : CertifiedContract :=
  ⟨3482, 3485, 0, .none, s3482_zero_contract, 351, s3482_zero_checked⟩

def s3482_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, true, true, true, false] 1 (.dec 8)⟩
theorem s3482_positive_checked : check 351 s3482_positive_contract = true := by decide +kernel
def s3482_positive : CertifiedContract :=
  ⟨3482, 3483, 1, (.dec 8), s3482_positive_contract, 351, s3482_positive_checked⟩

def s3483_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, true, true, true, true] 0 (.inc 4)⟩
theorem s3483_plain_checked : check 355 s3483_plain_contract = true := by decide +kernel
def s3483_plain : CertifiedContract :=
  ⟨3483, 3484, 0, (.inc 4), s3483_plain_contract, 355, s3483_plain_checked⟩

def s3484_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s3484_plain_checked : check 95 s3484_plain_contract = true := by decide +kernel
def s3484_plain : CertifiedContract :=
  ⟨3484, 3482, 0, .none, s3484_plain_contract, 95, s3484_plain_checked⟩

def s3485_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s3485_zero_checked : check 363 s3485_zero_contract = true := by decide +kernel
def s3485_zero : CertifiedContract :=
  ⟨3485, 3488, 0, .none, s3485_zero_contract, 363, s3485_zero_checked⟩

def s3485_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s3485_positive_checked : check 369 s3485_positive_contract = true := by decide +kernel
def s3485_positive : CertifiedContract :=
  ⟨3485, 3486, 1, (.dec 2), s3485_positive_contract, 369, s3485_positive_checked⟩

def s3486_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s3486_plain_checked : check 382 s3486_plain_contract = true := by decide +kernel
def s3486_plain : CertifiedContract :=
  ⟨3486, 3487, 0, (.inc 8), s3486_plain_contract, 382, s3486_plain_checked⟩

def s3487_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, false, false] 0 .none⟩
theorem s3487_plain_checked : check 101 s3487_plain_contract = true := by decide +kernel
def s3487_plain : CertifiedContract :=
  ⟨3487, 3485, 0, .none, s3487_plain_contract, 101, s3487_plain_checked⟩

def s3488_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s3488_zero_checked : check 384 s3488_zero_contract = true := by decide +kernel
def s3488_zero : CertifiedContract :=
  ⟨3488, 3491, 0, .none, s3488_zero_contract, 384, s3488_zero_checked⟩

def s3488_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s3488_positive_checked : check 390 s3488_positive_contract = true := by decide +kernel
def s3488_positive : CertifiedContract :=
  ⟨3488, 3489, 1, (.dec 0), s3488_positive_contract, 390, s3488_positive_checked⟩

def s3489_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s3489_plain_checked : check 382 s3489_plain_contract = true := by decide +kernel
def s3489_plain : CertifiedContract :=
  ⟨3489, 3490, 0, (.inc 2), s3489_plain_contract, 382, s3489_plain_checked⟩

def s3490_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s3490_plain_checked : check 104 s3490_plain_contract = true := by decide +kernel
def s3490_plain : CertifiedContract :=
  ⟨3490, 3488, 0, .none, s3490_plain_contract, 104, s3490_plain_checked⟩

def s3491_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3491_zero_checked : check 390 s3491_zero_contract = true := by decide +kernel
def s3491_zero : CertifiedContract :=
  ⟨3491, 3495, 0, .none, s3491_zero_contract, 390, s3491_zero_checked⟩

def s3491_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3491_positive_checked : check 396 s3491_positive_contract = true := by decide +kernel
def s3491_positive : CertifiedContract :=
  ⟨3491, 3492, 1, (.dec 2), s3491_positive_contract, 396, s3491_positive_checked⟩

def s3492_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3492_plain_checked : check 409 s3492_plain_contract = true := by decide +kernel
def s3492_plain : CertifiedContract :=
  ⟨3492, 3493, 0, (.inc 5), s3492_plain_contract, 409, s3492_plain_checked⟩

def s3493_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3493_plain_checked : check 436 s3493_plain_contract = true := by decide +kernel
def s3493_plain : CertifiedContract :=
  ⟨3493, 3494, 0, (.inc 8), s3493_plain_contract, 436, s3493_plain_checked⟩

def s3494_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s3494_plain_checked : check 119 s3494_plain_contract = true := by decide +kernel
def s3494_plain : CertifiedContract :=
  ⟨3494, 3491, 0, .none, s3494_plain_contract, 119, s3494_plain_checked⟩

def s3495_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, true, false] 0 .none⟩
theorem s3495_zero_checked : check 411 s3495_zero_contract = true := by decide +kernel
def s3495_zero : CertifiedContract :=
  ⟨3495, 3501, 0, .none, s3495_zero_contract, 411, s3495_zero_checked⟩

def s3495_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3495_positive_checked : check 414 s3495_positive_contract = true := by decide +kernel
def s3495_positive : CertifiedContract :=
  ⟨3495, 3496, 1, (.dec 8), s3495_positive_contract, 414, s3495_positive_checked⟩

def s3496_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3496_plain_checked : check 409 s3496_plain_contract = true := by decide +kernel
def s3496_plain : CertifiedContract :=
  ⟨3496, 3497, 0, (.inc 5), s3496_plain_contract, 409, s3496_plain_checked⟩

def s3497_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s3497_zero_checked : check 429 s3497_zero_contract = true := by decide +kernel
def s3497_zero : CertifiedContract :=
  ⟨3497, 3500, 0, .none, s3497_zero_contract, 429, s3497_zero_checked⟩

def s3497_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3497_positive_checked : check 432 s3497_positive_contract = true := by decide +kernel
def s3497_positive : CertifiedContract :=
  ⟨3497, 3498, 1, (.dec 8), s3497_positive_contract, 432, s3497_positive_checked⟩

def s3498_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3498_plain_checked : check 427 s3498_plain_contract = true := by decide +kernel
def s3498_plain : CertifiedContract :=
  ⟨3498, 3499, 0, (.inc 2), s3498_plain_contract, 427, s3498_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S070
