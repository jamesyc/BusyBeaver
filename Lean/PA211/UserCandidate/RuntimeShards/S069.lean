import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S069
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s3400_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s3400_plain_checked : check 409 s3400_plain_contract = true := by decide +kernel
def s3400_plain : CertifiedContract :=
  ⟨3400, 3401, 0, (.inc 0), s3400_plain_contract, 409, s3400_plain_checked⟩

def s3401_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s3401_plain_checked : check 110 s3401_plain_contract = true := by decide +kernel
def s3401_plain : CertifiedContract :=
  ⟨3401, 3399, 0, .none, s3401_plain_contract, 110, s3401_plain_checked⟩

def s3402_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, false] 0 (.inc 2)⟩
theorem s3402_plain_checked : check 349 s3402_plain_contract = true := by decide +kernel
def s3402_plain : CertifiedContract :=
  ⟨3402, 3403, 0, (.inc 2), s3402_plain_contract, 349, s3402_plain_checked⟩

def s3403_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, true, false] 0 .none⟩
theorem s3403_zero_checked : check 366 s3403_zero_contract = true := by decide +kernel
def s3403_zero : CertifiedContract :=
  ⟨3403, 3411, 0, .none, s3403_zero_contract, 366, s3403_zero_checked⟩

def s3403_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, true, false] 1 (.dec 0)⟩
theorem s3403_positive_checked : check 372 s3403_positive_contract = true := by decide +kernel
def s3403_positive : CertifiedContract :=
  ⟨3403, 3404, 1, (.dec 0), s3403_positive_contract, 372, s3403_positive_checked⟩

def s3404_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3404_plain_checked : check 382 s3404_plain_contract = true := by decide +kernel
def s3404_plain : CertifiedContract :=
  ⟨3404, 3405, 0, (.inc 5), s3404_plain_contract, 382, s3404_plain_checked⟩

def s3405_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3405_zero_checked : check 408 s3405_zero_contract = true := by decide +kernel
def s3405_zero : CertifiedContract :=
  ⟨3405, 3407, 0, .none, s3405_zero_contract, 408, s3405_zero_checked⟩

def s3405_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3405_positive_checked : check 414 s3405_positive_contract = true := by decide +kernel
def s3405_positive : CertifiedContract :=
  ⟨3405, 3406, 1, (.dec 8), s3405_positive_contract, 414, s3405_positive_checked⟩

def s3406_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s3406_plain_checked : check 113 s3406_plain_contract = true := by decide +kernel
def s3406_plain : CertifiedContract :=
  ⟨3406, 3410, 0, .none, s3406_plain_contract, 113, s3406_plain_checked⟩

def s3407_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s3407_zero_checked : check 420 s3407_zero_contract = true := by decide +kernel
def s3407_zero : CertifiedContract :=
  ⟨3407, 3410, 0, .none, s3407_zero_contract, 420, s3407_zero_checked⟩

def s3407_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3407_positive_checked : check 423 s3407_positive_contract = true := by decide +kernel
def s3407_positive : CertifiedContract :=
  ⟨3407, 3408, 1, (.dec 5), s3407_positive_contract, 423, s3407_positive_checked⟩

def s3408_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3408_plain_checked : check 427 s3408_plain_contract = true := by decide +kernel
def s3408_plain : CertifiedContract :=
  ⟨3408, 3409, 0, (.inc 8), s3408_plain_contract, 427, s3408_plain_checked⟩

def s3409_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3409_plain_checked : check 116 s3409_plain_contract = true := by decide +kernel
def s3409_plain : CertifiedContract :=
  ⟨3409, 3407, 0, .none, s3409_plain_contract, 116, s3409_plain_checked⟩

def s3410_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s3410_plain_checked : check 107 s3410_plain_contract = true := by decide +kernel
def s3410_plain : CertifiedContract :=
  ⟨3410, 3403, 0, .none, s3410_plain_contract, 107, s3410_plain_checked⟩

def s3411_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, false, false] 0 .none⟩
theorem s3411_zero_checked : check 366 s3411_zero_contract = true := by decide +kernel
def s3411_zero : CertifiedContract :=
  ⟨3411, 3414, 0, .none, s3411_zero_contract, 366, s3411_zero_checked⟩

def s3411_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3411_positive_checked : check 369 s3411_positive_contract = true := by decide +kernel
def s3411_positive : CertifiedContract :=
  ⟨3411, 3412, 1, (.dec 5), s3411_positive_contract, 369, s3411_positive_checked⟩

def s3412_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, true, true, true] 0 (.inc 0)⟩
theorem s3412_plain_checked : check 382 s3412_plain_contract = true := by decide +kernel
def s3412_plain : CertifiedContract :=
  ⟨3412, 3413, 0, (.inc 0), s3412_plain_contract, 382, s3412_plain_checked⟩

def s3413_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, false, true, false] 0 .none⟩
theorem s3413_plain_checked : check 101 s3413_plain_contract = true := by decide +kernel
def s3413_plain : CertifiedContract :=
  ⟨3413, 3411, 0, .none, s3413_plain_contract, 101, s3413_plain_checked⟩

def s3414_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, true, false] 0 .none⟩
theorem s3414_zero_checked : check 363 s3414_zero_contract = true := by decide +kernel
def s3414_zero : CertifiedContract :=
  ⟨3414, 3418, 0, .none, s3414_zero_contract, 363, s3414_zero_checked⟩

def s3414_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3414_positive_checked : check 369 s3414_positive_contract = true := by decide +kernel
def s3414_positive : CertifiedContract :=
  ⟨3414, 3415, 1, (.dec 2), s3414_positive_contract, 369, s3414_positive_checked⟩

def s3415_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3415_plain_checked : check 382 s3415_plain_contract = true := by decide +kernel
def s3415_plain : CertifiedContract :=
  ⟨3415, 3416, 0, (.inc 5), s3415_plain_contract, 382, s3415_plain_checked⟩

def s3416_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3416_plain_checked : check 409 s3416_plain_contract = true := by decide +kernel
def s3416_plain : CertifiedContract :=
  ⟨3416, 3417, 0, (.inc 8), s3416_plain_contract, 409, s3416_plain_checked⟩

def s3417_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, false, false] 0 .none⟩
theorem s3417_plain_checked : check 110 s3417_plain_contract = true := by decide +kernel
def s3417_plain : CertifiedContract :=
  ⟨3417, 3414, 0, .none, s3417_plain_contract, 110, s3417_plain_checked⟩

def s3418_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, true, false] 0 .none⟩
theorem s3418_zero_checked : check 384 s3418_zero_contract = true := by decide +kernel
def s3418_zero : CertifiedContract :=
  ⟨3418, 3424, 0, .none, s3418_zero_contract, 384, s3418_zero_checked⟩

def s3418_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3418_positive_checked : check 387 s3418_positive_contract = true := by decide +kernel
def s3418_positive : CertifiedContract :=
  ⟨3418, 3419, 1, (.dec 8), s3418_positive_contract, 387, s3418_positive_checked⟩

def s3419_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3419_plain_checked : check 382 s3419_plain_contract = true := by decide +kernel
def s3419_plain : CertifiedContract :=
  ⟨3419, 3420, 0, (.inc 5), s3419_plain_contract, 382, s3419_plain_checked⟩

def s3420_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, true, true, true] 0 .none⟩
theorem s3420_zero_checked : check 402 s3420_zero_contract = true := by decide +kernel
def s3420_zero : CertifiedContract :=
  ⟨3420, 3423, 0, .none, s3420_zero_contract, 402, s3420_zero_checked⟩

def s3420_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3420_positive_checked : check 405 s3420_positive_contract = true := by decide +kernel
def s3420_positive : CertifiedContract :=
  ⟨3420, 3421, 1, (.dec 8), s3420_positive_contract, 405, s3420_positive_checked⟩

def s3421_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3421_plain_checked : check 400 s3421_plain_contract = true := by decide +kernel
def s3421_plain : CertifiedContract :=
  ⟨3421, 3422, 0, (.inc 2), s3421_plain_contract, 400, s3421_plain_checked⟩

def s3422_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3422_plain_checked : check 110 s3422_plain_contract = true := by decide +kernel
def s3422_plain : CertifiedContract :=
  ⟨3422, 3420, 0, .none, s3422_plain_contract, 110, s3422_plain_checked⟩

def s3423_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, false, false] 0 .none⟩
theorem s3423_plain_checked : check 113 s3423_plain_contract = true := by decide +kernel
def s3423_plain : CertifiedContract :=
  ⟨3423, 3414, 0, .none, s3423_plain_contract, 113, s3423_plain_checked⟩

def s3424_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s3424_zero_checked : check 381 s3424_zero_contract = true := by decide +kernel
def s3424_zero : CertifiedContract :=
  ⟨3424, 3430, 0, .none, s3424_zero_contract, 381, s3424_zero_checked⟩

def s3424_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3424_positive_checked : check 369 s3424_positive_contract = true := by decide +kernel
def s3424_positive : CertifiedContract :=
  ⟨3424, 3425, 1, (.dec 5), s3424_positive_contract, 369, s3424_positive_checked⟩

def s3425_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3425_plain_checked : check 382 s3425_plain_contract = true := by decide +kernel
def s3425_plain : CertifiedContract :=
  ⟨3425, 3426, 0, (.inc 2), s3425_plain_contract, 382, s3425_plain_checked⟩

def s3426_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3426_plain_checked : check 385 s3426_plain_contract = true := by decide +kernel
def s3426_plain : CertifiedContract :=
  ⟨3426, 3427, 0, (.inc 2), s3426_plain_contract, 385, s3426_plain_checked⟩

def s3427_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3427_plain_checked : check 391 s3427_plain_contract = true := by decide +kernel
def s3427_plain : CertifiedContract :=
  ⟨3427, 3428, 0, (.inc 2), s3427_plain_contract, 391, s3427_plain_checked⟩

def s3428_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, true, true, true] 0 (.inc 2)⟩
theorem s3428_plain_checked : check 397 s3428_plain_contract = true := by decide +kernel
def s3428_plain : CertifiedContract :=
  ⟨3428, 3429, 0, (.inc 2), s3428_plain_contract, 397, s3428_plain_checked⟩

def s3429_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, true, false] 0 .none⟩
theorem s3429_plain_checked : check 98 s3429_plain_contract = true := by decide +kernel
def s3429_plain : CertifiedContract :=
  ⟨3429, 3424, 0, .none, s3429_plain_contract, 98, s3429_plain_checked⟩

def s3430_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, true, false] 0 .none⟩
theorem s3430_zero_checked : check 357 s3430_zero_contract = true := by decide +kernel
def s3430_zero : CertifiedContract :=
  ⟨3430, 3438, 0, .none, s3430_zero_contract, 357, s3430_zero_checked⟩

def s3430_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s3430_positive_checked : check 363 s3430_positive_contract = true := by decide +kernel
def s3430_positive : CertifiedContract :=
  ⟨3430, 3431, 1, (.dec 0), s3430_positive_contract, 363, s3430_positive_checked⟩

def s3431_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3431_plain_checked : check 373 s3431_plain_contract = true := by decide +kernel
def s3431_plain : CertifiedContract :=
  ⟨3431, 3432, 0, (.inc 5), s3431_plain_contract, 373, s3431_plain_checked⟩

def s3432_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3432_zero_checked : check 399 s3432_zero_contract = true := by decide +kernel
def s3432_zero : CertifiedContract :=
  ⟨3432, 3434, 0, .none, s3432_zero_contract, 399, s3432_zero_checked⟩

def s3432_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3432_positive_checked : check 405 s3432_positive_contract = true := by decide +kernel
def s3432_positive : CertifiedContract :=
  ⟨3432, 3433, 1, (.dec 8), s3432_positive_contract, 405, s3432_positive_checked⟩

def s3433_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s3433_plain_checked : check 110 s3433_plain_contract = true := by decide +kernel
def s3433_plain : CertifiedContract :=
  ⟨3433, 3437, 0, .none, s3433_plain_contract, 110, s3433_plain_checked⟩

def s3434_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s3434_zero_checked : check 411 s3434_zero_contract = true := by decide +kernel
def s3434_zero : CertifiedContract :=
  ⟨3434, 3437, 0, .none, s3434_zero_contract, 411, s3434_zero_checked⟩

def s3434_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3434_positive_checked : check 414 s3434_positive_contract = true := by decide +kernel
def s3434_positive : CertifiedContract :=
  ⟨3434, 3435, 1, (.dec 5), s3434_positive_contract, 414, s3434_positive_checked⟩

def s3435_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3435_plain_checked : check 418 s3435_plain_contract = true := by decide +kernel
def s3435_plain : CertifiedContract :=
  ⟨3435, 3436, 0, (.inc 8), s3435_plain_contract, 418, s3435_plain_checked⟩

def s3436_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3436_plain_checked : check 113 s3436_plain_contract = true := by decide +kernel
def s3436_plain : CertifiedContract :=
  ⟨3436, 3434, 0, .none, s3436_plain_contract, 113, s3436_plain_checked⟩

def s3437_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s3437_plain_checked : check 104 s3437_plain_contract = true := by decide +kernel
def s3437_plain : CertifiedContract :=
  ⟨3437, 3430, 0, .none, s3437_plain_contract, 104, s3437_plain_checked⟩

def s3438_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s3438_zero_checked : check 357 s3438_zero_contract = true := by decide +kernel
def s3438_zero : CertifiedContract :=
  ⟨3438, 3441, 0, .none, s3438_zero_contract, 357, s3438_zero_checked⟩

def s3438_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s3438_positive_checked : check 360 s3438_positive_contract = true := by decide +kernel
def s3438_positive : CertifiedContract :=
  ⟨3438, 3439, 1, (.dec 5), s3438_positive_contract, 360, s3438_positive_checked⟩

def s3439_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s3439_plain_checked : check 373 s3439_plain_contract = true := by decide +kernel
def s3439_plain : CertifiedContract :=
  ⟨3439, 3440, 0, (.inc 0), s3439_plain_contract, 373, s3439_plain_checked⟩

def s3440_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, false, true, false] 0 .none⟩
theorem s3440_plain_checked : check 98 s3440_plain_contract = true := by decide +kernel
def s3440_plain : CertifiedContract :=
  ⟨3440, 3438, 0, .none, s3440_plain_contract, 98, s3440_plain_checked⟩

def s3441_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, true, false] 0 .none⟩
theorem s3441_zero_checked : check 354 s3441_zero_contract = true := by decide +kernel
def s3441_zero : CertifiedContract :=
  ⟨3441, 3445, 0, .none, s3441_zero_contract, 354, s3441_zero_checked⟩

def s3441_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3441_positive_checked : check 360 s3441_positive_contract = true := by decide +kernel
def s3441_positive : CertifiedContract :=
  ⟨3441, 3442, 1, (.dec 2), s3441_positive_contract, 360, s3441_positive_checked⟩

def s3442_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3442_plain_checked : check 373 s3442_plain_contract = true := by decide +kernel
def s3442_plain : CertifiedContract :=
  ⟨3442, 3443, 0, (.inc 5), s3442_plain_contract, 373, s3442_plain_checked⟩

def s3443_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3443_plain_checked : check 400 s3443_plain_contract = true := by decide +kernel
def s3443_plain : CertifiedContract :=
  ⟨3443, 3444, 0, (.inc 8), s3443_plain_contract, 400, s3443_plain_checked⟩

def s3444_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s3444_plain_checked : check 107 s3444_plain_contract = true := by decide +kernel
def s3444_plain : CertifiedContract :=
  ⟨3444, 3441, 0, .none, s3444_plain_contract, 107, s3444_plain_checked⟩

def s3445_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s3445_zero_checked : check 375 s3445_zero_contract = true := by decide +kernel
def s3445_zero : CertifiedContract :=
  ⟨3445, 3451, 0, .none, s3445_zero_contract, 375, s3445_zero_checked⟩

def s3445_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3445_positive_checked : check 378 s3445_positive_contract = true := by decide +kernel
def s3445_positive : CertifiedContract :=
  ⟨3445, 3446, 1, (.dec 8), s3445_positive_contract, 378, s3445_positive_checked⟩

def s3446_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3446_plain_checked : check 373 s3446_plain_contract = true := by decide +kernel
def s3446_plain : CertifiedContract :=
  ⟨3446, 3447, 0, (.inc 5), s3446_plain_contract, 373, s3446_plain_checked⟩

def s3447_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, true, true, true] 0 .none⟩
theorem s3447_zero_checked : check 393 s3447_zero_contract = true := by decide +kernel
def s3447_zero : CertifiedContract :=
  ⟨3447, 3450, 0, .none, s3447_zero_contract, 393, s3447_zero_checked⟩

def s3447_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3447_positive_checked : check 396 s3447_positive_contract = true := by decide +kernel
def s3447_positive : CertifiedContract :=
  ⟨3447, 3448, 1, (.dec 8), s3447_positive_contract, 396, s3447_positive_checked⟩

def s3448_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3448_plain_checked : check 391 s3448_plain_contract = true := by decide +kernel
def s3448_plain : CertifiedContract :=
  ⟨3448, 3449, 0, (.inc 2), s3448_plain_contract, 391, s3448_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S069
