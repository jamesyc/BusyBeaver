module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S065
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s3203_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s3203_plain_checked : check 372 s3203_plain_contract = true := by decide +kernel
def s3203_plain : CertifiedContract :=
  ⟨3203, 3204, 0, (.inc 8), s3203_plain_contract, 372, s3203_plain_checked⟩

def s3204_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s3204_plain_checked : check 97 s3204_plain_contract = true := by decide +kernel
def s3204_plain : CertifiedContract :=
  ⟨3204, 3202, 0, .none, s3204_plain_contract, 97, s3204_plain_checked⟩

def s3205_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s3205_zero_checked : check 374 s3205_zero_contract = true := by decide +kernel
def s3205_zero : CertifiedContract :=
  ⟨3205, 3208, 0, .none, s3205_zero_contract, 374, s3205_zero_checked⟩

def s3205_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s3205_positive_checked : check 380 s3205_positive_contract = true := by decide +kernel
def s3205_positive : CertifiedContract :=
  ⟨3205, 3206, 1, (.dec 0), s3205_positive_contract, 380, s3205_positive_checked⟩

def s3206_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s3206_plain_checked : check 372 s3206_plain_contract = true := by decide +kernel
def s3206_plain : CertifiedContract :=
  ⟨3206, 3207, 0, (.inc 2), s3206_plain_contract, 372, s3206_plain_checked⟩

def s3207_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s3207_plain_checked : check 100 s3207_plain_contract = true := by decide +kernel
def s3207_plain : CertifiedContract :=
  ⟨3207, 3205, 0, .none, s3207_plain_contract, 100, s3207_plain_checked⟩

def s3208_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3208_zero_checked : check 380 s3208_zero_contract = true := by decide +kernel
def s3208_zero : CertifiedContract :=
  ⟨3208, 3212, 0, .none, s3208_zero_contract, 380, s3208_zero_checked⟩

def s3208_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3208_positive_checked : check 386 s3208_positive_contract = true := by decide +kernel
def s3208_positive : CertifiedContract :=
  ⟨3208, 3209, 1, (.dec 2), s3208_positive_contract, 386, s3208_positive_checked⟩

def s3209_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3209_plain_checked : check 399 s3209_plain_contract = true := by decide +kernel
def s3209_plain : CertifiedContract :=
  ⟨3209, 3210, 0, (.inc 5), s3209_plain_contract, 399, s3209_plain_checked⟩

def s3210_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3210_plain_checked : check 426 s3210_plain_contract = true := by decide +kernel
def s3210_plain : CertifiedContract :=
  ⟨3210, 3211, 0, (.inc 8), s3210_plain_contract, 426, s3210_plain_checked⟩

def s3211_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s3211_plain_checked : check 115 s3211_plain_contract = true := by decide +kernel
def s3211_plain : CertifiedContract :=
  ⟨3211, 3208, 0, .none, s3211_plain_contract, 115, s3211_plain_checked⟩

def s3212_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s3212_zero_checked : check 401 s3212_zero_contract = true := by decide +kernel
def s3212_zero : CertifiedContract :=
  ⟨3212, 3218, 0, .none, s3212_zero_contract, 401, s3212_zero_checked⟩

def s3212_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3212_positive_checked : check 404 s3212_positive_contract = true := by decide +kernel
def s3212_positive : CertifiedContract :=
  ⟨3212, 3213, 1, (.dec 8), s3212_positive_contract, 404, s3212_positive_checked⟩

def s3213_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3213_plain_checked : check 399 s3213_plain_contract = true := by decide +kernel
def s3213_plain : CertifiedContract :=
  ⟨3213, 3214, 0, (.inc 5), s3213_plain_contract, 399, s3213_plain_checked⟩

def s3214_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s3214_zero_checked : check 419 s3214_zero_contract = true := by decide +kernel
def s3214_zero : CertifiedContract :=
  ⟨3214, 3217, 0, .none, s3214_zero_contract, 419, s3214_zero_checked⟩

def s3214_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3214_positive_checked : check 422 s3214_positive_contract = true := by decide +kernel
def s3214_positive : CertifiedContract :=
  ⟨3214, 3215, 1, (.dec 8), s3214_positive_contract, 422, s3214_positive_checked⟩

def s3215_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3215_plain_checked : check 417 s3215_plain_contract = true := by decide +kernel
def s3215_plain : CertifiedContract :=
  ⟨3215, 3216, 0, (.inc 2), s3215_plain_contract, 417, s3215_plain_checked⟩

def s3216_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3216_plain_checked : check 115 s3216_plain_contract = true := by decide +kernel
def s3216_plain : CertifiedContract :=
  ⟨3216, 3214, 0, .none, s3216_plain_contract, 115, s3216_plain_checked⟩

def s3217_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s3217_plain_checked : check 118 s3217_plain_contract = true := by decide +kernel
def s3217_plain : CertifiedContract :=
  ⟨3217, 3208, 0, .none, s3217_plain_contract, 118, s3217_plain_checked⟩

def s3218_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false, false] 0 .none⟩
theorem s3218_zero_checked : check 389 s3218_zero_contract = true := by decide +kernel
def s3218_zero : CertifiedContract :=
  ⟨3218, 3221, 0, .none, s3218_zero_contract, 389, s3218_zero_checked⟩

def s3218_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s3218_positive_checked : check 386 s3218_positive_contract = true := by decide +kernel
def s3218_positive : CertifiedContract :=
  ⟨3218, 3219, 1, (.dec 5), s3218_positive_contract, 386, s3218_positive_checked⟩

def s3219_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s3219_plain_checked : check 399 s3219_plain_contract = true := by decide +kernel
def s3219_plain : CertifiedContract :=
  ⟨3219, 3220, 0, (.inc 0), s3219_plain_contract, 399, s3219_plain_checked⟩

def s3220_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s3220_plain_checked : check 106 s3220_plain_contract = true := by decide +kernel
def s3220_plain : CertifiedContract :=
  ⟨3220, 3218, 0, .none, s3220_plain_contract, 106, s3220_plain_checked⟩

def s3221_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s3221_zero_checked : check 353 s3221_zero_contract = true := by decide +kernel
def s3221_zero : CertifiedContract :=
  ⟨3221, 3225, 0, .none, s3221_zero_contract, 353, s3221_zero_checked⟩

def s3221_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s3221_positive_checked : check 359 s3221_positive_contract = true := by decide +kernel
def s3221_positive : CertifiedContract :=
  ⟨3221, 3222, 1, (.dec 7), s3221_positive_contract, 359, s3221_positive_checked⟩

def s3222_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s3222_plain_checked : check 363 s3222_plain_contract = true := by decide +kernel
def s3222_plain : CertifiedContract :=
  ⟨3222, 3223, 0, (.inc 2), s3222_plain_contract, 363, s3222_plain_checked⟩

def s3223_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3223_plain_checked : check 390 s3223_plain_contract = true := by decide +kernel
def s3223_plain : CertifiedContract :=
  ⟨3223, 3224, 0, (.inc 8), s3223_plain_contract, 390, s3223_plain_checked⟩

def s3224_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false, false] 0 .none⟩
theorem s3224_plain_checked : check 103 s3224_plain_contract = true := by decide +kernel
def s3224_plain : CertifiedContract :=
  ⟨3224, 3221, 0, .none, s3224_plain_contract, 103, s3224_plain_checked⟩

def s3225_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, false] 0 .none⟩
theorem s3225_zero_checked : check 362 s3225_zero_contract = true := by decide +kernel
def s3225_zero : CertifiedContract :=
  ⟨3225, 3228, 0, .none, s3225_zero_contract, 362, s3225_zero_checked⟩

def s3225_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s3225_positive_checked : check 359 s3225_positive_contract = true := by decide +kernel
def s3225_positive : CertifiedContract :=
  ⟨3225, 3226, 1, (.dec 8), s3225_positive_contract, 359, s3225_positive_checked⟩

def s3226_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s3226_plain_checked : check 390 s3226_plain_contract = true := by decide +kernel
def s3226_plain : CertifiedContract :=
  ⟨3226, 3227, 0, (.inc 7), s3226_plain_contract, 390, s3226_plain_checked⟩

def s3227_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s3227_plain_checked : check 97 s3227_plain_contract = true := by decide +kernel
def s3227_plain : CertifiedContract :=
  ⟨3227, 3225, 0, .none, s3227_plain_contract, 97, s3227_plain_checked⟩

def s3228_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, true, false] 0 .none⟩
theorem s3228_zero_checked : check 365 s3228_zero_contract = true := by decide +kernel
def s3228_zero : CertifiedContract :=
  ⟨3228, 3236, 0, .none, s3228_zero_contract, 365, s3228_zero_checked⟩

def s3228_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s3228_positive_checked : check 371 s3228_positive_contract = true := by decide +kernel
def s3228_positive : CertifiedContract :=
  ⟨3228, 3229, 1, (.dec 0), s3228_positive_contract, 371, s3228_positive_checked⟩

def s3229_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3229_plain_checked : check 381 s3229_plain_contract = true := by decide +kernel
def s3229_plain : CertifiedContract :=
  ⟨3229, 3230, 0, (.inc 5), s3229_plain_contract, 381, s3229_plain_checked⟩

def s3230_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3230_zero_checked : check 407 s3230_zero_contract = true := by decide +kernel
def s3230_zero : CertifiedContract :=
  ⟨3230, 3232, 0, .none, s3230_zero_contract, 407, s3230_zero_checked⟩

def s3230_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3230_positive_checked : check 413 s3230_positive_contract = true := by decide +kernel
def s3230_positive : CertifiedContract :=
  ⟨3230, 3231, 1, (.dec 8), s3230_positive_contract, 413, s3230_positive_checked⟩

def s3231_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s3231_plain_checked : check 112 s3231_plain_contract = true := by decide +kernel
def s3231_plain : CertifiedContract :=
  ⟨3231, 3235, 0, .none, s3231_plain_contract, 112, s3231_plain_checked⟩

def s3232_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s3232_zero_checked : check 419 s3232_zero_contract = true := by decide +kernel
def s3232_zero : CertifiedContract :=
  ⟨3232, 3235, 0, .none, s3232_zero_contract, 419, s3232_zero_checked⟩

def s3232_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3232_positive_checked : check 422 s3232_positive_contract = true := by decide +kernel
def s3232_positive : CertifiedContract :=
  ⟨3232, 3233, 1, (.dec 5), s3232_positive_contract, 422, s3232_positive_checked⟩

def s3233_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3233_plain_checked : check 426 s3233_plain_contract = true := by decide +kernel
def s3233_plain : CertifiedContract :=
  ⟨3233, 3234, 0, (.inc 8), s3233_plain_contract, 426, s3233_plain_checked⟩

def s3234_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3234_plain_checked : check 115 s3234_plain_contract = true := by decide +kernel
def s3234_plain : CertifiedContract :=
  ⟨3234, 3232, 0, .none, s3234_plain_contract, 115, s3234_plain_checked⟩

def s3235_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, false] 0 .none⟩
theorem s3235_plain_checked : check 106 s3235_plain_contract = true := by decide +kernel
def s3235_plain : CertifiedContract :=
  ⟨3235, 3228, 0, .none, s3235_plain_contract, 106, s3235_plain_checked⟩

def s3236_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s3236_zero_checked : check 365 s3236_zero_contract = true := by decide +kernel
def s3236_zero : CertifiedContract :=
  ⟨3236, 3239, 0, .none, s3236_zero_contract, 365, s3236_zero_checked⟩

def s3236_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s3236_positive_checked : check 368 s3236_positive_contract = true := by decide +kernel
def s3236_positive : CertifiedContract :=
  ⟨3236, 3237, 1, (.dec 5), s3236_positive_contract, 368, s3236_positive_checked⟩

def s3237_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s3237_plain_checked : check 381 s3237_plain_contract = true := by decide +kernel
def s3237_plain : CertifiedContract :=
  ⟨3237, 3238, 0, (.inc 0), s3237_plain_contract, 381, s3237_plain_checked⟩

def s3238_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, true, false] 0 .none⟩
theorem s3238_plain_checked : check 100 s3238_plain_contract = true := by decide +kernel
def s3238_plain : CertifiedContract :=
  ⟨3238, 3236, 0, .none, s3238_plain_contract, 100, s3238_plain_checked⟩

def s3239_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, false] 0 .none⟩
theorem s3239_zero_checked : check 362 s3239_zero_contract = true := by decide +kernel
def s3239_zero : CertifiedContract :=
  ⟨3239, 3243, 0, .none, s3239_zero_contract, 362, s3239_zero_checked⟩

def s3239_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3239_positive_checked : check 368 s3239_positive_contract = true := by decide +kernel
def s3239_positive : CertifiedContract :=
  ⟨3239, 3240, 1, (.dec 2), s3239_positive_contract, 368, s3239_positive_checked⟩

def s3240_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3240_plain_checked : check 381 s3240_plain_contract = true := by decide +kernel
def s3240_plain : CertifiedContract :=
  ⟨3240, 3241, 0, (.inc 5), s3240_plain_contract, 381, s3240_plain_checked⟩

def s3241_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3241_plain_checked : check 408 s3241_plain_contract = true := by decide +kernel
def s3241_plain : CertifiedContract :=
  ⟨3241, 3242, 0, (.inc 8), s3241_plain_contract, 408, s3241_plain_checked⟩

def s3242_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s3242_plain_checked : check 109 s3242_plain_contract = true := by decide +kernel
def s3242_plain : CertifiedContract :=
  ⟨3242, 3239, 0, .none, s3242_plain_contract, 109, s3242_plain_checked⟩

def s3243_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, false] 0 .none⟩
theorem s3243_zero_checked : check 383 s3243_zero_contract = true := by decide +kernel
def s3243_zero : CertifiedContract :=
  ⟨3243, 3249, 0, .none, s3243_zero_contract, 383, s3243_zero_checked⟩

def s3243_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3243_positive_checked : check 386 s3243_positive_contract = true := by decide +kernel
def s3243_positive : CertifiedContract :=
  ⟨3243, 3244, 1, (.dec 8), s3243_positive_contract, 386, s3243_positive_checked⟩

def s3244_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3244_plain_checked : check 381 s3244_plain_contract = true := by decide +kernel
def s3244_plain : CertifiedContract :=
  ⟨3244, 3245, 0, (.inc 5), s3244_plain_contract, 381, s3244_plain_checked⟩

def s3245_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, true] 0 .none⟩
theorem s3245_zero_checked : check 401 s3245_zero_contract = true := by decide +kernel
def s3245_zero : CertifiedContract :=
  ⟨3245, 3248, 0, .none, s3245_zero_contract, 401, s3245_zero_checked⟩

def s3245_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3245_positive_checked : check 404 s3245_positive_contract = true := by decide +kernel
def s3245_positive : CertifiedContract :=
  ⟨3245, 3246, 1, (.dec 8), s3245_positive_contract, 404, s3245_positive_checked⟩

def s3246_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3246_plain_checked : check 399 s3246_plain_contract = true := by decide +kernel
def s3246_plain : CertifiedContract :=
  ⟨3246, 3247, 0, (.inc 2), s3246_plain_contract, 399, s3246_plain_checked⟩

def s3247_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3247_plain_checked : check 109 s3247_plain_contract = true := by decide +kernel
def s3247_plain : CertifiedContract :=
  ⟨3247, 3245, 0, .none, s3247_plain_contract, 109, s3247_plain_checked⟩

def s3248_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s3248_plain_checked : check 112 s3248_plain_contract = true := by decide +kernel
def s3248_plain : CertifiedContract :=
  ⟨3248, 3239, 0, .none, s3248_plain_contract, 112, s3248_plain_checked⟩

def s3249_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, true] 0 .none⟩
theorem s3249_zero_checked : check 368 s3249_zero_contract = true := by decide +kernel
def s3249_zero : CertifiedContract :=
  ⟨3249, 3255, 0, .none, s3249_zero_contract, 368, s3249_zero_checked⟩

def s3249_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3249_positive_checked : check 368 s3249_positive_contract = true := by decide +kernel
def s3249_positive : CertifiedContract :=
  ⟨3249, 3250, 1, (.dec 5), s3249_positive_contract, 368, s3249_positive_checked⟩

def s3250_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3250_plain_checked : check 381 s3250_plain_contract = true := by decide +kernel
def s3250_plain : CertifiedContract :=
  ⟨3250, 3251, 0, (.inc 2), s3250_plain_contract, 381, s3250_plain_checked⟩

def s3251_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3251_plain_checked : check 384 s3251_plain_contract = true := by decide +kernel
def s3251_plain : CertifiedContract :=
  ⟨3251, 3252, 0, (.inc 2), s3251_plain_contract, 384, s3251_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s3203_plain,
  s3204_plain,
  s3205_zero,
  s3205_positive,
  s3206_plain,
  s3207_plain,
  s3208_zero,
  s3208_positive,
  s3209_plain,
  s3210_plain,
  s3211_plain,
  s3212_zero,
  s3212_positive,
  s3213_plain,
  s3214_zero,
  s3214_positive,
  s3215_plain,
  s3216_plain,
  s3217_plain,
  s3218_zero,
  s3218_positive,
  s3219_plain,
  s3220_plain,
  s3221_zero,
  s3221_positive,
  s3222_plain,
  s3223_plain,
  s3224_plain,
  s3225_zero,
  s3225_positive,
  s3226_plain,
  s3227_plain,
  s3228_zero,
  s3228_positive,
  s3229_plain,
  s3230_zero,
  s3230_positive,
  s3231_plain,
  s3232_zero,
  s3232_positive,
  s3233_plain,
  s3234_plain,
  s3235_plain,
  s3236_zero,
  s3236_positive,
  s3237_plain,
  s3238_plain,
  s3239_zero,
  s3239_positive,
  s3240_plain,
  s3241_plain,
  s3242_plain,
  s3243_zero,
  s3243_positive,
  s3244_plain,
  s3245_zero,
  s3245_positive,
  s3246_plain,
  s3247_plain,
  s3248_plain,
  s3249_zero,
  s3249_positive,
  s3250_plain,
  s3251_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S065
