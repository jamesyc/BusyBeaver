module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S065
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s3203_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s3203_plain_checked : check 373 s3203_plain_contract = true := by decide +kernel
def s3203_plain : CertifiedContract :=
  ⟨3203, 3204, 0, (.inc 8), s3203_plain_contract, 373, s3203_plain_checked⟩

def s3204_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s3204_plain_checked : check 98 s3204_plain_contract = true := by decide +kernel
def s3204_plain : CertifiedContract :=
  ⟨3204, 3202, 0, .none, s3204_plain_contract, 98, s3204_plain_checked⟩

def s3205_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s3205_zero_checked : check 375 s3205_zero_contract = true := by decide +kernel
def s3205_zero : CertifiedContract :=
  ⟨3205, 3208, 0, .none, s3205_zero_contract, 375, s3205_zero_checked⟩

def s3205_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s3205_positive_checked : check 381 s3205_positive_contract = true := by decide +kernel
def s3205_positive : CertifiedContract :=
  ⟨3205, 3206, 1, (.dec 0), s3205_positive_contract, 381, s3205_positive_checked⟩

def s3206_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s3206_plain_checked : check 373 s3206_plain_contract = true := by decide +kernel
def s3206_plain : CertifiedContract :=
  ⟨3206, 3207, 0, (.inc 2), s3206_plain_contract, 373, s3206_plain_checked⟩

def s3207_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s3207_plain_checked : check 101 s3207_plain_contract = true := by decide +kernel
def s3207_plain : CertifiedContract :=
  ⟨3207, 3205, 0, .none, s3207_plain_contract, 101, s3207_plain_checked⟩

def s3208_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3208_zero_checked : check 381 s3208_zero_contract = true := by decide +kernel
def s3208_zero : CertifiedContract :=
  ⟨3208, 3212, 0, .none, s3208_zero_contract, 381, s3208_zero_checked⟩

def s3208_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3208_positive_checked : check 387 s3208_positive_contract = true := by decide +kernel
def s3208_positive : CertifiedContract :=
  ⟨3208, 3209, 1, (.dec 2), s3208_positive_contract, 387, s3208_positive_checked⟩

def s3209_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3209_plain_checked : check 400 s3209_plain_contract = true := by decide +kernel
def s3209_plain : CertifiedContract :=
  ⟨3209, 3210, 0, (.inc 5), s3209_plain_contract, 400, s3209_plain_checked⟩

def s3210_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3210_plain_checked : check 427 s3210_plain_contract = true := by decide +kernel
def s3210_plain : CertifiedContract :=
  ⟨3210, 3211, 0, (.inc 8), s3210_plain_contract, 427, s3210_plain_checked⟩

def s3211_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s3211_plain_checked : check 116 s3211_plain_contract = true := by decide +kernel
def s3211_plain : CertifiedContract :=
  ⟨3211, 3208, 0, .none, s3211_plain_contract, 116, s3211_plain_checked⟩

def s3212_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s3212_zero_checked : check 402 s3212_zero_contract = true := by decide +kernel
def s3212_zero : CertifiedContract :=
  ⟨3212, 3218, 0, .none, s3212_zero_contract, 402, s3212_zero_checked⟩

def s3212_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3212_positive_checked : check 405 s3212_positive_contract = true := by decide +kernel
def s3212_positive : CertifiedContract :=
  ⟨3212, 3213, 1, (.dec 8), s3212_positive_contract, 405, s3212_positive_checked⟩

def s3213_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3213_plain_checked : check 400 s3213_plain_contract = true := by decide +kernel
def s3213_plain : CertifiedContract :=
  ⟨3213, 3214, 0, (.inc 5), s3213_plain_contract, 400, s3213_plain_checked⟩

def s3214_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s3214_zero_checked : check 420 s3214_zero_contract = true := by decide +kernel
def s3214_zero : CertifiedContract :=
  ⟨3214, 3217, 0, .none, s3214_zero_contract, 420, s3214_zero_checked⟩

def s3214_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3214_positive_checked : check 423 s3214_positive_contract = true := by decide +kernel
def s3214_positive : CertifiedContract :=
  ⟨3214, 3215, 1, (.dec 8), s3214_positive_contract, 423, s3214_positive_checked⟩

def s3215_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3215_plain_checked : check 418 s3215_plain_contract = true := by decide +kernel
def s3215_plain : CertifiedContract :=
  ⟨3215, 3216, 0, (.inc 2), s3215_plain_contract, 418, s3215_plain_checked⟩

def s3216_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3216_plain_checked : check 116 s3216_plain_contract = true := by decide +kernel
def s3216_plain : CertifiedContract :=
  ⟨3216, 3214, 0, .none, s3216_plain_contract, 116, s3216_plain_checked⟩

def s3217_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s3217_plain_checked : check 119 s3217_plain_contract = true := by decide +kernel
def s3217_plain : CertifiedContract :=
  ⟨3217, 3208, 0, .none, s3217_plain_contract, 119, s3217_plain_checked⟩

def s3218_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false, false] 0 .none⟩
theorem s3218_zero_checked : check 390 s3218_zero_contract = true := by decide +kernel
def s3218_zero : CertifiedContract :=
  ⟨3218, 3221, 0, .none, s3218_zero_contract, 390, s3218_zero_checked⟩

def s3218_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s3218_positive_checked : check 387 s3218_positive_contract = true := by decide +kernel
def s3218_positive : CertifiedContract :=
  ⟨3218, 3219, 1, (.dec 5), s3218_positive_contract, 387, s3218_positive_checked⟩

def s3219_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s3219_plain_checked : check 400 s3219_plain_contract = true := by decide +kernel
def s3219_plain : CertifiedContract :=
  ⟨3219, 3220, 0, (.inc 0), s3219_plain_contract, 400, s3219_plain_checked⟩

def s3220_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s3220_plain_checked : check 107 s3220_plain_contract = true := by decide +kernel
def s3220_plain : CertifiedContract :=
  ⟨3220, 3218, 0, .none, s3220_plain_contract, 107, s3220_plain_checked⟩

def s3221_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s3221_zero_checked : check 354 s3221_zero_contract = true := by decide +kernel
def s3221_zero : CertifiedContract :=
  ⟨3221, 3225, 0, .none, s3221_zero_contract, 354, s3221_zero_checked⟩

def s3221_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s3221_positive_checked : check 360 s3221_positive_contract = true := by decide +kernel
def s3221_positive : CertifiedContract :=
  ⟨3221, 3222, 1, (.dec 7), s3221_positive_contract, 360, s3221_positive_checked⟩

def s3222_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s3222_plain_checked : check 364 s3222_plain_contract = true := by decide +kernel
def s3222_plain : CertifiedContract :=
  ⟨3222, 3223, 0, (.inc 2), s3222_plain_contract, 364, s3222_plain_checked⟩

def s3223_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3223_plain_checked : check 391 s3223_plain_contract = true := by decide +kernel
def s3223_plain : CertifiedContract :=
  ⟨3223, 3224, 0, (.inc 8), s3223_plain_contract, 391, s3223_plain_checked⟩

def s3224_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false, false] 0 .none⟩
theorem s3224_plain_checked : check 104 s3224_plain_contract = true := by decide +kernel
def s3224_plain : CertifiedContract :=
  ⟨3224, 3221, 0, .none, s3224_plain_contract, 104, s3224_plain_checked⟩

def s3225_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, false] 0 .none⟩
theorem s3225_zero_checked : check 363 s3225_zero_contract = true := by decide +kernel
def s3225_zero : CertifiedContract :=
  ⟨3225, 3228, 0, .none, s3225_zero_contract, 363, s3225_zero_checked⟩

def s3225_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s3225_positive_checked : check 360 s3225_positive_contract = true := by decide +kernel
def s3225_positive : CertifiedContract :=
  ⟨3225, 3226, 1, (.dec 8), s3225_positive_contract, 360, s3225_positive_checked⟩

def s3226_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s3226_plain_checked : check 391 s3226_plain_contract = true := by decide +kernel
def s3226_plain : CertifiedContract :=
  ⟨3226, 3227, 0, (.inc 7), s3226_plain_contract, 391, s3226_plain_checked⟩

def s3227_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s3227_plain_checked : check 98 s3227_plain_contract = true := by decide +kernel
def s3227_plain : CertifiedContract :=
  ⟨3227, 3225, 0, .none, s3227_plain_contract, 98, s3227_plain_checked⟩

def s3228_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, true, false] 0 .none⟩
theorem s3228_zero_checked : check 366 s3228_zero_contract = true := by decide +kernel
def s3228_zero : CertifiedContract :=
  ⟨3228, 3236, 0, .none, s3228_zero_contract, 366, s3228_zero_checked⟩

def s3228_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s3228_positive_checked : check 372 s3228_positive_contract = true := by decide +kernel
def s3228_positive : CertifiedContract :=
  ⟨3228, 3229, 1, (.dec 0), s3228_positive_contract, 372, s3228_positive_checked⟩

def s3229_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3229_plain_checked : check 382 s3229_plain_contract = true := by decide +kernel
def s3229_plain : CertifiedContract :=
  ⟨3229, 3230, 0, (.inc 5), s3229_plain_contract, 382, s3229_plain_checked⟩

def s3230_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3230_zero_checked : check 408 s3230_zero_contract = true := by decide +kernel
def s3230_zero : CertifiedContract :=
  ⟨3230, 3232, 0, .none, s3230_zero_contract, 408, s3230_zero_checked⟩

def s3230_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3230_positive_checked : check 414 s3230_positive_contract = true := by decide +kernel
def s3230_positive : CertifiedContract :=
  ⟨3230, 3231, 1, (.dec 8), s3230_positive_contract, 414, s3230_positive_checked⟩

def s3231_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s3231_plain_checked : check 113 s3231_plain_contract = true := by decide +kernel
def s3231_plain : CertifiedContract :=
  ⟨3231, 3235, 0, .none, s3231_plain_contract, 113, s3231_plain_checked⟩

def s3232_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s3232_zero_checked : check 420 s3232_zero_contract = true := by decide +kernel
def s3232_zero : CertifiedContract :=
  ⟨3232, 3235, 0, .none, s3232_zero_contract, 420, s3232_zero_checked⟩

def s3232_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3232_positive_checked : check 423 s3232_positive_contract = true := by decide +kernel
def s3232_positive : CertifiedContract :=
  ⟨3232, 3233, 1, (.dec 5), s3232_positive_contract, 423, s3232_positive_checked⟩

def s3233_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3233_plain_checked : check 427 s3233_plain_contract = true := by decide +kernel
def s3233_plain : CertifiedContract :=
  ⟨3233, 3234, 0, (.inc 8), s3233_plain_contract, 427, s3233_plain_checked⟩

def s3234_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3234_plain_checked : check 116 s3234_plain_contract = true := by decide +kernel
def s3234_plain : CertifiedContract :=
  ⟨3234, 3232, 0, .none, s3234_plain_contract, 116, s3234_plain_checked⟩

def s3235_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, false, false] 0 .none⟩
theorem s3235_plain_checked : check 107 s3235_plain_contract = true := by decide +kernel
def s3235_plain : CertifiedContract :=
  ⟨3235, 3228, 0, .none, s3235_plain_contract, 107, s3235_plain_checked⟩

def s3236_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s3236_zero_checked : check 366 s3236_zero_contract = true := by decide +kernel
def s3236_zero : CertifiedContract :=
  ⟨3236, 3239, 0, .none, s3236_zero_contract, 366, s3236_zero_checked⟩

def s3236_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s3236_positive_checked : check 369 s3236_positive_contract = true := by decide +kernel
def s3236_positive : CertifiedContract :=
  ⟨3236, 3237, 1, (.dec 5), s3236_positive_contract, 369, s3236_positive_checked⟩

def s3237_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s3237_plain_checked : check 382 s3237_plain_contract = true := by decide +kernel
def s3237_plain : CertifiedContract :=
  ⟨3237, 3238, 0, (.inc 0), s3237_plain_contract, 382, s3237_plain_checked⟩

def s3238_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, false, true, false] 0 .none⟩
theorem s3238_plain_checked : check 101 s3238_plain_contract = true := by decide +kernel
def s3238_plain : CertifiedContract :=
  ⟨3238, 3236, 0, .none, s3238_plain_contract, 101, s3238_plain_checked⟩

def s3239_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, false] 0 .none⟩
theorem s3239_zero_checked : check 363 s3239_zero_contract = true := by decide +kernel
def s3239_zero : CertifiedContract :=
  ⟨3239, 3243, 0, .none, s3239_zero_contract, 363, s3239_zero_checked⟩

def s3239_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3239_positive_checked : check 369 s3239_positive_contract = true := by decide +kernel
def s3239_positive : CertifiedContract :=
  ⟨3239, 3240, 1, (.dec 2), s3239_positive_contract, 369, s3239_positive_checked⟩

def s3240_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3240_plain_checked : check 382 s3240_plain_contract = true := by decide +kernel
def s3240_plain : CertifiedContract :=
  ⟨3240, 3241, 0, (.inc 5), s3240_plain_contract, 382, s3240_plain_checked⟩

def s3241_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3241_plain_checked : check 409 s3241_plain_contract = true := by decide +kernel
def s3241_plain : CertifiedContract :=
  ⟨3241, 3242, 0, (.inc 8), s3241_plain_contract, 409, s3241_plain_checked⟩

def s3242_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s3242_plain_checked : check 110 s3242_plain_contract = true := by decide +kernel
def s3242_plain : CertifiedContract :=
  ⟨3242, 3239, 0, .none, s3242_plain_contract, 110, s3242_plain_checked⟩

def s3243_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, false] 0 .none⟩
theorem s3243_zero_checked : check 384 s3243_zero_contract = true := by decide +kernel
def s3243_zero : CertifiedContract :=
  ⟨3243, 3249, 0, .none, s3243_zero_contract, 384, s3243_zero_checked⟩

def s3243_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3243_positive_checked : check 387 s3243_positive_contract = true := by decide +kernel
def s3243_positive : CertifiedContract :=
  ⟨3243, 3244, 1, (.dec 8), s3243_positive_contract, 387, s3243_positive_checked⟩

def s3244_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3244_plain_checked : check 382 s3244_plain_contract = true := by decide +kernel
def s3244_plain : CertifiedContract :=
  ⟨3244, 3245, 0, (.inc 5), s3244_plain_contract, 382, s3244_plain_checked⟩

def s3245_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, true] 0 .none⟩
theorem s3245_zero_checked : check 402 s3245_zero_contract = true := by decide +kernel
def s3245_zero : CertifiedContract :=
  ⟨3245, 3248, 0, .none, s3245_zero_contract, 402, s3245_zero_checked⟩

def s3245_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3245_positive_checked : check 405 s3245_positive_contract = true := by decide +kernel
def s3245_positive : CertifiedContract :=
  ⟨3245, 3246, 1, (.dec 8), s3245_positive_contract, 405, s3245_positive_checked⟩

def s3246_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3246_plain_checked : check 400 s3246_plain_contract = true := by decide +kernel
def s3246_plain : CertifiedContract :=
  ⟨3246, 3247, 0, (.inc 2), s3246_plain_contract, 400, s3246_plain_checked⟩

def s3247_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3247_plain_checked : check 110 s3247_plain_contract = true := by decide +kernel
def s3247_plain : CertifiedContract :=
  ⟨3247, 3245, 0, .none, s3247_plain_contract, 110, s3247_plain_checked⟩

def s3248_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s3248_plain_checked : check 113 s3248_plain_contract = true := by decide +kernel
def s3248_plain : CertifiedContract :=
  ⟨3248, 3239, 0, .none, s3248_plain_contract, 113, s3248_plain_checked⟩

def s3249_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, true] 0 .none⟩
theorem s3249_zero_checked : check 369 s3249_zero_contract = true := by decide +kernel
def s3249_zero : CertifiedContract :=
  ⟨3249, 3255, 0, .none, s3249_zero_contract, 369, s3249_zero_checked⟩

def s3249_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3249_positive_checked : check 369 s3249_positive_contract = true := by decide +kernel
def s3249_positive : CertifiedContract :=
  ⟨3249, 3250, 1, (.dec 5), s3249_positive_contract, 369, s3249_positive_checked⟩

def s3250_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3250_plain_checked : check 382 s3250_plain_contract = true := by decide +kernel
def s3250_plain : CertifiedContract :=
  ⟨3250, 3251, 0, (.inc 2), s3250_plain_contract, 382, s3250_plain_checked⟩

def s3251_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3251_plain_checked : check 385 s3251_plain_contract = true := by decide +kernel
def s3251_plain : CertifiedContract :=
  ⟨3251, 3252, 0, (.inc 2), s3251_plain_contract, 385, s3251_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S065
