import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S004
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s0193_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0193_positive_checked : check 306 s0193_positive_contract = true := by decide +kernel
def s0193_positive : CertifiedContract :=
  ⟨193, 194, 1, (.dec 5), s0193_positive_contract, 306, s0193_positive_checked⟩

def s0194_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0194_plain_checked : check 319 s0194_plain_contract = true := by decide +kernel
def s0194_plain : CertifiedContract :=
  ⟨194, 195, 0, (.inc 2), s0194_plain_contract, 319, s0194_plain_checked⟩

def s0195_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0195_plain_checked : check 322 s0195_plain_contract = true := by decide +kernel
def s0195_plain : CertifiedContract :=
  ⟨195, 196, 0, (.inc 2), s0195_plain_contract, 322, s0195_plain_checked⟩

def s0196_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0196_plain_checked : check 328 s0196_plain_contract = true := by decide +kernel
def s0196_plain : CertifiedContract :=
  ⟨196, 197, 0, (.inc 2), s0196_plain_contract, 328, s0196_plain_checked⟩

def s0197_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s0197_plain_checked : check 334 s0197_plain_contract = true := by decide +kernel
def s0197_plain : CertifiedContract :=
  ⟨197, 198, 0, (.inc 2), s0197_plain_contract, 334, s0197_plain_checked⟩

def s0198_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s0198_plain_checked : check 77 s0198_plain_contract = true := by decide +kernel
def s0198_plain : CertifiedContract :=
  ⟨198, 193, 0, .none, s0198_plain_contract, 77, s0198_plain_checked⟩

def s0199_zero_contract : Contract :=
  ⟨(some (1, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, true, false] 0 .none⟩
theorem s0199_zero_checked : check 312 s0199_zero_contract = true := by decide +kernel
def s0199_zero : CertifiedContract :=
  ⟨199, 207, 0, .none, s0199_zero_contract, 312, s0199_zero_checked⟩

def s0199_positive_contract : Contract :=
  ⟨(some (1, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, false] 1 (.dec 1)⟩
theorem s0199_positive_checked : check 318 s0199_positive_contract = true := by decide +kernel
def s0199_positive : CertifiedContract :=
  ⟨199, 200, 1, (.dec 1), s0199_positive_contract, 318, s0199_positive_checked⟩

def s0200_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0200_plain_checked : check 310 s0200_plain_contract = true := by decide +kernel
def s0200_plain : CertifiedContract :=
  ⟨200, 201, 0, (.inc 5), s0200_plain_contract, 310, s0200_plain_checked⟩

def s0201_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0201_zero_checked : check 336 s0201_zero_contract = true := by decide +kernel
def s0201_zero : CertifiedContract :=
  ⟨201, 203, 0, .none, s0201_zero_contract, 336, s0201_zero_checked⟩

def s0201_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0201_positive_checked : check 342 s0201_positive_contract = true := by decide +kernel
def s0201_positive : CertifiedContract :=
  ⟨201, 202, 1, (.dec 8), s0201_positive_contract, 342, s0201_positive_checked⟩

def s0202_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s0202_plain_checked : check 89 s0202_plain_contract = true := by decide +kernel
def s0202_plain : CertifiedContract :=
  ⟨202, 206, 0, .none, s0202_plain_contract, 89, s0202_plain_checked⟩

def s0203_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s0203_zero_checked : check 348 s0203_zero_contract = true := by decide +kernel
def s0203_zero : CertifiedContract :=
  ⟨203, 206, 0, .none, s0203_zero_contract, 348, s0203_zero_checked⟩

def s0203_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0203_positive_checked : check 351 s0203_positive_contract = true := by decide +kernel
def s0203_positive : CertifiedContract :=
  ⟨203, 204, 1, (.dec 5), s0203_positive_contract, 351, s0203_positive_checked⟩

def s0204_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0204_plain_checked : check 355 s0204_plain_contract = true := by decide +kernel
def s0204_plain : CertifiedContract :=
  ⟨204, 205, 0, (.inc 8), s0204_plain_contract, 355, s0204_plain_checked⟩

def s0205_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0205_plain_checked : check 92 s0205_plain_contract = true := by decide +kernel
def s0205_plain : CertifiedContract :=
  ⟨205, 203, 0, .none, s0205_plain_contract, 92, s0205_plain_checked⟩

def s0206_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, false] 0 .none⟩
theorem s0206_plain_checked : check 83 s0206_plain_contract = true := by decide +kernel
def s0206_plain : CertifiedContract :=
  ⟨206, 199, 0, .none, s0206_plain_contract, 83, s0206_plain_checked⟩

def s0207_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, false, false] 0 .none⟩
theorem s0207_zero_checked : check 312 s0207_zero_contract = true := by decide +kernel
def s0207_zero : CertifiedContract :=
  ⟨207, 210, 0, .none, s0207_zero_contract, 312, s0207_zero_checked⟩

def s0207_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0207_positive_checked : check 315 s0207_positive_contract = true := by decide +kernel
def s0207_positive : CertifiedContract :=
  ⟨207, 208, 1, (.dec 5), s0207_positive_contract, 315, s0207_positive_checked⟩

def s0208_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, true, true, true] 0 (.inc 1)⟩
theorem s0208_plain_checked : check 328 s0208_plain_contract = true := by decide +kernel
def s0208_plain : CertifiedContract :=
  ⟨208, 209, 0, (.inc 1), s0208_plain_contract, 328, s0208_plain_checked⟩

def s0209_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, true, false] 0 .none⟩
theorem s0209_plain_checked : check 86 s0209_plain_contract = true := by decide +kernel
def s0209_plain : CertifiedContract :=
  ⟨209, 207, 0, .none, s0209_plain_contract, 86, s0209_plain_checked⟩

def s0210_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0210_zero_checked : check 300 s0210_zero_contract = true := by decide +kernel
def s0210_zero : CertifiedContract :=
  ⟨210, 213, 0, .none, s0210_zero_contract, 300, s0210_zero_checked⟩

def s0210_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, false, true, false] 1 (.dec 8)⟩
theorem s0210_positive_checked : check 306 s0210_positive_contract = true := by decide +kernel
def s0210_positive : CertifiedContract :=
  ⟨210, 211, 1, (.dec 8), s0210_positive_contract, 306, s0210_positive_checked⟩

def s0211_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, false, true, true] 0 (.inc 3)⟩
theorem s0211_plain_checked : check 322 s0211_plain_contract = true := by decide +kernel
def s0211_plain : CertifiedContract :=
  ⟨211, 212, 0, (.inc 3), s0211_plain_contract, 322, s0211_plain_checked⟩

def s0212_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, false, false] 0 .none⟩
theorem s0212_plain_checked : check 80 s0212_plain_contract = true := by decide +kernel
def s0212_plain : CertifiedContract :=
  ⟨212, 210, 0, .none, s0212_plain_contract, 80, s0212_plain_checked⟩

def s0213_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, false] 0 .none⟩
theorem s0213_zero_checked : check 318 s0213_zero_contract = true := by decide +kernel
def s0213_zero : CertifiedContract :=
  ⟨213, 216, 0, .none, s0213_zero_contract, 318, s0213_zero_checked⟩

def s0213_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0213_positive_checked : check 324 s0213_positive_contract = true := by decide +kernel
def s0213_positive : CertifiedContract :=
  ⟨213, 214, 1, (.dec 2), s0213_positive_contract, 324, s0213_positive_checked⟩

def s0214_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, false, true, true] 0 (.inc 8)⟩
theorem s0214_plain_checked : check 337 s0214_plain_contract = true := by decide +kernel
def s0214_plain : CertifiedContract :=
  ⟨214, 215, 0, (.inc 8), s0214_plain_contract, 337, s0214_plain_checked⟩

def s0215_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0215_plain_checked : check 86 s0215_plain_contract = true := by decide +kernel
def s0215_plain : CertifiedContract :=
  ⟨215, 213, 0, .none, s0215_plain_contract, 86, s0215_plain_checked⟩

def s0216_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0216_zero_checked : check 339 s0216_zero_contract = true := by decide +kernel
def s0216_zero : CertifiedContract :=
  ⟨216, 219, 0, .none, s0216_zero_contract, 339, s0216_zero_checked⟩

def s0216_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0216_positive_checked : check 345 s0216_positive_contract = true := by decide +kernel
def s0216_positive : CertifiedContract :=
  ⟨216, 217, 1, (.dec 0), s0216_positive_contract, 345, s0216_positive_checked⟩

def s0217_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0217_plain_checked : check 337 s0217_plain_contract = true := by decide +kernel
def s0217_plain : CertifiedContract :=
  ⟨217, 218, 0, (.inc 2), s0217_plain_contract, 337, s0217_plain_checked⟩

def s0218_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, false] 0 .none⟩
theorem s0218_plain_checked : check 89 s0218_plain_contract = true := by decide +kernel
def s0218_plain : CertifiedContract :=
  ⟨218, 216, 0, .none, s0218_plain_contract, 89, s0218_plain_checked⟩

def s0219_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0219_zero_checked : check 345 s0219_zero_contract = true := by decide +kernel
def s0219_zero : CertifiedContract :=
  ⟨219, 223, 0, .none, s0219_zero_contract, 345, s0219_zero_checked⟩

def s0219_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0219_positive_checked : check 351 s0219_positive_contract = true := by decide +kernel
def s0219_positive : CertifiedContract :=
  ⟨219, 220, 1, (.dec 2), s0219_positive_contract, 351, s0219_positive_checked⟩

def s0220_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0220_plain_checked : check 364 s0220_plain_contract = true := by decide +kernel
def s0220_plain : CertifiedContract :=
  ⟨220, 221, 0, (.inc 5), s0220_plain_contract, 364, s0220_plain_checked⟩

def s0221_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0221_plain_checked : check 391 s0221_plain_contract = true := by decide +kernel
def s0221_plain : CertifiedContract :=
  ⟨221, 222, 0, (.inc 8), s0221_plain_contract, 391, s0221_plain_checked⟩

def s0222_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0222_plain_checked : check 104 s0222_plain_contract = true := by decide +kernel
def s0222_plain : CertifiedContract :=
  ⟨222, 219, 0, .none, s0222_plain_contract, 104, s0222_plain_checked⟩

def s0223_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s0223_zero_checked : check 366 s0223_zero_contract = true := by decide +kernel
def s0223_zero : CertifiedContract :=
  ⟨223, 229, 0, .none, s0223_zero_contract, 366, s0223_zero_checked⟩

def s0223_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0223_positive_checked : check 369 s0223_positive_contract = true := by decide +kernel
def s0223_positive : CertifiedContract :=
  ⟨223, 224, 1, (.dec 8), s0223_positive_contract, 369, s0223_positive_checked⟩

def s0224_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0224_plain_checked : check 364 s0224_plain_contract = true := by decide +kernel
def s0224_plain : CertifiedContract :=
  ⟨224, 225, 0, (.inc 5), s0224_plain_contract, 364, s0224_plain_checked⟩

def s0225_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s0225_zero_checked : check 384 s0225_zero_contract = true := by decide +kernel
def s0225_zero : CertifiedContract :=
  ⟨225, 228, 0, .none, s0225_zero_contract, 384, s0225_zero_checked⟩

def s0225_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0225_positive_checked : check 387 s0225_positive_contract = true := by decide +kernel
def s0225_positive : CertifiedContract :=
  ⟨225, 226, 1, (.dec 8), s0225_positive_contract, 387, s0225_positive_checked⟩

def s0226_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0226_plain_checked : check 382 s0226_plain_contract = true := by decide +kernel
def s0226_plain : CertifiedContract :=
  ⟨226, 227, 0, (.inc 2), s0226_plain_contract, 382, s0226_plain_checked⟩

def s0227_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0227_plain_checked : check 104 s0227_plain_contract = true := by decide +kernel
def s0227_plain : CertifiedContract :=
  ⟨227, 225, 0, .none, s0227_plain_contract, 104, s0227_plain_checked⟩

def s0228_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0228_plain_checked : check 107 s0228_plain_contract = true := by decide +kernel
def s0228_plain : CertifiedContract :=
  ⟨228, 219, 0, .none, s0228_plain_contract, 107, s0228_plain_checked⟩

def s0229_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, false] 0 .none⟩
theorem s0229_zero_checked : check 354 s0229_zero_contract = true := by decide +kernel
def s0229_zero : CertifiedContract :=
  ⟨229, 232, 0, .none, s0229_zero_contract, 354, s0229_zero_checked⟩

def s0229_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0229_positive_checked : check 351 s0229_positive_contract = true := by decide +kernel
def s0229_positive : CertifiedContract :=
  ⟨229, 230, 1, (.dec 5), s0229_positive_contract, 351, s0229_positive_checked⟩

def s0230_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0230_plain_checked : check 364 s0230_plain_contract = true := by decide +kernel
def s0230_plain : CertifiedContract :=
  ⟨230, 231, 0, (.inc 0), s0230_plain_contract, 364, s0230_plain_checked⟩

def s0231_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s0231_plain_checked : check 95 s0231_plain_contract = true := by decide +kernel
def s0231_plain : CertifiedContract :=
  ⟨231, 229, 0, .none, s0231_plain_contract, 95, s0231_plain_checked⟩

def s0232_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, true, false] 0 .none⟩
theorem s0232_zero_checked : check 318 s0232_zero_contract = true := by decide +kernel
def s0232_zero : CertifiedContract :=
  ⟨232, 236, 0, .none, s0232_zero_contract, 318, s0232_zero_checked⟩

def s0232_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, true, false] 1 (.dec 3)⟩
theorem s0232_positive_checked : check 324 s0232_positive_contract = true := by decide +kernel
def s0232_positive : CertifiedContract :=
  ⟨232, 233, 1, (.dec 3), s0232_positive_contract, 324, s0232_positive_checked⟩

def s0233_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0233_plain_checked : check 337 s0233_plain_contract = true := by decide +kernel
def s0233_plain : CertifiedContract :=
  ⟨233, 234, 0, (.inc 2), s0233_plain_contract, 337, s0233_plain_checked⟩

def s0234_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0234_plain_checked : check 364 s0234_plain_contract = true := by decide +kernel
def s0234_plain : CertifiedContract :=
  ⟨234, 235, 0, (.inc 8), s0234_plain_contract, 364, s0234_plain_checked⟩

def s0235_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, false] 0 .none⟩
theorem s0235_plain_checked : check 95 s0235_plain_contract = true := by decide +kernel
def s0235_plain : CertifiedContract :=
  ⟨235, 232, 0, .none, s0235_plain_contract, 95, s0235_plain_checked⟩

def s0236_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, false] 0 .none⟩
theorem s0236_zero_checked : check 330 s0236_zero_contract = true := by decide +kernel
def s0236_zero : CertifiedContract :=
  ⟨236, 239, 0, .none, s0236_zero_contract, 330, s0236_zero_checked⟩

def s0236_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, true, true, false] 1 (.dec 8)⟩
theorem s0236_positive_checked : check 324 s0236_positive_contract = true := by decide +kernel
def s0236_positive : CertifiedContract :=
  ⟨236, 237, 1, (.dec 8), s0236_positive_contract, 324, s0236_positive_checked⟩

def s0237_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, true, true, true] 0 (.inc 3)⟩
theorem s0237_plain_checked : check 340 s0237_plain_contract = true := by decide +kernel
def s0237_plain : CertifiedContract :=
  ⟨237, 238, 0, (.inc 3), s0237_plain_contract, 340, s0237_plain_checked⟩

def s0238_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, true, false] 0 .none⟩
theorem s0238_plain_checked : check 86 s0238_plain_contract = true := by decide +kernel
def s0238_plain : CertifiedContract :=
  ⟨238, 236, 0, .none, s0238_plain_contract, 86, s0238_plain_checked⟩

def s0239_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, true, false] 0 .none⟩
theorem s0239_zero_checked : check 312 s0239_zero_contract = true := by decide +kernel
def s0239_zero : CertifiedContract :=
  ⟨239, 247, 0, .none, s0239_zero_contract, 312, s0239_zero_checked⟩

def s0239_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, false] 1 (.dec 0)⟩
theorem s0239_positive_checked : check 318 s0239_positive_contract = true := by decide +kernel
def s0239_positive : CertifiedContract :=
  ⟨239, 240, 1, (.dec 0), s0239_positive_contract, 318, s0239_positive_checked⟩

def s0240_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0240_plain_checked : check 328 s0240_plain_contract = true := by decide +kernel
def s0240_plain : CertifiedContract :=
  ⟨240, 241, 0, (.inc 5), s0240_plain_contract, 328, s0240_plain_checked⟩

def s0241_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s0241_zero_checked : check 354 s0241_zero_contract = true := by decide +kernel
def s0241_zero : CertifiedContract :=
  ⟨241, 243, 0, .none, s0241_zero_contract, 354, s0241_zero_checked⟩

def s0241_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0241_positive_checked : check 360 s0241_positive_contract = true := by decide +kernel
def s0241_positive : CertifiedContract :=
  ⟨241, 242, 1, (.dec 8), s0241_positive_contract, 360, s0241_positive_checked⟩

end PA211.UserCandidate.RuntimeShards.S004
