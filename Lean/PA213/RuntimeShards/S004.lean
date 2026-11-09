module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S004
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s0193_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0193_positive_checked : check 305 s0193_positive_contract = true := by decide +kernel
def s0193_positive : CertifiedContract :=
  ⟨193, 194, 1, (.dec 5), s0193_positive_contract, 305, s0193_positive_checked⟩

def s0194_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0194_plain_checked : check 318 s0194_plain_contract = true := by decide +kernel
def s0194_plain : CertifiedContract :=
  ⟨194, 195, 0, (.inc 2), s0194_plain_contract, 318, s0194_plain_checked⟩

def s0195_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0195_plain_checked : check 321 s0195_plain_contract = true := by decide +kernel
def s0195_plain : CertifiedContract :=
  ⟨195, 196, 0, (.inc 2), s0195_plain_contract, 321, s0195_plain_checked⟩

def s0196_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0196_plain_checked : check 318 s0196_plain_contract = true := by decide +kernel
def s0196_plain : CertifiedContract :=
  ⟨196, 197, 0, (.inc 2), s0196_plain_contract, 318, s0196_plain_checked⟩

def s0197_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s0197_plain_checked : check 324 s0197_plain_contract = true := by decide +kernel
def s0197_plain : CertifiedContract :=
  ⟨197, 198, 0, (.inc 2), s0197_plain_contract, 324, s0197_plain_checked⟩

def s0198_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s0198_plain_checked : check 76 s0198_plain_contract = true := by decide +kernel
def s0198_plain : CertifiedContract :=
  ⟨198, 193, 0, .none, s0198_plain_contract, 76, s0198_plain_checked⟩

def s0199_zero_contract : Contract :=
  ⟨(some (1, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, true, false] 0 .none⟩
theorem s0199_zero_checked : check 311 s0199_zero_contract = true := by decide +kernel
def s0199_zero : CertifiedContract :=
  ⟨199, 207, 0, .none, s0199_zero_contract, 311, s0199_zero_checked⟩

def s0199_positive_contract : Contract :=
  ⟨(some (1, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, false] 1 (.dec 1)⟩
theorem s0199_positive_checked : check 317 s0199_positive_contract = true := by decide +kernel
def s0199_positive : CertifiedContract :=
  ⟨199, 200, 1, (.dec 1), s0199_positive_contract, 317, s0199_positive_checked⟩

def s0200_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0200_plain_checked : check 309 s0200_plain_contract = true := by decide +kernel
def s0200_plain : CertifiedContract :=
  ⟨200, 201, 0, (.inc 5), s0200_plain_contract, 309, s0200_plain_checked⟩

def s0201_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0201_zero_checked : check 335 s0201_zero_contract = true := by decide +kernel
def s0201_zero : CertifiedContract :=
  ⟨201, 203, 0, .none, s0201_zero_contract, 335, s0201_zero_checked⟩

def s0201_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0201_positive_checked : check 341 s0201_positive_contract = true := by decide +kernel
def s0201_positive : CertifiedContract :=
  ⟨201, 202, 1, (.dec 8), s0201_positive_contract, 341, s0201_positive_checked⟩

def s0202_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s0202_plain_checked : check 88 s0202_plain_contract = true := by decide +kernel
def s0202_plain : CertifiedContract :=
  ⟨202, 206, 0, .none, s0202_plain_contract, 88, s0202_plain_checked⟩

def s0203_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s0203_zero_checked : check 347 s0203_zero_contract = true := by decide +kernel
def s0203_zero : CertifiedContract :=
  ⟨203, 206, 0, .none, s0203_zero_contract, 347, s0203_zero_checked⟩

def s0203_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0203_positive_checked : check 350 s0203_positive_contract = true := by decide +kernel
def s0203_positive : CertifiedContract :=
  ⟨203, 204, 1, (.dec 5), s0203_positive_contract, 350, s0203_positive_checked⟩

def s0204_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0204_plain_checked : check 354 s0204_plain_contract = true := by decide +kernel
def s0204_plain : CertifiedContract :=
  ⟨204, 205, 0, (.inc 8), s0204_plain_contract, 354, s0204_plain_checked⟩

def s0205_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0205_plain_checked : check 91 s0205_plain_contract = true := by decide +kernel
def s0205_plain : CertifiedContract :=
  ⟨205, 203, 0, .none, s0205_plain_contract, 91, s0205_plain_checked⟩

def s0206_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, false] 0 .none⟩
theorem s0206_plain_checked : check 82 s0206_plain_contract = true := by decide +kernel
def s0206_plain : CertifiedContract :=
  ⟨206, 199, 0, .none, s0206_plain_contract, 82, s0206_plain_checked⟩

def s0207_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, false, false] 0 .none⟩
theorem s0207_zero_checked : check 311 s0207_zero_contract = true := by decide +kernel
def s0207_zero : CertifiedContract :=
  ⟨207, 210, 0, .none, s0207_zero_contract, 311, s0207_zero_checked⟩

def s0207_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0207_positive_checked : check 314 s0207_positive_contract = true := by decide +kernel
def s0207_positive : CertifiedContract :=
  ⟨207, 208, 1, (.dec 5), s0207_positive_contract, 314, s0207_positive_checked⟩

def s0208_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, true, true, true] 0 (.inc 1)⟩
theorem s0208_plain_checked : check 327 s0208_plain_contract = true := by decide +kernel
def s0208_plain : CertifiedContract :=
  ⟨208, 209, 0, (.inc 1), s0208_plain_contract, 327, s0208_plain_checked⟩

def s0209_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, true, false] 0 .none⟩
theorem s0209_plain_checked : check 85 s0209_plain_contract = true := by decide +kernel
def s0209_plain : CertifiedContract :=
  ⟨209, 207, 0, .none, s0209_plain_contract, 85, s0209_plain_checked⟩

def s0210_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0210_zero_checked : check 299 s0210_zero_contract = true := by decide +kernel
def s0210_zero : CertifiedContract :=
  ⟨210, 213, 0, .none, s0210_zero_contract, 299, s0210_zero_checked⟩

def s0210_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, false, true, false] 1 (.dec 8)⟩
theorem s0210_positive_checked : check 305 s0210_positive_contract = true := by decide +kernel
def s0210_positive : CertifiedContract :=
  ⟨210, 211, 1, (.dec 8), s0210_positive_contract, 305, s0210_positive_checked⟩

def s0211_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, false, true, true] 0 (.inc 3)⟩
theorem s0211_plain_checked : check 321 s0211_plain_contract = true := by decide +kernel
def s0211_plain : CertifiedContract :=
  ⟨211, 212, 0, (.inc 3), s0211_plain_contract, 321, s0211_plain_checked⟩

def s0212_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, false, false] 0 .none⟩
theorem s0212_plain_checked : check 79 s0212_plain_contract = true := by decide +kernel
def s0212_plain : CertifiedContract :=
  ⟨212, 210, 0, .none, s0212_plain_contract, 79, s0212_plain_checked⟩

def s0213_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, false] 0 .none⟩
theorem s0213_zero_checked : check 317 s0213_zero_contract = true := by decide +kernel
def s0213_zero : CertifiedContract :=
  ⟨213, 216, 0, .none, s0213_zero_contract, 317, s0213_zero_checked⟩

def s0213_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0213_positive_checked : check 323 s0213_positive_contract = true := by decide +kernel
def s0213_positive : CertifiedContract :=
  ⟨213, 214, 1, (.dec 2), s0213_positive_contract, 323, s0213_positive_checked⟩

def s0214_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, false, true, true] 0 (.inc 8)⟩
theorem s0214_plain_checked : check 336 s0214_plain_contract = true := by decide +kernel
def s0214_plain : CertifiedContract :=
  ⟨214, 215, 0, (.inc 8), s0214_plain_contract, 336, s0214_plain_checked⟩

def s0215_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0215_plain_checked : check 85 s0215_plain_contract = true := by decide +kernel
def s0215_plain : CertifiedContract :=
  ⟨215, 213, 0, .none, s0215_plain_contract, 85, s0215_plain_checked⟩

def s0216_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0216_zero_checked : check 338 s0216_zero_contract = true := by decide +kernel
def s0216_zero : CertifiedContract :=
  ⟨216, 219, 0, .none, s0216_zero_contract, 338, s0216_zero_checked⟩

def s0216_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0216_positive_checked : check 344 s0216_positive_contract = true := by decide +kernel
def s0216_positive : CertifiedContract :=
  ⟨216, 217, 1, (.dec 0), s0216_positive_contract, 344, s0216_positive_checked⟩

def s0217_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0217_plain_checked : check 336 s0217_plain_contract = true := by decide +kernel
def s0217_plain : CertifiedContract :=
  ⟨217, 218, 0, (.inc 2), s0217_plain_contract, 336, s0217_plain_checked⟩

def s0218_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, false, false] 0 .none⟩
theorem s0218_plain_checked : check 88 s0218_plain_contract = true := by decide +kernel
def s0218_plain : CertifiedContract :=
  ⟨218, 216, 0, .none, s0218_plain_contract, 88, s0218_plain_checked⟩

def s0219_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0219_zero_checked : check 344 s0219_zero_contract = true := by decide +kernel
def s0219_zero : CertifiedContract :=
  ⟨219, 223, 0, .none, s0219_zero_contract, 344, s0219_zero_checked⟩

def s0219_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0219_positive_checked : check 350 s0219_positive_contract = true := by decide +kernel
def s0219_positive : CertifiedContract :=
  ⟨219, 220, 1, (.dec 2), s0219_positive_contract, 350, s0219_positive_checked⟩

def s0220_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0220_plain_checked : check 363 s0220_plain_contract = true := by decide +kernel
def s0220_plain : CertifiedContract :=
  ⟨220, 221, 0, (.inc 5), s0220_plain_contract, 363, s0220_plain_checked⟩

def s0221_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0221_plain_checked : check 390 s0221_plain_contract = true := by decide +kernel
def s0221_plain : CertifiedContract :=
  ⟨221, 222, 0, (.inc 8), s0221_plain_contract, 390, s0221_plain_checked⟩

def s0222_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0222_plain_checked : check 103 s0222_plain_contract = true := by decide +kernel
def s0222_plain : CertifiedContract :=
  ⟨222, 219, 0, .none, s0222_plain_contract, 103, s0222_plain_checked⟩

def s0223_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s0223_zero_checked : check 365 s0223_zero_contract = true := by decide +kernel
def s0223_zero : CertifiedContract :=
  ⟨223, 229, 0, .none, s0223_zero_contract, 365, s0223_zero_checked⟩

def s0223_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0223_positive_checked : check 368 s0223_positive_contract = true := by decide +kernel
def s0223_positive : CertifiedContract :=
  ⟨223, 224, 1, (.dec 8), s0223_positive_contract, 368, s0223_positive_checked⟩

def s0224_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0224_plain_checked : check 363 s0224_plain_contract = true := by decide +kernel
def s0224_plain : CertifiedContract :=
  ⟨224, 225, 0, (.inc 5), s0224_plain_contract, 363, s0224_plain_checked⟩

def s0225_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s0225_zero_checked : check 383 s0225_zero_contract = true := by decide +kernel
def s0225_zero : CertifiedContract :=
  ⟨225, 228, 0, .none, s0225_zero_contract, 383, s0225_zero_checked⟩

def s0225_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0225_positive_checked : check 386 s0225_positive_contract = true := by decide +kernel
def s0225_positive : CertifiedContract :=
  ⟨225, 226, 1, (.dec 8), s0225_positive_contract, 386, s0225_positive_checked⟩

def s0226_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0226_plain_checked : check 381 s0226_plain_contract = true := by decide +kernel
def s0226_plain : CertifiedContract :=
  ⟨226, 227, 0, (.inc 2), s0226_plain_contract, 381, s0226_plain_checked⟩

def s0227_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0227_plain_checked : check 103 s0227_plain_contract = true := by decide +kernel
def s0227_plain : CertifiedContract :=
  ⟨227, 225, 0, .none, s0227_plain_contract, 103, s0227_plain_checked⟩

def s0228_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0228_plain_checked : check 106 s0228_plain_contract = true := by decide +kernel
def s0228_plain : CertifiedContract :=
  ⟨228, 219, 0, .none, s0228_plain_contract, 106, s0228_plain_checked⟩

def s0229_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, false] 0 .none⟩
theorem s0229_zero_checked : check 353 s0229_zero_contract = true := by decide +kernel
def s0229_zero : CertifiedContract :=
  ⟨229, 232, 0, .none, s0229_zero_contract, 353, s0229_zero_checked⟩

def s0229_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0229_positive_checked : check 350 s0229_positive_contract = true := by decide +kernel
def s0229_positive : CertifiedContract :=
  ⟨229, 230, 1, (.dec 5), s0229_positive_contract, 350, s0229_positive_checked⟩

def s0230_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0230_plain_checked : check 363 s0230_plain_contract = true := by decide +kernel
def s0230_plain : CertifiedContract :=
  ⟨230, 231, 0, (.inc 0), s0230_plain_contract, 363, s0230_plain_checked⟩

def s0231_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s0231_plain_checked : check 94 s0231_plain_contract = true := by decide +kernel
def s0231_plain : CertifiedContract :=
  ⟨231, 229, 0, .none, s0231_plain_contract, 94, s0231_plain_checked⟩

def s0232_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, true, false] 0 .none⟩
theorem s0232_zero_checked : check 317 s0232_zero_contract = true := by decide +kernel
def s0232_zero : CertifiedContract :=
  ⟨232, 236, 0, .none, s0232_zero_contract, 317, s0232_zero_checked⟩

def s0232_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, true, false] 1 (.dec 3)⟩
theorem s0232_positive_checked : check 323 s0232_positive_contract = true := by decide +kernel
def s0232_positive : CertifiedContract :=
  ⟨232, 233, 1, (.dec 3), s0232_positive_contract, 323, s0232_positive_checked⟩

def s0233_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0233_plain_checked : check 336 s0233_plain_contract = true := by decide +kernel
def s0233_plain : CertifiedContract :=
  ⟨233, 234, 0, (.inc 2), s0233_plain_contract, 336, s0233_plain_checked⟩

def s0234_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0234_plain_checked : check 363 s0234_plain_contract = true := by decide +kernel
def s0234_plain : CertifiedContract :=
  ⟨234, 235, 0, (.inc 8), s0234_plain_contract, 363, s0234_plain_checked⟩

def s0235_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, false, false] 0 .none⟩
theorem s0235_plain_checked : check 94 s0235_plain_contract = true := by decide +kernel
def s0235_plain : CertifiedContract :=
  ⟨235, 232, 0, .none, s0235_plain_contract, 94, s0235_plain_checked⟩

def s0236_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, false] 0 .none⟩
theorem s0236_zero_checked : check 329 s0236_zero_contract = true := by decide +kernel
def s0236_zero : CertifiedContract :=
  ⟨236, 239, 0, .none, s0236_zero_contract, 329, s0236_zero_checked⟩

def s0236_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, true, true, false] 1 (.dec 8)⟩
theorem s0236_positive_checked : check 323 s0236_positive_contract = true := by decide +kernel
def s0236_positive : CertifiedContract :=
  ⟨236, 237, 1, (.dec 8), s0236_positive_contract, 323, s0236_positive_checked⟩

def s0237_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, true, true, true] 0 (.inc 3)⟩
theorem s0237_plain_checked : check 339 s0237_plain_contract = true := by decide +kernel
def s0237_plain : CertifiedContract :=
  ⟨237, 238, 0, (.inc 3), s0237_plain_contract, 339, s0237_plain_checked⟩

def s0238_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, true, true, true, true, false] 0 .none⟩
theorem s0238_plain_checked : check 85 s0238_plain_contract = true := by decide +kernel
def s0238_plain : CertifiedContract :=
  ⟨238, 236, 0, .none, s0238_plain_contract, 85, s0238_plain_checked⟩

def s0239_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, true, false] 0 .none⟩
theorem s0239_zero_checked : check 311 s0239_zero_contract = true := by decide +kernel
def s0239_zero : CertifiedContract :=
  ⟨239, 247, 0, .none, s0239_zero_contract, 311, s0239_zero_checked⟩

def s0239_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, false] 1 (.dec 0)⟩
theorem s0239_positive_checked : check 317 s0239_positive_contract = true := by decide +kernel
def s0239_positive : CertifiedContract :=
  ⟨239, 240, 1, (.dec 0), s0239_positive_contract, 317, s0239_positive_checked⟩

def s0240_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0240_plain_checked : check 327 s0240_plain_contract = true := by decide +kernel
def s0240_plain : CertifiedContract :=
  ⟨240, 241, 0, (.inc 5), s0240_plain_contract, 327, s0240_plain_checked⟩

def s0241_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s0241_zero_checked : check 353 s0241_zero_contract = true := by decide +kernel
def s0241_zero : CertifiedContract :=
  ⟨241, 243, 0, .none, s0241_zero_contract, 353, s0241_zero_checked⟩

def s0241_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0241_positive_checked : check 359 s0241_positive_contract = true := by decide +kernel
def s0241_positive : CertifiedContract :=
  ⟨241, 242, 1, (.dec 8), s0241_positive_contract, 359, s0241_positive_checked⟩

def nonterminal : Array CertifiedContract := #[
  s0193_positive,
  s0194_plain,
  s0195_plain,
  s0196_plain,
  s0197_plain,
  s0198_plain,
  s0199_zero,
  s0199_positive,
  s0200_plain,
  s0201_zero,
  s0201_positive,
  s0202_plain,
  s0203_zero,
  s0203_positive,
  s0204_plain,
  s0205_plain,
  s0206_plain,
  s0207_zero,
  s0207_positive,
  s0208_plain,
  s0209_plain,
  s0210_zero,
  s0210_positive,
  s0211_plain,
  s0212_plain,
  s0213_zero,
  s0213_positive,
  s0214_plain,
  s0215_plain,
  s0216_zero,
  s0216_positive,
  s0217_plain,
  s0218_plain,
  s0219_zero,
  s0219_positive,
  s0220_plain,
  s0221_plain,
  s0222_plain,
  s0223_zero,
  s0223_positive,
  s0224_plain,
  s0225_zero,
  s0225_positive,
  s0226_plain,
  s0227_plain,
  s0228_plain,
  s0229_zero,
  s0229_positive,
  s0230_plain,
  s0231_plain,
  s0232_zero,
  s0232_positive,
  s0233_plain,
  s0234_plain,
  s0235_plain,
  s0236_zero,
  s0236_positive,
  s0237_plain,
  s0238_plain,
  s0239_zero,
  s0239_positive,
  s0240_plain,
  s0241_zero,
  s0241_positive
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S004
