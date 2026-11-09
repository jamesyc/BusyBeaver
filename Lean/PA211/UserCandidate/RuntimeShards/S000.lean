import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S000
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s0000_zero_contract : Contract :=
  ⟨(some (1, true)), rootFrame [false, false, false, false], rootFrame [false, false, true, false, false] 0 .none⟩
theorem s0000_zero_checked : check 204 s0000_zero_contract = true := by decide +kernel
def s0000_zero : CertifiedContract :=
  ⟨0, 2, 0, .none, s0000_zero_contract, 204, s0000_zero_checked⟩

def s0000_positive_contract : Contract :=
  ⟨(some (1, false)), rootFrame [false, false, false, false], rootFrame [false, false, false, true] 1 (.dec 1)⟩
theorem s0000_positive_checked : check 210 s0000_positive_contract = true := by decide +kernel
def s0000_positive : CertifiedContract :=
  ⟨0, 1, 1, (.dec 1), s0000_positive_contract, 210, s0000_positive_checked⟩

def s0001_plain_contract : Contract :=
  ⟨(none), rootFrame [false, false, false, true], rootFrame [false, true, false, false, false] 0 .none⟩
theorem s0001_plain_checked : check 55 s0001_plain_contract = true := by decide +kernel
def s0001_plain : CertifiedContract :=
  ⟨1, 9, 0, .none, s0001_plain_contract, 55, s0001_plain_checked⟩

def s0002_zero_contract : Contract :=
  ⟨(some (6, true)), rootFrame [false, false, true, false, false], rootFrame [false, false, true, true, false] 0 .none⟩
theorem s0002_zero_checked : check 213 s0002_zero_contract = true := by decide +kernel
def s0002_zero : CertifiedContract :=
  ⟨2, 6, 0, .none, s0002_zero_contract, 213, s0002_zero_checked⟩

def s0002_positive_contract : Contract :=
  ⟨(some (6, false)), rootFrame [false, false, true, false, false], rootFrame [false, false, true, false, true, false] 1 (.dec 6)⟩
theorem s0002_positive_checked : check 219 s0002_positive_contract = true := by decide +kernel
def s0002_positive : CertifiedContract :=
  ⟨2, 3, 1, (.dec 6), s0002_positive_contract, 219, s0002_positive_checked⟩

def s0003_plain_contract : Contract :=
  ⟨(none), rootFrame [false, false, true, false, true, false], rootFrame [false, false, true, false, true, true, false] 0 (.inc 1)⟩
theorem s0003_plain_checked : check 229 s0003_plain_contract = true := by decide +kernel
def s0003_plain : CertifiedContract :=
  ⟨3, 4, 0, (.inc 1), s0003_plain_contract, 229, s0003_plain_checked⟩

def s0004_plain_contract : Contract :=
  ⟨(none), rootFrame [false, false, true, false, true, true, false], rootFrame [false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0004_plain_checked : check 256 s0004_plain_contract = true := by decide +kernel
def s0004_plain : CertifiedContract :=
  ⟨4, 5, 0, (.inc 8), s0004_plain_contract, 256, s0004_plain_checked⟩

def s0005_plain_contract : Contract :=
  ⟨(none), rootFrame [false, false, true, false, true, true, true], rootFrame [false, false, true, false, false] 0 .none⟩
theorem s0005_plain_checked : check 59 s0005_plain_contract = true := by decide +kernel
def s0005_plain : CertifiedContract :=
  ⟨5, 2, 0, .none, s0005_plain_contract, 59, s0005_plain_checked⟩

def s0006_plain_contract : Contract :=
  ⟨(none), rootFrame [false, false, true, true, false], rootFrame [false, false, true, true, true, false] 0 (.inc 6)⟩
theorem s0006_plain_checked : check 220 s0006_plain_contract = true := by decide +kernel
def s0006_plain : CertifiedContract :=
  ⟨6, 7, 0, (.inc 6), s0006_plain_contract, 220, s0006_plain_checked⟩

def s0007_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [false, false, true, true, true, false], rootFrame [false, true, false, false, false] 0 .none⟩
theorem s0007_zero_checked : check 237 s0007_zero_contract = true := by decide +kernel
def s0007_zero : CertifiedContract :=
  ⟨7, 9, 0, .none, s0007_zero_contract, 237, s0007_zero_checked⟩

def s0007_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [false, false, true, true, true, false], rootFrame [false, false, true, true, true, true] 1 (.dec 8)⟩
theorem s0007_positive_checked : check 234 s0007_positive_contract = true := by decide +kernel
def s0007_positive : CertifiedContract :=
  ⟨7, 8, 1, (.dec 8), s0007_positive_contract, 234, s0007_positive_checked⟩

def s0008_plain_contract : Contract :=
  ⟨(none), rootFrame [false, false, true, true, true, true], rootFrame [false, false, true, true, false] 0 .none⟩
theorem s0008_plain_checked : check 50 s0008_plain_contract = true := by decide +kernel
def s0008_plain : CertifiedContract :=
  ⟨8, 6, 0, .none, s0008_plain_contract, 50, s0008_plain_checked⟩

def s0009_zero_contract : Contract :=
  ⟨(some (1, true)), rootFrame [false, true, false, false, false], rootFrame [false, true, false, true, false] 0 .none⟩
theorem s0009_zero_checked : check 213 s0009_zero_contract = true := by decide +kernel
def s0009_zero : CertifiedContract :=
  ⟨9, 17, 0, .none, s0009_zero_contract, 213, s0009_zero_checked⟩

def s0009_positive_contract : Contract :=
  ⟨(some (1, false)), rootFrame [false, true, false, false, false], rootFrame [false, true, false, false, true, false] 1 (.dec 1)⟩
theorem s0009_positive_checked : check 219 s0009_positive_contract = true := by decide +kernel
def s0009_positive : CertifiedContract :=
  ⟨9, 10, 1, (.dec 1), s0009_positive_contract, 219, s0009_positive_checked⟩

def s0010_plain_contract : Contract :=
  ⟨(none), rootFrame [false, true, false, false, true, false], rootFrame [false, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0010_plain_checked : check 211 s0010_plain_contract = true := by decide +kernel
def s0010_plain : CertifiedContract :=
  ⟨10, 11, 0, (.inc 5), s0010_plain_contract, 211, s0010_plain_checked⟩

def s0011_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [false, true, false, false, true, true, false, false, false], rootFrame [false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s0011_zero_checked : check 237 s0011_zero_contract = true := by decide +kernel
def s0011_zero : CertifiedContract :=
  ⟨11, 13, 0, .none, s0011_zero_contract, 237, s0011_zero_checked⟩

def s0011_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [false, true, false, false, true, true, false, false, false], rootFrame [false, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0011_positive_checked : check 243 s0011_positive_contract = true := by decide +kernel
def s0011_positive : CertifiedContract :=
  ⟨11, 12, 1, (.dec 8), s0011_positive_contract, 243, s0011_positive_checked⟩

def s0012_plain_contract : Contract :=
  ⟨(none), rootFrame [false, true, false, false, true, true, false, false, true], rootFrame [false, true, false, false, true, true, true] 0 .none⟩
theorem s0012_plain_checked : check 56 s0012_plain_contract = true := by decide +kernel
def s0012_plain : CertifiedContract :=
  ⟨12, 16, 0, .none, s0012_plain_contract, 56, s0012_plain_checked⟩

def s0013_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [false, true, false, false, true, true, false, true, false], rootFrame [false, true, false, false, true, true, true] 0 .none⟩
theorem s0013_zero_checked : check 249 s0013_zero_contract = true := by decide +kernel
def s0013_zero : CertifiedContract :=
  ⟨13, 16, 0, .none, s0013_zero_contract, 249, s0013_zero_checked⟩

def s0013_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [false, true, false, false, true, true, false, true, false], rootFrame [false, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0013_positive_checked : check 252 s0013_positive_contract = true := by decide +kernel
def s0013_positive : CertifiedContract :=
  ⟨13, 14, 1, (.dec 5), s0013_positive_contract, 252, s0013_positive_checked⟩

def s0014_plain_contract : Contract :=
  ⟨(none), rootFrame [false, true, false, false, true, true, false, true, true, false], rootFrame [false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0014_plain_checked : check 256 s0014_plain_contract = true := by decide +kernel
def s0014_plain : CertifiedContract :=
  ⟨14, 15, 0, (.inc 8), s0014_plain_contract, 256, s0014_plain_checked⟩

def s0015_plain_contract : Contract :=
  ⟨(none), rootFrame [false, true, false, false, true, true, false, true, true, true], rootFrame [false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s0015_plain_checked : check 59 s0015_plain_contract = true := by decide +kernel
def s0015_plain : CertifiedContract :=
  ⟨15, 13, 0, .none, s0015_plain_contract, 59, s0015_plain_checked⟩

def s0016_plain_contract : Contract :=
  ⟨(none), rootFrame [false, true, false, false, true, true, true], rootFrame [false, true, false, false, false] 0 .none⟩
theorem s0016_plain_checked : check 50 s0016_plain_contract = true := by decide +kernel
def s0016_plain : CertifiedContract :=
  ⟨16, 9, 0, .none, s0016_plain_contract, 50, s0016_plain_checked⟩

def s0017_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [false, true, false, true, false], rootFrame [false, true, true, false] 0 .none⟩
theorem s0017_zero_checked : check 213 s0017_zero_contract = true := by decide +kernel
def s0017_zero : CertifiedContract :=
  ⟨17, 20, 0, .none, s0017_zero_contract, 213, s0017_zero_checked⟩

def s0017_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [false, true, false, true, false], rootFrame [false, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0017_positive_checked : check 216 s0017_positive_contract = true := by decide +kernel
def s0017_positive : CertifiedContract :=
  ⟨17, 18, 1, (.dec 5), s0017_positive_contract, 216, s0017_positive_checked⟩

def s0018_plain_contract : Contract :=
  ⟨(none), rootFrame [false, true, false, true, true, false], rootFrame [false, true, false, true, true, true] 0 (.inc 1)⟩
theorem s0018_plain_checked : check 229 s0018_plain_contract = true := by decide +kernel
def s0018_plain : CertifiedContract :=
  ⟨18, 19, 0, (.inc 1), s0018_plain_contract, 229, s0018_plain_checked⟩

def s0019_plain_contract : Contract :=
  ⟨(none), rootFrame [false, true, false, true, true, true], rootFrame [false, true, false, true, false] 0 .none⟩
theorem s0019_plain_checked : check 53 s0019_plain_contract = true := by decide +kernel
def s0019_plain : CertifiedContract :=
  ⟨19, 17, 0, .none, s0019_plain_contract, 53, s0019_plain_checked⟩

def s0020_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [false, true, true, false], rootFrame [true, false, false] 0 .none⟩
theorem s0020_zero_checked : check 198 s0020_zero_contract = true := by decide +kernel
def s0020_zero : CertifiedContract :=
  ⟨20, 23, 0, .none, s0020_zero_contract, 198, s0020_zero_checked⟩

def s0020_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [false, true, true, false], rootFrame [false, true, true, true, false] 1 (.dec 8)⟩
theorem s0020_positive_checked : check 198 s0020_positive_contract = true := by decide +kernel
def s0020_positive : CertifiedContract :=
  ⟨20, 21, 1, (.dec 8), s0020_positive_contract, 198, s0020_positive_checked⟩

def s0021_plain_contract : Contract :=
  ⟨(none), rootFrame [false, true, true, true, false], rootFrame [false, true, true, true, true] 0 (.inc 4)⟩
theorem s0021_plain_checked : check 202 s0021_plain_contract = true := by decide +kernel
def s0021_plain : CertifiedContract :=
  ⟨21, 22, 0, (.inc 4), s0021_plain_contract, 202, s0021_plain_checked⟩

def s0022_plain_contract : Contract :=
  ⟨(none), rootFrame [false, true, true, true, true], rootFrame [false, true, true, false] 0 .none⟩
theorem s0022_plain_checked : check 44 s0022_plain_contract = true := by decide +kernel
def s0022_plain : CertifiedContract :=
  ⟨22, 20, 0, .none, s0022_plain_contract, 44, s0022_plain_checked⟩

def s0023_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, false], rootFrame [true, true, false, false] 0 .none⟩
theorem s0023_zero_checked : check 192 s0023_zero_contract = true := by decide +kernel
def s0023_zero : CertifiedContract :=
  ⟨23, 3911, 0, .none, s0023_zero_contract, 192, s0023_zero_checked⟩

def s0023_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, false], rootFrame [true, false, true, false, false, false] 1 (.dec 4)⟩
theorem s0023_positive_checked : check 198 s0023_positive_contract = true := by decide +kernel
def s0023_positive : CertifiedContract :=
  ⟨23, 24, 1, (.dec 4), s0023_positive_contract, 198, s0023_positive_checked⟩

def s0024_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, false], rootFrame [true, false, true, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s0024_zero_checked : check 219 s0024_zero_contract = true := by decide +kernel
def s0024_zero : CertifiedContract :=
  ⟨24, 3804, 0, .none, s0024_zero_contract, 219, s0024_zero_checked⟩

def s0024_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, false, false, false, false, false, false] 1 (.dec 4)⟩
theorem s0024_positive_checked : check 225 s0024_positive_contract = true := by decide +kernel
def s0024_positive : CertifiedContract :=
  ⟨24, 25, 1, (.dec 4), s0024_positive_contract, 225, s0024_positive_checked⟩

def s0025_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0025_zero_checked : check 282 s0025_zero_contract = true := by decide +kernel
def s0025_zero : CertifiedContract :=
  ⟨25, 28, 0, .none, s0025_zero_contract, 282, s0025_zero_checked⟩

def s0025_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s0025_positive_checked : check 288 s0025_positive_contract = true := by decide +kernel
def s0025_positive : CertifiedContract :=
  ⟨25, 26, 1, (.dec 2), s0025_positive_contract, 288, s0025_positive_checked⟩

def s0026_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s0026_plain_checked : check 301 s0026_plain_contract = true := by decide +kernel
def s0026_plain : CertifiedContract :=
  ⟨26, 27, 0, (.inc 8), s0026_plain_contract, 301, s0026_plain_checked⟩

def s0027_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s0027_plain_checked : check 74 s0027_plain_contract = true := by decide +kernel
def s0027_plain : CertifiedContract :=
  ⟨27, 25, 0, .none, s0027_plain_contract, 74, s0027_plain_checked⟩

def s0028_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0028_zero_checked : check 303 s0028_zero_contract = true := by decide +kernel
def s0028_zero : CertifiedContract :=
  ⟨28, 31, 0, .none, s0028_zero_contract, 303, s0028_zero_checked⟩

def s0028_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0028_positive_checked : check 309 s0028_positive_contract = true := by decide +kernel
def s0028_positive : CertifiedContract :=
  ⟨28, 29, 1, (.dec 0), s0028_positive_contract, 309, s0028_positive_checked⟩

def s0029_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0029_plain_checked : check 301 s0029_plain_contract = true := by decide +kernel
def s0029_plain : CertifiedContract :=
  ⟨29, 30, 0, (.inc 2), s0029_plain_contract, 301, s0029_plain_checked⟩

def s0030_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0030_plain_checked : check 77 s0030_plain_contract = true := by decide +kernel
def s0030_plain : CertifiedContract :=
  ⟨30, 28, 0, .none, s0030_plain_contract, 77, s0030_plain_checked⟩

def s0031_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0031_zero_checked : check 309 s0031_zero_contract = true := by decide +kernel
def s0031_zero : CertifiedContract :=
  ⟨31, 35, 0, .none, s0031_zero_contract, 309, s0031_zero_checked⟩

def s0031_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0031_positive_checked : check 315 s0031_positive_contract = true := by decide +kernel
def s0031_positive : CertifiedContract :=
  ⟨31, 32, 1, (.dec 2), s0031_positive_contract, 315, s0031_positive_checked⟩

def s0032_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0032_plain_checked : check 328 s0032_plain_contract = true := by decide +kernel
def s0032_plain : CertifiedContract :=
  ⟨32, 33, 0, (.inc 5), s0032_plain_contract, 328, s0032_plain_checked⟩

def s0033_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0033_plain_checked : check 355 s0033_plain_contract = true := by decide +kernel
def s0033_plain : CertifiedContract :=
  ⟨33, 34, 0, (.inc 8), s0033_plain_contract, 355, s0033_plain_checked⟩

def s0034_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0034_plain_checked : check 92 s0034_plain_contract = true := by decide +kernel
def s0034_plain : CertifiedContract :=
  ⟨34, 31, 0, .none, s0034_plain_contract, 92, s0034_plain_checked⟩

def s0035_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s0035_zero_checked : check 330 s0035_zero_contract = true := by decide +kernel
def s0035_zero : CertifiedContract :=
  ⟨35, 41, 0, .none, s0035_zero_contract, 330, s0035_zero_checked⟩

def s0035_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0035_positive_checked : check 333 s0035_positive_contract = true := by decide +kernel
def s0035_positive : CertifiedContract :=
  ⟨35, 36, 1, (.dec 8), s0035_positive_contract, 333, s0035_positive_checked⟩

def s0036_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0036_plain_checked : check 328 s0036_plain_contract = true := by decide +kernel
def s0036_plain : CertifiedContract :=
  ⟨36, 37, 0, (.inc 5), s0036_plain_contract, 328, s0036_plain_checked⟩

def s0037_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s0037_zero_checked : check 348 s0037_zero_contract = true := by decide +kernel
def s0037_zero : CertifiedContract :=
  ⟨37, 40, 0, .none, s0037_zero_contract, 348, s0037_zero_checked⟩

def s0037_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0037_positive_checked : check 351 s0037_positive_contract = true := by decide +kernel
def s0037_positive : CertifiedContract :=
  ⟨37, 38, 1, (.dec 8), s0037_positive_contract, 351, s0037_positive_checked⟩

def s0038_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0038_plain_checked : check 346 s0038_plain_contract = true := by decide +kernel
def s0038_plain : CertifiedContract :=
  ⟨38, 39, 0, (.inc 2), s0038_plain_contract, 346, s0038_plain_checked⟩

def s0039_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0039_plain_checked : check 92 s0039_plain_contract = true := by decide +kernel
def s0039_plain : CertifiedContract :=
  ⟨39, 37, 0, .none, s0039_plain_contract, 92, s0039_plain_checked⟩

def s0040_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0040_plain_checked : check 95 s0040_plain_contract = true := by decide +kernel
def s0040_plain : CertifiedContract :=
  ⟨40, 31, 0, .none, s0040_plain_contract, 95, s0040_plain_checked⟩

def s0041_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s0041_zero_checked : check 318 s0041_zero_contract = true := by decide +kernel
def s0041_zero : CertifiedContract :=
  ⟨41, 44, 0, .none, s0041_zero_contract, 318, s0041_zero_checked⟩

def s0041_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0041_positive_checked : check 315 s0041_positive_contract = true := by decide +kernel
def s0041_positive : CertifiedContract :=
  ⟨41, 42, 1, (.dec 5), s0041_positive_contract, 315, s0041_positive_checked⟩

def s0042_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0042_plain_checked : check 328 s0042_plain_contract = true := by decide +kernel
def s0042_plain : CertifiedContract :=
  ⟨42, 43, 0, (.inc 0), s0042_plain_contract, 328, s0042_plain_checked⟩

def s0043_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s0043_plain_checked : check 83 s0043_plain_contract = true := by decide +kernel
def s0043_plain : CertifiedContract :=
  ⟨43, 41, 0, .none, s0043_plain_contract, 83, s0043_plain_checked⟩

def s0044_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s0044_zero_checked : check 282 s0044_zero_contract = true := by decide +kernel
def s0044_zero : CertifiedContract :=
  ⟨44, 48, 0, .none, s0044_zero_contract, 282, s0044_zero_checked⟩

def s0044_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, false, false, false, true, false, true, false] 1 (.dec 3)⟩
theorem s0044_positive_checked : check 288 s0044_positive_contract = true := by decide +kernel
def s0044_positive : CertifiedContract :=
  ⟨44, 45, 1, (.dec 3), s0044_positive_contract, 288, s0044_positive_checked⟩

def s0045_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0045_plain_checked : check 301 s0045_plain_contract = true := by decide +kernel
def s0045_plain : CertifiedContract :=
  ⟨45, 46, 0, (.inc 2), s0045_plain_contract, 301, s0045_plain_checked⟩

def s0046_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0046_plain_checked : check 328 s0046_plain_contract = true := by decide +kernel
def s0046_plain : CertifiedContract :=
  ⟨46, 47, 0, (.inc 8), s0046_plain_contract, 328, s0046_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S000
