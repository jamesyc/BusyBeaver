module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S000
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s0000_zero_contract : Contract :=
  ⟨(some (1, true)), rootFrame [false, false, false, false], rootFrame [false, false, true, false, false] 0 .none⟩
theorem s0000_zero_checked : check 203 s0000_zero_contract = true := by decide +kernel
def s0000_zero : CertifiedContract :=
  ⟨0, 2, 0, .none, s0000_zero_contract, 203, s0000_zero_checked⟩

def s0000_positive_contract : Contract :=
  ⟨(some (1, false)), rootFrame [false, false, false, false], rootFrame [false, false, false, true] 1 (.dec 1)⟩
theorem s0000_positive_checked : check 209 s0000_positive_contract = true := by decide +kernel
def s0000_positive : CertifiedContract :=
  ⟨0, 1, 1, (.dec 1), s0000_positive_contract, 209, s0000_positive_checked⟩

def s0001_plain_contract : Contract :=
  ⟨(none), rootFrame [false, false, false, true], rootFrame [false, true, false, false, false] 0 .none⟩
theorem s0001_plain_checked : check 54 s0001_plain_contract = true := by decide +kernel
def s0001_plain : CertifiedContract :=
  ⟨1, 9, 0, .none, s0001_plain_contract, 54, s0001_plain_checked⟩

def s0002_zero_contract : Contract :=
  ⟨(some (6, true)), rootFrame [false, false, true, false, false], rootFrame [false, false, true, true, false] 0 .none⟩
theorem s0002_zero_checked : check 212 s0002_zero_contract = true := by decide +kernel
def s0002_zero : CertifiedContract :=
  ⟨2, 6, 0, .none, s0002_zero_contract, 212, s0002_zero_checked⟩

def s0002_positive_contract : Contract :=
  ⟨(some (6, false)), rootFrame [false, false, true, false, false], rootFrame [false, false, true, false, true, false] 1 (.dec 6)⟩
theorem s0002_positive_checked : check 218 s0002_positive_contract = true := by decide +kernel
def s0002_positive : CertifiedContract :=
  ⟨2, 3, 1, (.dec 6), s0002_positive_contract, 218, s0002_positive_checked⟩

def s0003_plain_contract : Contract :=
  ⟨(none), rootFrame [false, false, true, false, true, false], rootFrame [false, false, true, false, true, true, false] 0 (.inc 1)⟩
theorem s0003_plain_checked : check 228 s0003_plain_contract = true := by decide +kernel
def s0003_plain : CertifiedContract :=
  ⟨3, 4, 0, (.inc 1), s0003_plain_contract, 228, s0003_plain_checked⟩

def s0004_plain_contract : Contract :=
  ⟨(none), rootFrame [false, false, true, false, true, true, false], rootFrame [false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0004_plain_checked : check 255 s0004_plain_contract = true := by decide +kernel
def s0004_plain : CertifiedContract :=
  ⟨4, 5, 0, (.inc 8), s0004_plain_contract, 255, s0004_plain_checked⟩

def s0005_plain_contract : Contract :=
  ⟨(none), rootFrame [false, false, true, false, true, true, true], rootFrame [false, false, true, false, false] 0 .none⟩
theorem s0005_plain_checked : check 58 s0005_plain_contract = true := by decide +kernel
def s0005_plain : CertifiedContract :=
  ⟨5, 2, 0, .none, s0005_plain_contract, 58, s0005_plain_checked⟩

def s0006_plain_contract : Contract :=
  ⟨(none), rootFrame [false, false, true, true, false], rootFrame [false, false, true, true, true, false] 0 (.inc 6)⟩
theorem s0006_plain_checked : check 219 s0006_plain_contract = true := by decide +kernel
def s0006_plain : CertifiedContract :=
  ⟨6, 7, 0, (.inc 6), s0006_plain_contract, 219, s0006_plain_checked⟩

def s0007_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [false, false, true, true, true, false], rootFrame [false, true, false, false, false] 0 .none⟩
theorem s0007_zero_checked : check 236 s0007_zero_contract = true := by decide +kernel
def s0007_zero : CertifiedContract :=
  ⟨7, 9, 0, .none, s0007_zero_contract, 236, s0007_zero_checked⟩

def s0007_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [false, false, true, true, true, false], rootFrame [false, false, true, true, true, true] 1 (.dec 8)⟩
theorem s0007_positive_checked : check 233 s0007_positive_contract = true := by decide +kernel
def s0007_positive : CertifiedContract :=
  ⟨7, 8, 1, (.dec 8), s0007_positive_contract, 233, s0007_positive_checked⟩

def s0008_plain_contract : Contract :=
  ⟨(none), rootFrame [false, false, true, true, true, true], rootFrame [false, false, true, true, false] 0 .none⟩
theorem s0008_plain_checked : check 49 s0008_plain_contract = true := by decide +kernel
def s0008_plain : CertifiedContract :=
  ⟨8, 6, 0, .none, s0008_plain_contract, 49, s0008_plain_checked⟩

def s0009_zero_contract : Contract :=
  ⟨(some (1, true)), rootFrame [false, true, false, false, false], rootFrame [false, true, false, true, false] 0 .none⟩
theorem s0009_zero_checked : check 212 s0009_zero_contract = true := by decide +kernel
def s0009_zero : CertifiedContract :=
  ⟨9, 17, 0, .none, s0009_zero_contract, 212, s0009_zero_checked⟩

def s0009_positive_contract : Contract :=
  ⟨(some (1, false)), rootFrame [false, true, false, false, false], rootFrame [false, true, false, false, true, false] 1 (.dec 1)⟩
theorem s0009_positive_checked : check 218 s0009_positive_contract = true := by decide +kernel
def s0009_positive : CertifiedContract :=
  ⟨9, 10, 1, (.dec 1), s0009_positive_contract, 218, s0009_positive_checked⟩

def s0010_plain_contract : Contract :=
  ⟨(none), rootFrame [false, true, false, false, true, false], rootFrame [false, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0010_plain_checked : check 210 s0010_plain_contract = true := by decide +kernel
def s0010_plain : CertifiedContract :=
  ⟨10, 11, 0, (.inc 5), s0010_plain_contract, 210, s0010_plain_checked⟩

def s0011_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [false, true, false, false, true, true, false, false, false], rootFrame [false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s0011_zero_checked : check 236 s0011_zero_contract = true := by decide +kernel
def s0011_zero : CertifiedContract :=
  ⟨11, 13, 0, .none, s0011_zero_contract, 236, s0011_zero_checked⟩

def s0011_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [false, true, false, false, true, true, false, false, false], rootFrame [false, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0011_positive_checked : check 242 s0011_positive_contract = true := by decide +kernel
def s0011_positive : CertifiedContract :=
  ⟨11, 12, 1, (.dec 8), s0011_positive_contract, 242, s0011_positive_checked⟩

def s0012_plain_contract : Contract :=
  ⟨(none), rootFrame [false, true, false, false, true, true, false, false, true], rootFrame [false, true, false, false, true, true, true] 0 .none⟩
theorem s0012_plain_checked : check 55 s0012_plain_contract = true := by decide +kernel
def s0012_plain : CertifiedContract :=
  ⟨12, 16, 0, .none, s0012_plain_contract, 55, s0012_plain_checked⟩

def s0013_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [false, true, false, false, true, true, false, true, false], rootFrame [false, true, false, false, true, true, true] 0 .none⟩
theorem s0013_zero_checked : check 248 s0013_zero_contract = true := by decide +kernel
def s0013_zero : CertifiedContract :=
  ⟨13, 16, 0, .none, s0013_zero_contract, 248, s0013_zero_checked⟩

def s0013_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [false, true, false, false, true, true, false, true, false], rootFrame [false, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0013_positive_checked : check 251 s0013_positive_contract = true := by decide +kernel
def s0013_positive : CertifiedContract :=
  ⟨13, 14, 1, (.dec 5), s0013_positive_contract, 251, s0013_positive_checked⟩

def s0014_plain_contract : Contract :=
  ⟨(none), rootFrame [false, true, false, false, true, true, false, true, true, false], rootFrame [false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0014_plain_checked : check 255 s0014_plain_contract = true := by decide +kernel
def s0014_plain : CertifiedContract :=
  ⟨14, 15, 0, (.inc 8), s0014_plain_contract, 255, s0014_plain_checked⟩

def s0015_plain_contract : Contract :=
  ⟨(none), rootFrame [false, true, false, false, true, true, false, true, true, true], rootFrame [false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s0015_plain_checked : check 58 s0015_plain_contract = true := by decide +kernel
def s0015_plain : CertifiedContract :=
  ⟨15, 13, 0, .none, s0015_plain_contract, 58, s0015_plain_checked⟩

def s0016_plain_contract : Contract :=
  ⟨(none), rootFrame [false, true, false, false, true, true, true], rootFrame [false, true, false, false, false] 0 .none⟩
theorem s0016_plain_checked : check 49 s0016_plain_contract = true := by decide +kernel
def s0016_plain : CertifiedContract :=
  ⟨16, 9, 0, .none, s0016_plain_contract, 49, s0016_plain_checked⟩

def s0017_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [false, true, false, true, false], rootFrame [false, true, true, false] 0 .none⟩
theorem s0017_zero_checked : check 212 s0017_zero_contract = true := by decide +kernel
def s0017_zero : CertifiedContract :=
  ⟨17, 20, 0, .none, s0017_zero_contract, 212, s0017_zero_checked⟩

def s0017_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [false, true, false, true, false], rootFrame [false, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0017_positive_checked : check 215 s0017_positive_contract = true := by decide +kernel
def s0017_positive : CertifiedContract :=
  ⟨17, 18, 1, (.dec 5), s0017_positive_contract, 215, s0017_positive_checked⟩

def s0018_plain_contract : Contract :=
  ⟨(none), rootFrame [false, true, false, true, true, false], rootFrame [false, true, false, true, true, true] 0 (.inc 1)⟩
theorem s0018_plain_checked : check 228 s0018_plain_contract = true := by decide +kernel
def s0018_plain : CertifiedContract :=
  ⟨18, 19, 0, (.inc 1), s0018_plain_contract, 228, s0018_plain_checked⟩

def s0019_plain_contract : Contract :=
  ⟨(none), rootFrame [false, true, false, true, true, true], rootFrame [false, true, false, true, false] 0 .none⟩
theorem s0019_plain_checked : check 52 s0019_plain_contract = true := by decide +kernel
def s0019_plain : CertifiedContract :=
  ⟨19, 17, 0, .none, s0019_plain_contract, 52, s0019_plain_checked⟩

def s0020_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [false, true, true, false], rootFrame [true, false, false] 0 .none⟩
theorem s0020_zero_checked : check 197 s0020_zero_contract = true := by decide +kernel
def s0020_zero : CertifiedContract :=
  ⟨20, 23, 0, .none, s0020_zero_contract, 197, s0020_zero_checked⟩

def s0020_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [false, true, true, false], rootFrame [false, true, true, true, false] 1 (.dec 8)⟩
theorem s0020_positive_checked : check 197 s0020_positive_contract = true := by decide +kernel
def s0020_positive : CertifiedContract :=
  ⟨20, 21, 1, (.dec 8), s0020_positive_contract, 197, s0020_positive_checked⟩

def s0021_plain_contract : Contract :=
  ⟨(none), rootFrame [false, true, true, true, false], rootFrame [false, true, true, true, true] 0 (.inc 4)⟩
theorem s0021_plain_checked : check 201 s0021_plain_contract = true := by decide +kernel
def s0021_plain : CertifiedContract :=
  ⟨21, 22, 0, (.inc 4), s0021_plain_contract, 201, s0021_plain_checked⟩

def s0022_plain_contract : Contract :=
  ⟨(none), rootFrame [false, true, true, true, true], rootFrame [false, true, true, false] 0 .none⟩
theorem s0022_plain_checked : check 43 s0022_plain_contract = true := by decide +kernel
def s0022_plain : CertifiedContract :=
  ⟨22, 20, 0, .none, s0022_plain_contract, 43, s0022_plain_checked⟩

def s0023_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, false], rootFrame [true, true, false, false] 0 .none⟩
theorem s0023_zero_checked : check 191 s0023_zero_contract = true := by decide +kernel
def s0023_zero : CertifiedContract :=
  ⟨23, 3911, 0, .none, s0023_zero_contract, 191, s0023_zero_checked⟩

def s0023_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, false], rootFrame [true, false, true, false, false, false] 1 (.dec 4)⟩
theorem s0023_positive_checked : check 197 s0023_positive_contract = true := by decide +kernel
def s0023_positive : CertifiedContract :=
  ⟨23, 24, 1, (.dec 4), s0023_positive_contract, 197, s0023_positive_checked⟩

def s0024_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, false], rootFrame [true, false, true, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s0024_zero_checked : check 218 s0024_zero_contract = true := by decide +kernel
def s0024_zero : CertifiedContract :=
  ⟨24, 3804, 0, .none, s0024_zero_contract, 218, s0024_zero_checked⟩

def s0024_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, false, false, false, false, false, false] 1 (.dec 4)⟩
theorem s0024_positive_checked : check 224 s0024_positive_contract = true := by decide +kernel
def s0024_positive : CertifiedContract :=
  ⟨24, 25, 1, (.dec 4), s0024_positive_contract, 224, s0024_positive_checked⟩

def s0025_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0025_zero_checked : check 281 s0025_zero_contract = true := by decide +kernel
def s0025_zero : CertifiedContract :=
  ⟨25, 28, 0, .none, s0025_zero_contract, 281, s0025_zero_checked⟩

def s0025_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s0025_positive_checked : check 287 s0025_positive_contract = true := by decide +kernel
def s0025_positive : CertifiedContract :=
  ⟨25, 26, 1, (.dec 2), s0025_positive_contract, 287, s0025_positive_checked⟩

def s0026_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s0026_plain_checked : check 300 s0026_plain_contract = true := by decide +kernel
def s0026_plain : CertifiedContract :=
  ⟨26, 27, 0, (.inc 8), s0026_plain_contract, 300, s0026_plain_checked⟩

def s0027_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s0027_plain_checked : check 73 s0027_plain_contract = true := by decide +kernel
def s0027_plain : CertifiedContract :=
  ⟨27, 25, 0, .none, s0027_plain_contract, 73, s0027_plain_checked⟩

def s0028_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0028_zero_checked : check 302 s0028_zero_contract = true := by decide +kernel
def s0028_zero : CertifiedContract :=
  ⟨28, 31, 0, .none, s0028_zero_contract, 302, s0028_zero_checked⟩

def s0028_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0028_positive_checked : check 308 s0028_positive_contract = true := by decide +kernel
def s0028_positive : CertifiedContract :=
  ⟨28, 29, 1, (.dec 0), s0028_positive_contract, 308, s0028_positive_checked⟩

def s0029_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0029_plain_checked : check 300 s0029_plain_contract = true := by decide +kernel
def s0029_plain : CertifiedContract :=
  ⟨29, 30, 0, (.inc 2), s0029_plain_contract, 300, s0029_plain_checked⟩

def s0030_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0030_plain_checked : check 76 s0030_plain_contract = true := by decide +kernel
def s0030_plain : CertifiedContract :=
  ⟨30, 28, 0, .none, s0030_plain_contract, 76, s0030_plain_checked⟩

def s0031_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0031_zero_checked : check 308 s0031_zero_contract = true := by decide +kernel
def s0031_zero : CertifiedContract :=
  ⟨31, 35, 0, .none, s0031_zero_contract, 308, s0031_zero_checked⟩

def s0031_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0031_positive_checked : check 314 s0031_positive_contract = true := by decide +kernel
def s0031_positive : CertifiedContract :=
  ⟨31, 32, 1, (.dec 2), s0031_positive_contract, 314, s0031_positive_checked⟩

def s0032_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0032_plain_checked : check 327 s0032_plain_contract = true := by decide +kernel
def s0032_plain : CertifiedContract :=
  ⟨32, 33, 0, (.inc 5), s0032_plain_contract, 327, s0032_plain_checked⟩

def s0033_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0033_plain_checked : check 354 s0033_plain_contract = true := by decide +kernel
def s0033_plain : CertifiedContract :=
  ⟨33, 34, 0, (.inc 8), s0033_plain_contract, 354, s0033_plain_checked⟩

def s0034_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0034_plain_checked : check 91 s0034_plain_contract = true := by decide +kernel
def s0034_plain : CertifiedContract :=
  ⟨34, 31, 0, .none, s0034_plain_contract, 91, s0034_plain_checked⟩

def s0035_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s0035_zero_checked : check 329 s0035_zero_contract = true := by decide +kernel
def s0035_zero : CertifiedContract :=
  ⟨35, 41, 0, .none, s0035_zero_contract, 329, s0035_zero_checked⟩

def s0035_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0035_positive_checked : check 332 s0035_positive_contract = true := by decide +kernel
def s0035_positive : CertifiedContract :=
  ⟨35, 36, 1, (.dec 8), s0035_positive_contract, 332, s0035_positive_checked⟩

def s0036_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0036_plain_checked : check 327 s0036_plain_contract = true := by decide +kernel
def s0036_plain : CertifiedContract :=
  ⟨36, 37, 0, (.inc 5), s0036_plain_contract, 327, s0036_plain_checked⟩

def s0037_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s0037_zero_checked : check 347 s0037_zero_contract = true := by decide +kernel
def s0037_zero : CertifiedContract :=
  ⟨37, 40, 0, .none, s0037_zero_contract, 347, s0037_zero_checked⟩

def s0037_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0037_positive_checked : check 350 s0037_positive_contract = true := by decide +kernel
def s0037_positive : CertifiedContract :=
  ⟨37, 38, 1, (.dec 8), s0037_positive_contract, 350, s0037_positive_checked⟩

def s0038_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0038_plain_checked : check 345 s0038_plain_contract = true := by decide +kernel
def s0038_plain : CertifiedContract :=
  ⟨38, 39, 0, (.inc 2), s0038_plain_contract, 345, s0038_plain_checked⟩

def s0039_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0039_plain_checked : check 91 s0039_plain_contract = true := by decide +kernel
def s0039_plain : CertifiedContract :=
  ⟨39, 37, 0, .none, s0039_plain_contract, 91, s0039_plain_checked⟩

def s0040_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0040_plain_checked : check 94 s0040_plain_contract = true := by decide +kernel
def s0040_plain : CertifiedContract :=
  ⟨40, 31, 0, .none, s0040_plain_contract, 94, s0040_plain_checked⟩

def s0041_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s0041_zero_checked : check 317 s0041_zero_contract = true := by decide +kernel
def s0041_zero : CertifiedContract :=
  ⟨41, 44, 0, .none, s0041_zero_contract, 317, s0041_zero_checked⟩

def s0041_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0041_positive_checked : check 314 s0041_positive_contract = true := by decide +kernel
def s0041_positive : CertifiedContract :=
  ⟨41, 42, 1, (.dec 5), s0041_positive_contract, 314, s0041_positive_checked⟩

def s0042_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0042_plain_checked : check 327 s0042_plain_contract = true := by decide +kernel
def s0042_plain : CertifiedContract :=
  ⟨42, 43, 0, (.inc 0), s0042_plain_contract, 327, s0042_plain_checked⟩

def s0043_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s0043_plain_checked : check 82 s0043_plain_contract = true := by decide +kernel
def s0043_plain : CertifiedContract :=
  ⟨43, 41, 0, .none, s0043_plain_contract, 82, s0043_plain_checked⟩

def s0044_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s0044_zero_checked : check 281 s0044_zero_contract = true := by decide +kernel
def s0044_zero : CertifiedContract :=
  ⟨44, 48, 0, .none, s0044_zero_contract, 281, s0044_zero_checked⟩

def s0044_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, false, false, false, true, false, true, false] 1 (.dec 3)⟩
theorem s0044_positive_checked : check 287 s0044_positive_contract = true := by decide +kernel
def s0044_positive : CertifiedContract :=
  ⟨44, 45, 1, (.dec 3), s0044_positive_contract, 287, s0044_positive_checked⟩

def s0045_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0045_plain_checked : check 300 s0045_plain_contract = true := by decide +kernel
def s0045_plain : CertifiedContract :=
  ⟨45, 46, 0, (.inc 2), s0045_plain_contract, 300, s0045_plain_checked⟩

def s0046_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0046_plain_checked : check 327 s0046_plain_contract = true := by decide +kernel
def s0046_plain : CertifiedContract :=
  ⟨46, 47, 0, (.inc 8), s0046_plain_contract, 327, s0046_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s0000_zero,
  s0000_positive,
  s0001_plain,
  s0002_zero,
  s0002_positive,
  s0003_plain,
  s0004_plain,
  s0005_plain,
  s0006_plain,
  s0007_zero,
  s0007_positive,
  s0008_plain,
  s0009_zero,
  s0009_positive,
  s0010_plain,
  s0011_zero,
  s0011_positive,
  s0012_plain,
  s0013_zero,
  s0013_positive,
  s0014_plain,
  s0015_plain,
  s0016_plain,
  s0017_zero,
  s0017_positive,
  s0018_plain,
  s0019_plain,
  s0020_zero,
  s0020_positive,
  s0021_plain,
  s0022_plain,
  s0023_zero,
  s0023_positive,
  s0024_zero,
  s0024_positive,
  s0025_zero,
  s0025_positive,
  s0026_plain,
  s0027_plain,
  s0028_zero,
  s0028_positive,
  s0029_plain,
  s0030_plain,
  s0031_zero,
  s0031_positive,
  s0032_plain,
  s0033_plain,
  s0034_plain,
  s0035_zero,
  s0035_positive,
  s0036_plain,
  s0037_zero,
  s0037_positive,
  s0038_plain,
  s0039_plain,
  s0040_plain,
  s0041_zero,
  s0041_positive,
  s0042_plain,
  s0043_plain,
  s0044_zero,
  s0044_positive,
  s0045_plain,
  s0046_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S000
