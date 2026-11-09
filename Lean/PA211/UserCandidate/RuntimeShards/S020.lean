module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S020
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s0982_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s0982_zero_checked : check 375 s0982_zero_contract = true := by decide +kernel
def s0982_zero : CertifiedContract :=
  ⟨982, 985, 0, .none, s0982_zero_contract, 375, s0982_zero_checked⟩

def s0982_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0982_positive_checked : check 378 s0982_positive_contract = true := by decide +kernel
def s0982_positive : CertifiedContract :=
  ⟨982, 983, 1, (.dec 8), s0982_positive_contract, 378, s0982_positive_checked⟩

def s0983_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0983_plain_checked : check 373 s0983_plain_contract = true := by decide +kernel
def s0983_plain : CertifiedContract :=
  ⟨983, 984, 0, (.inc 2), s0983_plain_contract, 373, s0983_plain_checked⟩

def s0984_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0984_plain_checked : check 101 s0984_plain_contract = true := by decide +kernel
def s0984_plain : CertifiedContract :=
  ⟨984, 982, 0, .none, s0984_plain_contract, 101, s0984_plain_checked⟩

def s0985_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0985_plain_checked : check 104 s0985_plain_contract = true := by decide +kernel
def s0985_plain : CertifiedContract :=
  ⟨985, 976, 0, .none, s0985_plain_contract, 104, s0985_plain_checked⟩

def s0986_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, true, false] 0 .none⟩
theorem s0986_zero_checked : check 342 s0986_zero_contract = true := by decide +kernel
def s0986_zero : CertifiedContract :=
  ⟨986, 992, 0, .none, s0986_zero_contract, 342, s0986_zero_checked⟩

def s0986_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0986_positive_checked : check 342 s0986_positive_contract = true := by decide +kernel
def s0986_positive : CertifiedContract :=
  ⟨986, 987, 1, (.dec 5), s0986_positive_contract, 342, s0986_positive_checked⟩

def s0987_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0987_plain_checked : check 355 s0987_plain_contract = true := by decide +kernel
def s0987_plain : CertifiedContract :=
  ⟨987, 988, 0, (.inc 2), s0987_plain_contract, 355, s0987_plain_checked⟩

def s0988_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0988_plain_checked : check 358 s0988_plain_contract = true := by decide +kernel
def s0988_plain : CertifiedContract :=
  ⟨988, 989, 0, (.inc 2), s0988_plain_contract, 358, s0988_plain_checked⟩

def s0989_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0989_plain_checked : check 364 s0989_plain_contract = true := by decide +kernel
def s0989_plain : CertifiedContract :=
  ⟨989, 990, 0, (.inc 2), s0989_plain_contract, 364, s0989_plain_checked⟩

def s0990_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s0990_plain_checked : check 370 s0990_plain_contract = true := by decide +kernel
def s0990_plain : CertifiedContract :=
  ⟨990, 991, 0, (.inc 2), s0990_plain_contract, 370, s0990_plain_checked⟩

def s0991_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s0991_plain_checked : check 89 s0991_plain_contract = true := by decide +kernel
def s0991_plain : CertifiedContract :=
  ⟨991, 986, 0, .none, s0991_plain_contract, 89, s0991_plain_checked⟩

def s0992_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0992_plain_checked : check 310 s0992_plain_contract = true := by decide +kernel
def s0992_plain : CertifiedContract :=
  ⟨992, 993, 0, (.inc 2), s0992_plain_contract, 310, s0992_plain_checked⟩

def s0993_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, false, false] 0 (.inc 2)⟩
theorem s0993_plain_checked : check 319 s0993_plain_contract = true := by decide +kernel
def s0993_plain : CertifiedContract :=
  ⟨993, 994, 0, (.inc 2), s0993_plain_contract, 319, s0993_plain_checked⟩

def s0994_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s0994_zero_checked : check 336 s0994_zero_contract = true := by decide +kernel
def s0994_zero : CertifiedContract :=
  ⟨994, 997, 0, .none, s0994_zero_contract, 336, s0994_zero_checked⟩

def s0994_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s0994_positive_checked : check 342 s0994_positive_contract = true := by decide +kernel
def s0994_positive : CertifiedContract :=
  ⟨994, 995, 1, (.dec 2), s0994_positive_contract, 342, s0994_positive_checked⟩

def s0995_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s0995_plain_checked : check 355 s0995_plain_contract = true := by decide +kernel
def s0995_plain : CertifiedContract :=
  ⟨995, 996, 0, (.inc 8), s0995_plain_contract, 355, s0995_plain_checked⟩

def s0996_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, false, false] 0 .none⟩
theorem s0996_plain_checked : check 92 s0996_plain_contract = true := by decide +kernel
def s0996_plain : CertifiedContract :=
  ⟨996, 994, 0, .none, s0996_plain_contract, 92, s0996_plain_checked⟩

def s0997_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0997_zero_checked : check 357 s0997_zero_contract = true := by decide +kernel
def s0997_zero : CertifiedContract :=
  ⟨997, 1000, 0, .none, s0997_zero_contract, 357, s0997_zero_checked⟩

def s0997_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0997_positive_checked : check 363 s0997_positive_contract = true := by decide +kernel
def s0997_positive : CertifiedContract :=
  ⟨997, 998, 1, (.dec 0), s0997_positive_contract, 363, s0997_positive_checked⟩

def s0998_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0998_plain_checked : check 355 s0998_plain_contract = true := by decide +kernel
def s0998_plain : CertifiedContract :=
  ⟨998, 999, 0, (.inc 2), s0998_plain_contract, 355, s0998_plain_checked⟩

def s0999_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s0999_plain_checked : check 95 s0999_plain_contract = true := by decide +kernel
def s0999_plain : CertifiedContract :=
  ⟨999, 997, 0, .none, s0999_plain_contract, 95, s0999_plain_checked⟩

def s1000_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1000_zero_checked : check 363 s1000_zero_contract = true := by decide +kernel
def s1000_zero : CertifiedContract :=
  ⟨1000, 1004, 0, .none, s1000_zero_contract, 363, s1000_zero_checked⟩

def s1000_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1000_positive_checked : check 369 s1000_positive_contract = true := by decide +kernel
def s1000_positive : CertifiedContract :=
  ⟨1000, 1001, 1, (.dec 2), s1000_positive_contract, 369, s1000_positive_checked⟩

def s1001_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1001_plain_checked : check 382 s1001_plain_contract = true := by decide +kernel
def s1001_plain : CertifiedContract :=
  ⟨1001, 1002, 0, (.inc 5), s1001_plain_contract, 382, s1001_plain_checked⟩

def s1002_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1002_plain_checked : check 409 s1002_plain_contract = true := by decide +kernel
def s1002_plain : CertifiedContract :=
  ⟨1002, 1003, 0, (.inc 8), s1002_plain_contract, 409, s1002_plain_checked⟩

def s1003_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1003_plain_checked : check 110 s1003_plain_contract = true := by decide +kernel
def s1003_plain : CertifiedContract :=
  ⟨1003, 1000, 0, .none, s1003_plain_contract, 110, s1003_plain_checked⟩

def s1004_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, true, false] 0 .none⟩
theorem s1004_zero_checked : check 384 s1004_zero_contract = true := by decide +kernel
def s1004_zero : CertifiedContract :=
  ⟨1004, 1010, 0, .none, s1004_zero_contract, 384, s1004_zero_checked⟩

def s1004_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1004_positive_checked : check 387 s1004_positive_contract = true := by decide +kernel
def s1004_positive : CertifiedContract :=
  ⟨1004, 1005, 1, (.dec 8), s1004_positive_contract, 387, s1004_positive_checked⟩

def s1005_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1005_plain_checked : check 382 s1005_plain_contract = true := by decide +kernel
def s1005_plain : CertifiedContract :=
  ⟨1005, 1006, 0, (.inc 5), s1005_plain_contract, 382, s1005_plain_checked⟩

def s1006_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s1006_zero_checked : check 402 s1006_zero_contract = true := by decide +kernel
def s1006_zero : CertifiedContract :=
  ⟨1006, 1009, 0, .none, s1006_zero_contract, 402, s1006_zero_checked⟩

def s1006_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1006_positive_checked : check 405 s1006_positive_contract = true := by decide +kernel
def s1006_positive : CertifiedContract :=
  ⟨1006, 1007, 1, (.dec 8), s1006_positive_contract, 405, s1006_positive_checked⟩

def s1007_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1007_plain_checked : check 400 s1007_plain_contract = true := by decide +kernel
def s1007_plain : CertifiedContract :=
  ⟨1007, 1008, 0, (.inc 2), s1007_plain_contract, 400, s1007_plain_checked⟩

def s1008_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1008_plain_checked : check 110 s1008_plain_contract = true := by decide +kernel
def s1008_plain : CertifiedContract :=
  ⟨1008, 1006, 0, .none, s1008_plain_contract, 110, s1008_plain_checked⟩

def s1009_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1009_plain_checked : check 113 s1009_plain_contract = true := by decide +kernel
def s1009_plain : CertifiedContract :=
  ⟨1009, 1000, 0, .none, s1009_plain_contract, 113, s1009_plain_checked⟩

def s1010_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, true] 0 .none⟩
theorem s1010_zero_checked : check 372 s1010_zero_contract = true := by decide +kernel
def s1010_zero : CertifiedContract :=
  ⟨1010, 1013, 0, .none, s1010_zero_contract, 372, s1010_zero_checked⟩

def s1010_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1010_positive_checked : check 369 s1010_positive_contract = true := by decide +kernel
def s1010_positive : CertifiedContract :=
  ⟨1010, 1011, 1, (.dec 5), s1010_positive_contract, 369, s1010_positive_checked⟩

def s1011_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1011_plain_checked : check 382 s1011_plain_contract = true := by decide +kernel
def s1011_plain : CertifiedContract :=
  ⟨1011, 1012, 0, (.inc 0), s1011_plain_contract, 382, s1011_plain_checked⟩

def s1012_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, true, true, false] 0 .none⟩
theorem s1012_plain_checked : check 101 s1012_plain_contract = true := by decide +kernel
def s1012_plain : CertifiedContract :=
  ⟨1012, 1010, 0, .none, s1012_plain_contract, 101, s1012_plain_checked⟩

def s1013_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, false] 0 (.inc 2)⟩
theorem s1013_plain_checked : check 322 s1013_plain_contract = true := by decide +kernel
def s1013_plain : CertifiedContract :=
  ⟨1013, 1014, 0, (.inc 2), s1013_plain_contract, 322, s1013_plain_checked⟩

def s1014_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, true, false] 0 .none⟩
theorem s1014_zero_checked : check 366 s1014_zero_contract = true := by decide +kernel
def s1014_zero : CertifiedContract :=
  ⟨1014, 1022, 0, .none, s1014_zero_contract, 366, s1014_zero_checked⟩

def s1014_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s1014_positive_checked : check 372 s1014_positive_contract = true := by decide +kernel
def s1014_positive : CertifiedContract :=
  ⟨1014, 1015, 1, (.dec 0), s1014_positive_contract, 372, s1014_positive_checked⟩

def s1015_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s1015_plain_checked : check 382 s1015_plain_contract = true := by decide +kernel
def s1015_plain : CertifiedContract :=
  ⟨1015, 1016, 0, (.inc 5), s1015_plain_contract, 382, s1015_plain_checked⟩

def s1016_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1016_zero_checked : check 408 s1016_zero_contract = true := by decide +kernel
def s1016_zero : CertifiedContract :=
  ⟨1016, 1018, 0, .none, s1016_zero_contract, 408, s1016_zero_checked⟩

def s1016_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1016_positive_checked : check 414 s1016_positive_contract = true := by decide +kernel
def s1016_positive : CertifiedContract :=
  ⟨1016, 1017, 1, (.dec 8), s1016_positive_contract, 414, s1016_positive_checked⟩

def s1017_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s1017_plain_checked : check 113 s1017_plain_contract = true := by decide +kernel
def s1017_plain : CertifiedContract :=
  ⟨1017, 1021, 0, .none, s1017_plain_contract, 113, s1017_plain_checked⟩

def s1018_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s1018_zero_checked : check 420 s1018_zero_contract = true := by decide +kernel
def s1018_zero : CertifiedContract :=
  ⟨1018, 1021, 0, .none, s1018_zero_contract, 420, s1018_zero_checked⟩

def s1018_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1018_positive_checked : check 423 s1018_positive_contract = true := by decide +kernel
def s1018_positive : CertifiedContract :=
  ⟨1018, 1019, 1, (.dec 5), s1018_positive_contract, 423, s1018_positive_checked⟩

def s1019_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1019_plain_checked : check 427 s1019_plain_contract = true := by decide +kernel
def s1019_plain : CertifiedContract :=
  ⟨1019, 1020, 0, (.inc 8), s1019_plain_contract, 427, s1019_plain_checked⟩

def s1020_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1020_plain_checked : check 116 s1020_plain_contract = true := by decide +kernel
def s1020_plain : CertifiedContract :=
  ⟨1020, 1018, 0, .none, s1020_plain_contract, 116, s1020_plain_checked⟩

def s1021_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, false, false] 0 .none⟩
theorem s1021_plain_checked : check 107 s1021_plain_contract = true := by decide +kernel
def s1021_plain : CertifiedContract :=
  ⟨1021, 1014, 0, .none, s1021_plain_contract, 107, s1021_plain_checked⟩

def s1022_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s1022_zero_checked : check 366 s1022_zero_contract = true := by decide +kernel
def s1022_zero : CertifiedContract :=
  ⟨1022, 1025, 0, .none, s1022_zero_contract, 366, s1022_zero_checked⟩

def s1022_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s1022_positive_checked : check 369 s1022_positive_contract = true := by decide +kernel
def s1022_positive : CertifiedContract :=
  ⟨1022, 1023, 1, (.dec 5), s1022_positive_contract, 369, s1022_positive_checked⟩

def s1023_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s1023_plain_checked : check 382 s1023_plain_contract = true := by decide +kernel
def s1023_plain : CertifiedContract :=
  ⟨1023, 1024, 0, (.inc 0), s1023_plain_contract, 382, s1023_plain_checked⟩

def s1024_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, false, true, false] 0 .none⟩
theorem s1024_plain_checked : check 101 s1024_plain_contract = true := by decide +kernel
def s1024_plain : CertifiedContract :=
  ⟨1024, 1022, 0, .none, s1024_plain_contract, 101, s1024_plain_checked⟩

def s1025_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false] 0 .none⟩
theorem s1025_zero_checked : check 363 s1025_zero_contract = true := by decide +kernel
def s1025_zero : CertifiedContract :=
  ⟨1025, 1029, 0, .none, s1025_zero_contract, 363, s1025_zero_checked⟩

def s1025_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1025_positive_checked : check 369 s1025_positive_contract = true := by decide +kernel
def s1025_positive : CertifiedContract :=
  ⟨1025, 1026, 1, (.dec 2), s1025_positive_contract, 369, s1025_positive_checked⟩

def s1026_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1026_plain_checked : check 382 s1026_plain_contract = true := by decide +kernel
def s1026_plain : CertifiedContract :=
  ⟨1026, 1027, 0, (.inc 5), s1026_plain_contract, 382, s1026_plain_checked⟩

def s1027_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1027_plain_checked : check 409 s1027_plain_contract = true := by decide +kernel
def s1027_plain : CertifiedContract :=
  ⟨1027, 1028, 0, (.inc 8), s1027_plain_contract, 409, s1027_plain_checked⟩

def s1028_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s1028_plain_checked : check 110 s1028_plain_contract = true := by decide +kernel
def s1028_plain : CertifiedContract :=
  ⟨1028, 1025, 0, .none, s1028_plain_contract, 110, s1028_plain_checked⟩

def s1029_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, true, false] 0 .none⟩
theorem s1029_zero_checked : check 384 s1029_zero_contract = true := by decide +kernel
def s1029_zero : CertifiedContract :=
  ⟨1029, 1035, 0, .none, s1029_zero_contract, 384, s1029_zero_checked⟩

def s1029_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1029_positive_checked : check 387 s1029_positive_contract = true := by decide +kernel
def s1029_positive : CertifiedContract :=
  ⟨1029, 1030, 1, (.dec 8), s1029_positive_contract, 387, s1029_positive_checked⟩

def s1030_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1030_plain_checked : check 382 s1030_plain_contract = true := by decide +kernel
def s1030_plain : CertifiedContract :=
  ⟨1030, 1031, 0, (.inc 5), s1030_plain_contract, 382, s1030_plain_checked⟩

def s1031_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, true] 0 .none⟩
theorem s1031_zero_checked : check 402 s1031_zero_contract = true := by decide +kernel
def s1031_zero : CertifiedContract :=
  ⟨1031, 1034, 0, .none, s1031_zero_contract, 402, s1031_zero_checked⟩

end PA211.UserCandidate.RuntimeShards.S020
