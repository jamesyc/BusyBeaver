import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S007
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s0340_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0340_plain_checked : check 337 s0340_plain_contract = true := by decide +kernel
def s0340_plain : CertifiedContract :=
  ⟨340, 341, 0, (.inc 2), s0340_plain_contract, 337, s0340_plain_checked⟩

def s0341_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0341_plain_checked : check 340 s0341_plain_contract = true := by decide +kernel
def s0341_plain : CertifiedContract :=
  ⟨341, 342, 0, (.inc 2), s0341_plain_contract, 340, s0341_plain_checked⟩

def s0342_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0342_plain_checked : check 346 s0342_plain_contract = true := by decide +kernel
def s0342_plain : CertifiedContract :=
  ⟨342, 343, 0, (.inc 2), s0342_plain_contract, 346, s0342_plain_checked⟩

def s0343_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s0343_plain_checked : check 352 s0343_plain_contract = true := by decide +kernel
def s0343_plain : CertifiedContract :=
  ⟨343, 344, 0, (.inc 2), s0343_plain_contract, 352, s0343_plain_checked⟩

def s0344_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, false] 0 .none⟩
theorem s0344_plain_checked : check 83 s0344_plain_contract = true := by decide +kernel
def s0344_plain : CertifiedContract :=
  ⟨344, 339, 0, .none, s0344_plain_contract, 83, s0344_plain_checked⟩

def s0345_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, false, false] 0 .none⟩
theorem s0345_zero_checked : check 309 s0345_zero_contract = true := by decide +kernel
def s0345_zero : CertifiedContract :=
  ⟨345, 348, 0, .none, s0345_zero_contract, 309, s0345_zero_checked⟩

def s0345_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, true, false] 1 (.dec 2)⟩
theorem s0345_positive_checked : check 315 s0345_positive_contract = true := by decide +kernel
def s0345_positive : CertifiedContract :=
  ⟨345, 346, 1, (.dec 2), s0345_positive_contract, 315, s0345_positive_checked⟩

def s0346_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, true, true] 0 (.inc 8)⟩
theorem s0346_plain_checked : check 328 s0346_plain_contract = true := by decide +kernel
def s0346_plain : CertifiedContract :=
  ⟨346, 347, 0, (.inc 8), s0346_plain_contract, 328, s0346_plain_checked⟩

def s0347_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s0347_plain_checked : check 83 s0347_plain_contract = true := by decide +kernel
def s0347_plain : CertifiedContract :=
  ⟨347, 345, 0, .none, s0347_plain_contract, 83, s0347_plain_checked⟩

def s0348_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s0348_zero_checked : check 330 s0348_zero_contract = true := by decide +kernel
def s0348_zero : CertifiedContract :=
  ⟨348, 351, 0, .none, s0348_zero_contract, 330, s0348_zero_checked⟩

def s0348_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0348_positive_checked : check 336 s0348_positive_contract = true := by decide +kernel
def s0348_positive : CertifiedContract :=
  ⟨348, 349, 1, (.dec 0), s0348_positive_contract, 336, s0348_positive_checked⟩

def s0349_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0349_plain_checked : check 328 s0349_plain_contract = true := by decide +kernel
def s0349_plain : CertifiedContract :=
  ⟨349, 350, 0, (.inc 2), s0349_plain_contract, 328, s0349_plain_checked⟩

def s0350_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, false, false] 0 .none⟩
theorem s0350_plain_checked : check 86 s0350_plain_contract = true := by decide +kernel
def s0350_plain : CertifiedContract :=
  ⟨350, 348, 0, .none, s0350_plain_contract, 86, s0350_plain_checked⟩

def s0351_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s0351_zero_checked : check 336 s0351_zero_contract = true := by decide +kernel
def s0351_zero : CertifiedContract :=
  ⟨351, 355, 0, .none, s0351_zero_contract, 336, s0351_zero_checked⟩

def s0351_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0351_positive_checked : check 342 s0351_positive_contract = true := by decide +kernel
def s0351_positive : CertifiedContract :=
  ⟨351, 352, 1, (.dec 2), s0351_positive_contract, 342, s0351_positive_checked⟩

def s0352_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0352_plain_checked : check 355 s0352_plain_contract = true := by decide +kernel
def s0352_plain : CertifiedContract :=
  ⟨352, 353, 0, (.inc 5), s0352_plain_contract, 355, s0352_plain_checked⟩

def s0353_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0353_plain_checked : check 382 s0353_plain_contract = true := by decide +kernel
def s0353_plain : CertifiedContract :=
  ⟨353, 354, 0, (.inc 8), s0353_plain_contract, 382, s0353_plain_checked⟩

def s0354_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s0354_plain_checked : check 101 s0354_plain_contract = true := by decide +kernel
def s0354_plain : CertifiedContract :=
  ⟨354, 351, 0, .none, s0354_plain_contract, 101, s0354_plain_checked⟩

def s0355_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s0355_zero_checked : check 357 s0355_zero_contract = true := by decide +kernel
def s0355_zero : CertifiedContract :=
  ⟨355, 361, 0, .none, s0355_zero_contract, 357, s0355_zero_checked⟩

def s0355_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0355_positive_checked : check 360 s0355_positive_contract = true := by decide +kernel
def s0355_positive : CertifiedContract :=
  ⟨355, 356, 1, (.dec 8), s0355_positive_contract, 360, s0355_positive_checked⟩

def s0356_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0356_plain_checked : check 355 s0356_plain_contract = true := by decide +kernel
def s0356_plain : CertifiedContract :=
  ⟨356, 357, 0, (.inc 5), s0356_plain_contract, 355, s0356_plain_checked⟩

def s0357_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s0357_zero_checked : check 375 s0357_zero_contract = true := by decide +kernel
def s0357_zero : CertifiedContract :=
  ⟨357, 360, 0, .none, s0357_zero_contract, 375, s0357_zero_checked⟩

def s0357_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0357_positive_checked : check 378 s0357_positive_contract = true := by decide +kernel
def s0357_positive : CertifiedContract :=
  ⟨357, 358, 1, (.dec 8), s0357_positive_contract, 378, s0357_positive_checked⟩

def s0358_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0358_plain_checked : check 373 s0358_plain_contract = true := by decide +kernel
def s0358_plain : CertifiedContract :=
  ⟨358, 359, 0, (.inc 2), s0358_plain_contract, 373, s0358_plain_checked⟩

def s0359_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0359_plain_checked : check 101 s0359_plain_contract = true := by decide +kernel
def s0359_plain : CertifiedContract :=
  ⟨359, 357, 0, .none, s0359_plain_contract, 101, s0359_plain_checked⟩

def s0360_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s0360_plain_checked : check 104 s0360_plain_contract = true := by decide +kernel
def s0360_plain : CertifiedContract :=
  ⟨360, 351, 0, .none, s0360_plain_contract, 104, s0360_plain_checked⟩

def s0361_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s0361_zero_checked : check 345 s0361_zero_contract = true := by decide +kernel
def s0361_zero : CertifiedContract :=
  ⟨361, 364, 0, .none, s0361_zero_contract, 345, s0361_zero_checked⟩

def s0361_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0361_positive_checked : check 342 s0361_positive_contract = true := by decide +kernel
def s0361_positive : CertifiedContract :=
  ⟨361, 362, 1, (.dec 5), s0361_positive_contract, 342, s0361_positive_checked⟩

def s0362_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0362_plain_checked : check 355 s0362_plain_contract = true := by decide +kernel
def s0362_plain : CertifiedContract :=
  ⟨362, 363, 0, (.inc 0), s0362_plain_contract, 355, s0362_plain_checked⟩

def s0363_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s0363_plain_checked : check 92 s0363_plain_contract = true := by decide +kernel
def s0363_plain : CertifiedContract :=
  ⟨363, 361, 0, .none, s0363_plain_contract, 92, s0363_plain_checked⟩

def s0364_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s0364_zero_checked : check 309 s0364_zero_contract = true := by decide +kernel
def s0364_zero : CertifiedContract :=
  ⟨364, 368, 0, .none, s0364_zero_contract, 309, s0364_zero_checked⟩

def s0364_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, true, false] 1 (.dec 7)⟩
theorem s0364_positive_checked : check 315 s0364_positive_contract = true := by decide +kernel
def s0364_positive : CertifiedContract :=
  ⟨364, 365, 1, (.dec 7), s0364_positive_contract, 315, s0364_positive_checked⟩

def s0365_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0365_plain_checked : check 319 s0365_plain_contract = true := by decide +kernel
def s0365_plain : CertifiedContract :=
  ⟨365, 366, 0, (.inc 2), s0365_plain_contract, 319, s0365_plain_checked⟩

def s0366_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0366_plain_checked : check 346 s0366_plain_contract = true := by decide +kernel
def s0366_plain : CertifiedContract :=
  ⟨366, 367, 0, (.inc 8), s0366_plain_contract, 346, s0366_plain_checked⟩

def s0367_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s0367_plain_checked : check 89 s0367_plain_contract = true := by decide +kernel
def s0367_plain : CertifiedContract :=
  ⟨367, 364, 0, .none, s0367_plain_contract, 89, s0367_plain_checked⟩

def s0368_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0368_zero_checked : check 315 s0368_zero_contract = true := by decide +kernel
def s0368_zero : CertifiedContract :=
  ⟨368, 371, 0, .none, s0368_zero_contract, 315, s0368_zero_checked⟩

def s0368_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, true, true, false] 1 (.dec 8)⟩
theorem s0368_positive_checked : check 315 s0368_positive_contract = true := by decide +kernel
def s0368_positive : CertifiedContract :=
  ⟨368, 369, 1, (.dec 8), s0368_positive_contract, 315, s0368_positive_checked⟩

def s0369_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, true, true, true] 0 (.inc 7)⟩
theorem s0369_plain_checked : check 346 s0369_plain_contract = true := by decide +kernel
def s0369_plain : CertifiedContract :=
  ⟨369, 370, 0, (.inc 7), s0369_plain_contract, 346, s0369_plain_checked⟩

def s0370_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s0370_plain_checked : check 83 s0370_plain_contract = true := by decide +kernel
def s0370_plain : CertifiedContract :=
  ⟨370, 368, 0, .none, s0370_plain_contract, 83, s0370_plain_checked⟩

def s0371_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, false, false] 0 .none⟩
theorem s0371_zero_checked : check 309 s0371_zero_contract = true := by decide +kernel
def s0371_zero : CertifiedContract :=
  ⟨371, 374, 0, .none, s0371_zero_contract, 309, s0371_zero_checked⟩

def s0371_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0371_positive_checked : check 315 s0371_positive_contract = true := by decide +kernel
def s0371_positive : CertifiedContract :=
  ⟨371, 372, 1, (.dec 2), s0371_positive_contract, 315, s0371_positive_checked⟩

def s0372_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, true, true] 0 (.inc 8)⟩
theorem s0372_plain_checked : check 328 s0372_plain_contract = true := by decide +kernel
def s0372_plain : CertifiedContract :=
  ⟨372, 373, 0, (.inc 8), s0372_plain_contract, 328, s0372_plain_checked⟩

def s0373_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0373_plain_checked : check 83 s0373_plain_contract = true := by decide +kernel
def s0373_plain : CertifiedContract :=
  ⟨373, 371, 0, .none, s0373_plain_contract, 83, s0373_plain_checked⟩

def s0374_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0374_zero_checked : check 330 s0374_zero_contract = true := by decide +kernel
def s0374_zero : CertifiedContract :=
  ⟨374, 377, 0, .none, s0374_zero_contract, 330, s0374_zero_checked⟩

def s0374_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0374_positive_checked : check 336 s0374_positive_contract = true := by decide +kernel
def s0374_positive : CertifiedContract :=
  ⟨374, 375, 1, (.dec 0), s0374_positive_contract, 336, s0374_positive_checked⟩

def s0375_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0375_plain_checked : check 328 s0375_plain_contract = true := by decide +kernel
def s0375_plain : CertifiedContract :=
  ⟨375, 376, 0, (.inc 2), s0375_plain_contract, 328, s0375_plain_checked⟩

def s0376_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, false, false] 0 .none⟩
theorem s0376_plain_checked : check 86 s0376_plain_contract = true := by decide +kernel
def s0376_plain : CertifiedContract :=
  ⟨376, 374, 0, .none, s0376_plain_contract, 86, s0376_plain_checked⟩

def s0377_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0377_zero_checked : check 336 s0377_zero_contract = true := by decide +kernel
def s0377_zero : CertifiedContract :=
  ⟨377, 381, 0, .none, s0377_zero_contract, 336, s0377_zero_checked⟩

def s0377_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0377_positive_checked : check 342 s0377_positive_contract = true := by decide +kernel
def s0377_positive : CertifiedContract :=
  ⟨377, 378, 1, (.dec 2), s0377_positive_contract, 342, s0377_positive_checked⟩

def s0378_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0378_plain_checked : check 355 s0378_plain_contract = true := by decide +kernel
def s0378_plain : CertifiedContract :=
  ⟨378, 379, 0, (.inc 5), s0378_plain_contract, 355, s0378_plain_checked⟩

def s0379_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0379_plain_checked : check 382 s0379_plain_contract = true := by decide +kernel
def s0379_plain : CertifiedContract :=
  ⟨379, 380, 0, (.inc 8), s0379_plain_contract, 382, s0379_plain_checked⟩

def s0380_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0380_plain_checked : check 101 s0380_plain_contract = true := by decide +kernel
def s0380_plain : CertifiedContract :=
  ⟨380, 377, 0, .none, s0380_plain_contract, 101, s0380_plain_checked⟩

def s0381_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s0381_zero_checked : check 357 s0381_zero_contract = true := by decide +kernel
def s0381_zero : CertifiedContract :=
  ⟨381, 387, 0, .none, s0381_zero_contract, 357, s0381_zero_checked⟩

def s0381_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0381_positive_checked : check 360 s0381_positive_contract = true := by decide +kernel
def s0381_positive : CertifiedContract :=
  ⟨381, 382, 1, (.dec 8), s0381_positive_contract, 360, s0381_positive_checked⟩

def s0382_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0382_plain_checked : check 355 s0382_plain_contract = true := by decide +kernel
def s0382_plain : CertifiedContract :=
  ⟨382, 383, 0, (.inc 5), s0382_plain_contract, 355, s0382_plain_checked⟩

def s0383_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s0383_zero_checked : check 375 s0383_zero_contract = true := by decide +kernel
def s0383_zero : CertifiedContract :=
  ⟨383, 386, 0, .none, s0383_zero_contract, 375, s0383_zero_checked⟩

def s0383_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0383_positive_checked : check 378 s0383_positive_contract = true := by decide +kernel
def s0383_positive : CertifiedContract :=
  ⟨383, 384, 1, (.dec 8), s0383_positive_contract, 378, s0383_positive_checked⟩

def s0384_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0384_plain_checked : check 373 s0384_plain_contract = true := by decide +kernel
def s0384_plain : CertifiedContract :=
  ⟨384, 385, 0, (.inc 2), s0384_plain_contract, 373, s0384_plain_checked⟩

def s0385_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0385_plain_checked : check 101 s0385_plain_contract = true := by decide +kernel
def s0385_plain : CertifiedContract :=
  ⟨385, 383, 0, .none, s0385_plain_contract, 101, s0385_plain_checked⟩

def s0386_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0386_plain_checked : check 104 s0386_plain_contract = true := by decide +kernel
def s0386_plain : CertifiedContract :=
  ⟨386, 377, 0, .none, s0386_plain_contract, 104, s0386_plain_checked⟩

def s0387_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, false, false] 0 .none⟩
theorem s0387_zero_checked : check 345 s0387_zero_contract = true := by decide +kernel
def s0387_zero : CertifiedContract :=
  ⟨387, 390, 0, .none, s0387_zero_contract, 345, s0387_zero_checked⟩

def s0387_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0387_positive_checked : check 342 s0387_positive_contract = true := by decide +kernel
def s0387_positive : CertifiedContract :=
  ⟨387, 388, 1, (.dec 5), s0387_positive_contract, 342, s0387_positive_checked⟩

def s0388_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0388_plain_checked : check 355 s0388_plain_contract = true := by decide +kernel
def s0388_plain : CertifiedContract :=
  ⟨388, 389, 0, (.inc 0), s0388_plain_contract, 355, s0388_plain_checked⟩

def s0389_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s0389_plain_checked : check 92 s0389_plain_contract = true := by decide +kernel
def s0389_plain : CertifiedContract :=
  ⟨389, 387, 0, .none, s0389_plain_contract, 92, s0389_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S007
