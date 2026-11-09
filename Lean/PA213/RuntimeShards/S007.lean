module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S007
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s0340_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0340_plain_checked : check 336 s0340_plain_contract = true := by decide +kernel
def s0340_plain : CertifiedContract :=
  ⟨340, 341, 0, (.inc 2), s0340_plain_contract, 336, s0340_plain_checked⟩

def s0341_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0341_plain_checked : check 339 s0341_plain_contract = true := by decide +kernel
def s0341_plain : CertifiedContract :=
  ⟨341, 342, 0, (.inc 2), s0341_plain_contract, 339, s0341_plain_checked⟩

def s0342_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0342_plain_checked : check 336 s0342_plain_contract = true := by decide +kernel
def s0342_plain : CertifiedContract :=
  ⟨342, 343, 0, (.inc 2), s0342_plain_contract, 336, s0342_plain_checked⟩

def s0343_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s0343_plain_checked : check 342 s0343_plain_contract = true := by decide +kernel
def s0343_plain : CertifiedContract :=
  ⟨343, 344, 0, (.inc 2), s0343_plain_contract, 342, s0343_plain_checked⟩

def s0344_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, false] 0 .none⟩
theorem s0344_plain_checked : check 82 s0344_plain_contract = true := by decide +kernel
def s0344_plain : CertifiedContract :=
  ⟨344, 339, 0, .none, s0344_plain_contract, 82, s0344_plain_checked⟩

def s0345_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, false, false] 0 .none⟩
theorem s0345_zero_checked : check 308 s0345_zero_contract = true := by decide +kernel
def s0345_zero : CertifiedContract :=
  ⟨345, 348, 0, .none, s0345_zero_contract, 308, s0345_zero_checked⟩

def s0345_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, true, false] 1 (.dec 2)⟩
theorem s0345_positive_checked : check 314 s0345_positive_contract = true := by decide +kernel
def s0345_positive : CertifiedContract :=
  ⟨345, 346, 1, (.dec 2), s0345_positive_contract, 314, s0345_positive_checked⟩

def s0346_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, true, true] 0 (.inc 8)⟩
theorem s0346_plain_checked : check 327 s0346_plain_contract = true := by decide +kernel
def s0346_plain : CertifiedContract :=
  ⟨346, 347, 0, (.inc 8), s0346_plain_contract, 327, s0346_plain_checked⟩

def s0347_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s0347_plain_checked : check 82 s0347_plain_contract = true := by decide +kernel
def s0347_plain : CertifiedContract :=
  ⟨347, 345, 0, .none, s0347_plain_contract, 82, s0347_plain_checked⟩

def s0348_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s0348_zero_checked : check 329 s0348_zero_contract = true := by decide +kernel
def s0348_zero : CertifiedContract :=
  ⟨348, 351, 0, .none, s0348_zero_contract, 329, s0348_zero_checked⟩

def s0348_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0348_positive_checked : check 335 s0348_positive_contract = true := by decide +kernel
def s0348_positive : CertifiedContract :=
  ⟨348, 349, 1, (.dec 0), s0348_positive_contract, 335, s0348_positive_checked⟩

def s0349_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0349_plain_checked : check 327 s0349_plain_contract = true := by decide +kernel
def s0349_plain : CertifiedContract :=
  ⟨349, 350, 0, (.inc 2), s0349_plain_contract, 327, s0349_plain_checked⟩

def s0350_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, false, false] 0 .none⟩
theorem s0350_plain_checked : check 85 s0350_plain_contract = true := by decide +kernel
def s0350_plain : CertifiedContract :=
  ⟨350, 348, 0, .none, s0350_plain_contract, 85, s0350_plain_checked⟩

def s0351_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s0351_zero_checked : check 335 s0351_zero_contract = true := by decide +kernel
def s0351_zero : CertifiedContract :=
  ⟨351, 355, 0, .none, s0351_zero_contract, 335, s0351_zero_checked⟩

def s0351_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0351_positive_checked : check 341 s0351_positive_contract = true := by decide +kernel
def s0351_positive : CertifiedContract :=
  ⟨351, 352, 1, (.dec 2), s0351_positive_contract, 341, s0351_positive_checked⟩

def s0352_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0352_plain_checked : check 354 s0352_plain_contract = true := by decide +kernel
def s0352_plain : CertifiedContract :=
  ⟨352, 353, 0, (.inc 5), s0352_plain_contract, 354, s0352_plain_checked⟩

def s0353_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0353_plain_checked : check 381 s0353_plain_contract = true := by decide +kernel
def s0353_plain : CertifiedContract :=
  ⟨353, 354, 0, (.inc 8), s0353_plain_contract, 381, s0353_plain_checked⟩

def s0354_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s0354_plain_checked : check 100 s0354_plain_contract = true := by decide +kernel
def s0354_plain : CertifiedContract :=
  ⟨354, 351, 0, .none, s0354_plain_contract, 100, s0354_plain_checked⟩

def s0355_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s0355_zero_checked : check 356 s0355_zero_contract = true := by decide +kernel
def s0355_zero : CertifiedContract :=
  ⟨355, 361, 0, .none, s0355_zero_contract, 356, s0355_zero_checked⟩

def s0355_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0355_positive_checked : check 359 s0355_positive_contract = true := by decide +kernel
def s0355_positive : CertifiedContract :=
  ⟨355, 356, 1, (.dec 8), s0355_positive_contract, 359, s0355_positive_checked⟩

def s0356_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0356_plain_checked : check 354 s0356_plain_contract = true := by decide +kernel
def s0356_plain : CertifiedContract :=
  ⟨356, 357, 0, (.inc 5), s0356_plain_contract, 354, s0356_plain_checked⟩

def s0357_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s0357_zero_checked : check 374 s0357_zero_contract = true := by decide +kernel
def s0357_zero : CertifiedContract :=
  ⟨357, 360, 0, .none, s0357_zero_contract, 374, s0357_zero_checked⟩

def s0357_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0357_positive_checked : check 377 s0357_positive_contract = true := by decide +kernel
def s0357_positive : CertifiedContract :=
  ⟨357, 358, 1, (.dec 8), s0357_positive_contract, 377, s0357_positive_checked⟩

def s0358_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0358_plain_checked : check 372 s0358_plain_contract = true := by decide +kernel
def s0358_plain : CertifiedContract :=
  ⟨358, 359, 0, (.inc 2), s0358_plain_contract, 372, s0358_plain_checked⟩

def s0359_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0359_plain_checked : check 100 s0359_plain_contract = true := by decide +kernel
def s0359_plain : CertifiedContract :=
  ⟨359, 357, 0, .none, s0359_plain_contract, 100, s0359_plain_checked⟩

def s0360_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s0360_plain_checked : check 103 s0360_plain_contract = true := by decide +kernel
def s0360_plain : CertifiedContract :=
  ⟨360, 351, 0, .none, s0360_plain_contract, 103, s0360_plain_checked⟩

def s0361_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s0361_zero_checked : check 344 s0361_zero_contract = true := by decide +kernel
def s0361_zero : CertifiedContract :=
  ⟨361, 364, 0, .none, s0361_zero_contract, 344, s0361_zero_checked⟩

def s0361_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0361_positive_checked : check 341 s0361_positive_contract = true := by decide +kernel
def s0361_positive : CertifiedContract :=
  ⟨361, 362, 1, (.dec 5), s0361_positive_contract, 341, s0361_positive_checked⟩

def s0362_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0362_plain_checked : check 354 s0362_plain_contract = true := by decide +kernel
def s0362_plain : CertifiedContract :=
  ⟨362, 363, 0, (.inc 0), s0362_plain_contract, 354, s0362_plain_checked⟩

def s0363_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s0363_plain_checked : check 91 s0363_plain_contract = true := by decide +kernel
def s0363_plain : CertifiedContract :=
  ⟨363, 361, 0, .none, s0363_plain_contract, 91, s0363_plain_checked⟩

def s0364_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s0364_zero_checked : check 308 s0364_zero_contract = true := by decide +kernel
def s0364_zero : CertifiedContract :=
  ⟨364, 368, 0, .none, s0364_zero_contract, 308, s0364_zero_checked⟩

def s0364_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, true, false] 1 (.dec 7)⟩
theorem s0364_positive_checked : check 314 s0364_positive_contract = true := by decide +kernel
def s0364_positive : CertifiedContract :=
  ⟨364, 365, 1, (.dec 7), s0364_positive_contract, 314, s0364_positive_checked⟩

def s0365_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0365_plain_checked : check 318 s0365_plain_contract = true := by decide +kernel
def s0365_plain : CertifiedContract :=
  ⟨365, 366, 0, (.inc 2), s0365_plain_contract, 318, s0365_plain_checked⟩

def s0366_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0366_plain_checked : check 345 s0366_plain_contract = true := by decide +kernel
def s0366_plain : CertifiedContract :=
  ⟨366, 367, 0, (.inc 8), s0366_plain_contract, 345, s0366_plain_checked⟩

def s0367_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s0367_plain_checked : check 88 s0367_plain_contract = true := by decide +kernel
def s0367_plain : CertifiedContract :=
  ⟨367, 364, 0, .none, s0367_plain_contract, 88, s0367_plain_checked⟩

def s0368_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0368_zero_checked : check 314 s0368_zero_contract = true := by decide +kernel
def s0368_zero : CertifiedContract :=
  ⟨368, 371, 0, .none, s0368_zero_contract, 314, s0368_zero_checked⟩

def s0368_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, true, true, false] 1 (.dec 8)⟩
theorem s0368_positive_checked : check 314 s0368_positive_contract = true := by decide +kernel
def s0368_positive : CertifiedContract :=
  ⟨368, 369, 1, (.dec 8), s0368_positive_contract, 314, s0368_positive_checked⟩

def s0369_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, true, true, true] 0 (.inc 7)⟩
theorem s0369_plain_checked : check 345 s0369_plain_contract = true := by decide +kernel
def s0369_plain : CertifiedContract :=
  ⟨369, 370, 0, (.inc 7), s0369_plain_contract, 345, s0369_plain_checked⟩

def s0370_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s0370_plain_checked : check 82 s0370_plain_contract = true := by decide +kernel
def s0370_plain : CertifiedContract :=
  ⟨370, 368, 0, .none, s0370_plain_contract, 82, s0370_plain_checked⟩

def s0371_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, false, false] 0 .none⟩
theorem s0371_zero_checked : check 308 s0371_zero_contract = true := by decide +kernel
def s0371_zero : CertifiedContract :=
  ⟨371, 374, 0, .none, s0371_zero_contract, 308, s0371_zero_checked⟩

def s0371_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0371_positive_checked : check 314 s0371_positive_contract = true := by decide +kernel
def s0371_positive : CertifiedContract :=
  ⟨371, 372, 1, (.dec 2), s0371_positive_contract, 314, s0371_positive_checked⟩

def s0372_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, true, true] 0 (.inc 8)⟩
theorem s0372_plain_checked : check 327 s0372_plain_contract = true := by decide +kernel
def s0372_plain : CertifiedContract :=
  ⟨372, 373, 0, (.inc 8), s0372_plain_contract, 327, s0372_plain_checked⟩

def s0373_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0373_plain_checked : check 82 s0373_plain_contract = true := by decide +kernel
def s0373_plain : CertifiedContract :=
  ⟨373, 371, 0, .none, s0373_plain_contract, 82, s0373_plain_checked⟩

def s0374_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0374_zero_checked : check 329 s0374_zero_contract = true := by decide +kernel
def s0374_zero : CertifiedContract :=
  ⟨374, 377, 0, .none, s0374_zero_contract, 329, s0374_zero_checked⟩

def s0374_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0374_positive_checked : check 335 s0374_positive_contract = true := by decide +kernel
def s0374_positive : CertifiedContract :=
  ⟨374, 375, 1, (.dec 0), s0374_positive_contract, 335, s0374_positive_checked⟩

def s0375_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0375_plain_checked : check 327 s0375_plain_contract = true := by decide +kernel
def s0375_plain : CertifiedContract :=
  ⟨375, 376, 0, (.inc 2), s0375_plain_contract, 327, s0375_plain_checked⟩

def s0376_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, false, false] 0 .none⟩
theorem s0376_plain_checked : check 85 s0376_plain_contract = true := by decide +kernel
def s0376_plain : CertifiedContract :=
  ⟨376, 374, 0, .none, s0376_plain_contract, 85, s0376_plain_checked⟩

def s0377_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0377_zero_checked : check 335 s0377_zero_contract = true := by decide +kernel
def s0377_zero : CertifiedContract :=
  ⟨377, 381, 0, .none, s0377_zero_contract, 335, s0377_zero_checked⟩

def s0377_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0377_positive_checked : check 341 s0377_positive_contract = true := by decide +kernel
def s0377_positive : CertifiedContract :=
  ⟨377, 378, 1, (.dec 2), s0377_positive_contract, 341, s0377_positive_checked⟩

def s0378_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0378_plain_checked : check 354 s0378_plain_contract = true := by decide +kernel
def s0378_plain : CertifiedContract :=
  ⟨378, 379, 0, (.inc 5), s0378_plain_contract, 354, s0378_plain_checked⟩

def s0379_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0379_plain_checked : check 381 s0379_plain_contract = true := by decide +kernel
def s0379_plain : CertifiedContract :=
  ⟨379, 380, 0, (.inc 8), s0379_plain_contract, 381, s0379_plain_checked⟩

def s0380_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0380_plain_checked : check 100 s0380_plain_contract = true := by decide +kernel
def s0380_plain : CertifiedContract :=
  ⟨380, 377, 0, .none, s0380_plain_contract, 100, s0380_plain_checked⟩

def s0381_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s0381_zero_checked : check 356 s0381_zero_contract = true := by decide +kernel
def s0381_zero : CertifiedContract :=
  ⟨381, 387, 0, .none, s0381_zero_contract, 356, s0381_zero_checked⟩

def s0381_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0381_positive_checked : check 359 s0381_positive_contract = true := by decide +kernel
def s0381_positive : CertifiedContract :=
  ⟨381, 382, 1, (.dec 8), s0381_positive_contract, 359, s0381_positive_checked⟩

def s0382_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0382_plain_checked : check 354 s0382_plain_contract = true := by decide +kernel
def s0382_plain : CertifiedContract :=
  ⟨382, 383, 0, (.inc 5), s0382_plain_contract, 354, s0382_plain_checked⟩

def s0383_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s0383_zero_checked : check 374 s0383_zero_contract = true := by decide +kernel
def s0383_zero : CertifiedContract :=
  ⟨383, 386, 0, .none, s0383_zero_contract, 374, s0383_zero_checked⟩

def s0383_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0383_positive_checked : check 377 s0383_positive_contract = true := by decide +kernel
def s0383_positive : CertifiedContract :=
  ⟨383, 384, 1, (.dec 8), s0383_positive_contract, 377, s0383_positive_checked⟩

def s0384_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0384_plain_checked : check 372 s0384_plain_contract = true := by decide +kernel
def s0384_plain : CertifiedContract :=
  ⟨384, 385, 0, (.inc 2), s0384_plain_contract, 372, s0384_plain_checked⟩

def s0385_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0385_plain_checked : check 100 s0385_plain_contract = true := by decide +kernel
def s0385_plain : CertifiedContract :=
  ⟨385, 383, 0, .none, s0385_plain_contract, 100, s0385_plain_checked⟩

def s0386_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0386_plain_checked : check 103 s0386_plain_contract = true := by decide +kernel
def s0386_plain : CertifiedContract :=
  ⟨386, 377, 0, .none, s0386_plain_contract, 103, s0386_plain_checked⟩

def s0387_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, false, false] 0 .none⟩
theorem s0387_zero_checked : check 344 s0387_zero_contract = true := by decide +kernel
def s0387_zero : CertifiedContract :=
  ⟨387, 390, 0, .none, s0387_zero_contract, 344, s0387_zero_checked⟩

def s0387_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0387_positive_checked : check 341 s0387_positive_contract = true := by decide +kernel
def s0387_positive : CertifiedContract :=
  ⟨387, 388, 1, (.dec 5), s0387_positive_contract, 341, s0387_positive_checked⟩

def s0388_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0388_plain_checked : check 354 s0388_plain_contract = true := by decide +kernel
def s0388_plain : CertifiedContract :=
  ⟨388, 389, 0, (.inc 0), s0388_plain_contract, 354, s0388_plain_checked⟩

def s0389_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s0389_plain_checked : check 91 s0389_plain_contract = true := by decide +kernel
def s0389_plain : CertifiedContract :=
  ⟨389, 387, 0, .none, s0389_plain_contract, 91, s0389_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s0340_plain,
  s0341_plain,
  s0342_plain,
  s0343_plain,
  s0344_plain,
  s0345_zero,
  s0345_positive,
  s0346_plain,
  s0347_plain,
  s0348_zero,
  s0348_positive,
  s0349_plain,
  s0350_plain,
  s0351_zero,
  s0351_positive,
  s0352_plain,
  s0353_plain,
  s0354_plain,
  s0355_zero,
  s0355_positive,
  s0356_plain,
  s0357_zero,
  s0357_positive,
  s0358_plain,
  s0359_plain,
  s0360_plain,
  s0361_zero,
  s0361_positive,
  s0362_plain,
  s0363_plain,
  s0364_zero,
  s0364_positive,
  s0365_plain,
  s0366_plain,
  s0367_plain,
  s0368_zero,
  s0368_positive,
  s0369_plain,
  s0370_plain,
  s0371_zero,
  s0371_positive,
  s0372_plain,
  s0373_plain,
  s0374_zero,
  s0374_positive,
  s0375_plain,
  s0376_plain,
  s0377_zero,
  s0377_positive,
  s0378_plain,
  s0379_plain,
  s0380_plain,
  s0381_zero,
  s0381_positive,
  s0382_plain,
  s0383_zero,
  s0383_positive,
  s0384_plain,
  s0385_plain,
  s0386_plain,
  s0387_zero,
  s0387_positive,
  s0388_plain,
  s0389_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S007
