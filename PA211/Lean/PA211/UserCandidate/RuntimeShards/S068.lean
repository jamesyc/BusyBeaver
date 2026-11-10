import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S068
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s3350_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3350_positive_checked : check 369 s3350_positive_contract = true := by decide +kernel
def s3350_positive : CertifiedContract :=
  ⟨3350, 3351, 1, (.dec 5), s3350_positive_contract, 369, s3350_positive_checked⟩

def s3351_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3351_plain_checked : check 382 s3351_plain_contract = true := by decide +kernel
def s3351_plain : CertifiedContract :=
  ⟨3351, 3352, 0, (.inc 2), s3351_plain_contract, 382, s3351_plain_checked⟩

def s3352_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3352_plain_checked : check 385 s3352_plain_contract = true := by decide +kernel
def s3352_plain : CertifiedContract :=
  ⟨3352, 3353, 0, (.inc 2), s3352_plain_contract, 385, s3352_plain_checked⟩

def s3353_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3353_plain_checked : check 391 s3353_plain_contract = true := by decide +kernel
def s3353_plain : CertifiedContract :=
  ⟨3353, 3354, 0, (.inc 2), s3353_plain_contract, 391, s3353_plain_checked⟩

def s3354_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, true, true, true] 0 (.inc 2)⟩
theorem s3354_plain_checked : check 397 s3354_plain_contract = true := by decide +kernel
def s3354_plain : CertifiedContract :=
  ⟨3354, 3355, 0, (.inc 2), s3354_plain_contract, 397, s3354_plain_checked⟩

def s3355_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, true, true, true, true, false] 0 .none⟩
theorem s3355_plain_checked : check 98 s3355_plain_contract = true := by decide +kernel
def s3355_plain : CertifiedContract :=
  ⟨3355, 3350, 0, .none, s3355_plain_contract, 98, s3355_plain_checked⟩

def s3356_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, true, false] 0 .none⟩
theorem s3356_zero_checked : check 357 s3356_zero_contract = true := by decide +kernel
def s3356_zero : CertifiedContract :=
  ⟨3356, 3364, 0, .none, s3356_zero_contract, 357, s3356_zero_checked⟩

def s3356_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s3356_positive_checked : check 363 s3356_positive_contract = true := by decide +kernel
def s3356_positive : CertifiedContract :=
  ⟨3356, 3357, 1, (.dec 0), s3356_positive_contract, 363, s3356_positive_checked⟩

def s3357_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3357_plain_checked : check 373 s3357_plain_contract = true := by decide +kernel
def s3357_plain : CertifiedContract :=
  ⟨3357, 3358, 0, (.inc 5), s3357_plain_contract, 373, s3357_plain_checked⟩

def s3358_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3358_zero_checked : check 399 s3358_zero_contract = true := by decide +kernel
def s3358_zero : CertifiedContract :=
  ⟨3358, 3360, 0, .none, s3358_zero_contract, 399, s3358_zero_checked⟩

def s3358_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3358_positive_checked : check 405 s3358_positive_contract = true := by decide +kernel
def s3358_positive : CertifiedContract :=
  ⟨3358, 3359, 1, (.dec 8), s3358_positive_contract, 405, s3358_positive_checked⟩

def s3359_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s3359_plain_checked : check 110 s3359_plain_contract = true := by decide +kernel
def s3359_plain : CertifiedContract :=
  ⟨3359, 3363, 0, .none, s3359_plain_contract, 110, s3359_plain_checked⟩

def s3360_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s3360_zero_checked : check 411 s3360_zero_contract = true := by decide +kernel
def s3360_zero : CertifiedContract :=
  ⟨3360, 3363, 0, .none, s3360_zero_contract, 411, s3360_zero_checked⟩

def s3360_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3360_positive_checked : check 414 s3360_positive_contract = true := by decide +kernel
def s3360_positive : CertifiedContract :=
  ⟨3360, 3361, 1, (.dec 5), s3360_positive_contract, 414, s3360_positive_checked⟩

def s3361_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3361_plain_checked : check 418 s3361_plain_contract = true := by decide +kernel
def s3361_plain : CertifiedContract :=
  ⟨3361, 3362, 0, (.inc 8), s3361_plain_contract, 418, s3361_plain_checked⟩

def s3362_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3362_plain_checked : check 113 s3362_plain_contract = true := by decide +kernel
def s3362_plain : CertifiedContract :=
  ⟨3362, 3360, 0, .none, s3362_plain_contract, 113, s3362_plain_checked⟩

def s3363_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, false] 0 .none⟩
theorem s3363_plain_checked : check 104 s3363_plain_contract = true := by decide +kernel
def s3363_plain : CertifiedContract :=
  ⟨3363, 3356, 0, .none, s3363_plain_contract, 104, s3363_plain_checked⟩

def s3364_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s3364_zero_checked : check 357 s3364_zero_contract = true := by decide +kernel
def s3364_zero : CertifiedContract :=
  ⟨3364, 3367, 0, .none, s3364_zero_contract, 357, s3364_zero_checked⟩

def s3364_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s3364_positive_checked : check 360 s3364_positive_contract = true := by decide +kernel
def s3364_positive : CertifiedContract :=
  ⟨3364, 3365, 1, (.dec 5), s3364_positive_contract, 360, s3364_positive_checked⟩

def s3365_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s3365_plain_checked : check 373 s3365_plain_contract = true := by decide +kernel
def s3365_plain : CertifiedContract :=
  ⟨3365, 3366, 0, (.inc 0), s3365_plain_contract, 373, s3365_plain_checked⟩

def s3366_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, false, true, false] 0 .none⟩
theorem s3366_plain_checked : check 98 s3366_plain_contract = true := by decide +kernel
def s3366_plain : CertifiedContract :=
  ⟨3366, 3364, 0, .none, s3366_plain_contract, 98, s3366_plain_checked⟩

def s3367_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false] 0 .none⟩
theorem s3367_zero_checked : check 354 s3367_zero_contract = true := by decide +kernel
def s3367_zero : CertifiedContract :=
  ⟨3367, 3371, 0, .none, s3367_zero_contract, 354, s3367_zero_checked⟩

def s3367_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3367_positive_checked : check 360 s3367_positive_contract = true := by decide +kernel
def s3367_positive : CertifiedContract :=
  ⟨3367, 3368, 1, (.dec 2), s3367_positive_contract, 360, s3367_positive_checked⟩

def s3368_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3368_plain_checked : check 373 s3368_plain_contract = true := by decide +kernel
def s3368_plain : CertifiedContract :=
  ⟨3368, 3369, 0, (.inc 5), s3368_plain_contract, 373, s3368_plain_checked⟩

def s3369_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3369_plain_checked : check 400 s3369_plain_contract = true := by decide +kernel
def s3369_plain : CertifiedContract :=
  ⟨3369, 3370, 0, (.inc 8), s3369_plain_contract, 400, s3369_plain_checked⟩

def s3370_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s3370_plain_checked : check 107 s3370_plain_contract = true := by decide +kernel
def s3370_plain : CertifiedContract :=
  ⟨3370, 3367, 0, .none, s3370_plain_contract, 107, s3370_plain_checked⟩

def s3371_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, true, false] 0 .none⟩
theorem s3371_zero_checked : check 375 s3371_zero_contract = true := by decide +kernel
def s3371_zero : CertifiedContract :=
  ⟨3371, 3377, 0, .none, s3371_zero_contract, 375, s3371_zero_checked⟩

def s3371_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3371_positive_checked : check 378 s3371_positive_contract = true := by decide +kernel
def s3371_positive : CertifiedContract :=
  ⟨3371, 3372, 1, (.dec 8), s3371_positive_contract, 378, s3371_positive_checked⟩

def s3372_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3372_plain_checked : check 373 s3372_plain_contract = true := by decide +kernel
def s3372_plain : CertifiedContract :=
  ⟨3372, 3373, 0, (.inc 5), s3372_plain_contract, 373, s3372_plain_checked⟩

def s3373_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, true, true] 0 .none⟩
theorem s3373_zero_checked : check 393 s3373_zero_contract = true := by decide +kernel
def s3373_zero : CertifiedContract :=
  ⟨3373, 3376, 0, .none, s3373_zero_contract, 393, s3373_zero_checked⟩

def s3373_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3373_positive_checked : check 396 s3373_positive_contract = true := by decide +kernel
def s3373_positive : CertifiedContract :=
  ⟨3373, 3374, 1, (.dec 8), s3373_positive_contract, 396, s3373_positive_checked⟩

def s3374_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3374_plain_checked : check 391 s3374_plain_contract = true := by decide +kernel
def s3374_plain : CertifiedContract :=
  ⟨3374, 3375, 0, (.inc 2), s3374_plain_contract, 391, s3374_plain_checked⟩

def s3375_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s3375_plain_checked : check 107 s3375_plain_contract = true := by decide +kernel
def s3375_plain : CertifiedContract :=
  ⟨3375, 3373, 0, .none, s3375_plain_contract, 107, s3375_plain_checked⟩

def s3376_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s3376_plain_checked : check 110 s3376_plain_contract = true := by decide +kernel
def s3376_plain : CertifiedContract :=
  ⟨3376, 3367, 0, .none, s3376_plain_contract, 110, s3376_plain_checked⟩

def s3377_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, false, false] 0 .none⟩
theorem s3377_zero_checked : check 360 s3377_zero_contract = true := by decide +kernel
def s3377_zero : CertifiedContract :=
  ⟨3377, 3383, 0, .none, s3377_zero_contract, 360, s3377_zero_checked⟩

def s3377_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3377_positive_checked : check 360 s3377_positive_contract = true := by decide +kernel
def s3377_positive : CertifiedContract :=
  ⟨3377, 3378, 1, (.dec 5), s3377_positive_contract, 360, s3377_positive_checked⟩

def s3378_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3378_plain_checked : check 373 s3378_plain_contract = true := by decide +kernel
def s3378_plain : CertifiedContract :=
  ⟨3378, 3379, 0, (.inc 2), s3378_plain_contract, 373, s3378_plain_checked⟩

def s3379_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3379_plain_checked : check 376 s3379_plain_contract = true := by decide +kernel
def s3379_plain : CertifiedContract :=
  ⟨3379, 3380, 0, (.inc 2), s3379_plain_contract, 376, s3379_plain_checked⟩

def s3380_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3380_plain_checked : check 382 s3380_plain_contract = true := by decide +kernel
def s3380_plain : CertifiedContract :=
  ⟨3380, 3381, 0, (.inc 2), s3380_plain_contract, 382, s3380_plain_checked⟩

def s3381_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s3381_plain_checked : check 388 s3381_plain_contract = true := by decide +kernel
def s3381_plain : CertifiedContract :=
  ⟨3381, 3382, 0, (.inc 2), s3381_plain_contract, 388, s3381_plain_checked⟩

def s3382_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, false, true, true, false] 0 .none⟩
theorem s3382_plain_checked : check 95 s3382_plain_contract = true := by decide +kernel
def s3382_plain : CertifiedContract :=
  ⟨3382, 3377, 0, .none, s3382_plain_contract, 95, s3382_plain_checked⟩

def s3383_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s3383_zero_checked : check 363 s3383_zero_contract = true := by decide +kernel
def s3383_zero : CertifiedContract :=
  ⟨3383, 3386, 0, .none, s3383_zero_contract, 363, s3383_zero_checked⟩

def s3383_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, false, true, false] 1 (.dec 2)⟩
theorem s3383_positive_checked : check 369 s3383_positive_contract = true := by decide +kernel
def s3383_positive : CertifiedContract :=
  ⟨3383, 3384, 1, (.dec 2), s3383_positive_contract, 369, s3383_positive_checked⟩

def s3384_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, false, true, true] 0 (.inc 8)⟩
theorem s3384_plain_checked : check 382 s3384_plain_contract = true := by decide +kernel
def s3384_plain : CertifiedContract :=
  ⟨3384, 3385, 0, (.inc 8), s3384_plain_contract, 382, s3384_plain_checked⟩

def s3385_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, false, false] 0 .none⟩
theorem s3385_plain_checked : check 101 s3385_plain_contract = true := by decide +kernel
def s3385_plain : CertifiedContract :=
  ⟨3385, 3383, 0, .none, s3385_plain_contract, 101, s3385_plain_checked⟩

def s3386_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s3386_zero_checked : check 384 s3386_zero_contract = true := by decide +kernel
def s3386_zero : CertifiedContract :=
  ⟨3386, 3389, 0, .none, s3386_zero_contract, 384, s3386_zero_checked⟩

def s3386_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s3386_positive_checked : check 390 s3386_positive_contract = true := by decide +kernel
def s3386_positive : CertifiedContract :=
  ⟨3386, 3387, 1, (.dec 0), s3386_positive_contract, 390, s3386_positive_checked⟩

def s3387_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s3387_plain_checked : check 382 s3387_plain_contract = true := by decide +kernel
def s3387_plain : CertifiedContract :=
  ⟨3387, 3388, 0, (.inc 2), s3387_plain_contract, 382, s3387_plain_checked⟩

def s3388_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s3388_plain_checked : check 104 s3388_plain_contract = true := by decide +kernel
def s3388_plain : CertifiedContract :=
  ⟨3388, 3386, 0, .none, s3388_plain_contract, 104, s3388_plain_checked⟩

def s3389_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3389_zero_checked : check 390 s3389_zero_contract = true := by decide +kernel
def s3389_zero : CertifiedContract :=
  ⟨3389, 3393, 0, .none, s3389_zero_contract, 390, s3389_zero_checked⟩

def s3389_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3389_positive_checked : check 396 s3389_positive_contract = true := by decide +kernel
def s3389_positive : CertifiedContract :=
  ⟨3389, 3390, 1, (.dec 2), s3389_positive_contract, 396, s3389_positive_checked⟩

def s3390_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3390_plain_checked : check 409 s3390_plain_contract = true := by decide +kernel
def s3390_plain : CertifiedContract :=
  ⟨3390, 3391, 0, (.inc 5), s3390_plain_contract, 409, s3390_plain_checked⟩

def s3391_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3391_plain_checked : check 436 s3391_plain_contract = true := by decide +kernel
def s3391_plain : CertifiedContract :=
  ⟨3391, 3392, 0, (.inc 8), s3391_plain_contract, 436, s3391_plain_checked⟩

def s3392_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s3392_plain_checked : check 119 s3392_plain_contract = true := by decide +kernel
def s3392_plain : CertifiedContract :=
  ⟨3392, 3389, 0, .none, s3392_plain_contract, 119, s3392_plain_checked⟩

def s3393_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s3393_zero_checked : check 411 s3393_zero_contract = true := by decide +kernel
def s3393_zero : CertifiedContract :=
  ⟨3393, 3399, 0, .none, s3393_zero_contract, 411, s3393_zero_checked⟩

def s3393_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3393_positive_checked : check 414 s3393_positive_contract = true := by decide +kernel
def s3393_positive : CertifiedContract :=
  ⟨3393, 3394, 1, (.dec 8), s3393_positive_contract, 414, s3393_positive_checked⟩

def s3394_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3394_plain_checked : check 409 s3394_plain_contract = true := by decide +kernel
def s3394_plain : CertifiedContract :=
  ⟨3394, 3395, 0, (.inc 5), s3394_plain_contract, 409, s3394_plain_checked⟩

def s3395_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s3395_zero_checked : check 429 s3395_zero_contract = true := by decide +kernel
def s3395_zero : CertifiedContract :=
  ⟨3395, 3398, 0, .none, s3395_zero_contract, 429, s3395_zero_checked⟩

def s3395_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3395_positive_checked : check 432 s3395_positive_contract = true := by decide +kernel
def s3395_positive : CertifiedContract :=
  ⟨3395, 3396, 1, (.dec 8), s3395_positive_contract, 432, s3395_positive_checked⟩

def s3396_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3396_plain_checked : check 427 s3396_plain_contract = true := by decide +kernel
def s3396_plain : CertifiedContract :=
  ⟨3396, 3397, 0, (.inc 2), s3396_plain_contract, 427, s3396_plain_checked⟩

def s3397_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3397_plain_checked : check 119 s3397_plain_contract = true := by decide +kernel
def s3397_plain : CertifiedContract :=
  ⟨3397, 3395, 0, .none, s3397_plain_contract, 119, s3397_plain_checked⟩

def s3398_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s3398_plain_checked : check 122 s3398_plain_contract = true := by decide +kernel
def s3398_plain : CertifiedContract :=
  ⟨3398, 3389, 0, .none, s3398_plain_contract, 122, s3398_plain_checked⟩

def s3399_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, true] 0 .none⟩
theorem s3399_zero_checked : check 399 s3399_zero_contract = true := by decide +kernel
def s3399_zero : CertifiedContract :=
  ⟨3399, 3402, 0, .none, s3399_zero_contract, 399, s3399_zero_checked⟩

def s3399_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, true, true, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s3399_positive_checked : check 396 s3399_positive_contract = true := by decide +kernel
def s3399_positive : CertifiedContract :=
  ⟨3399, 3400, 1, (.dec 5), s3399_positive_contract, 396, s3399_positive_checked⟩

end PA211.UserCandidate.RuntimeShards.S068
