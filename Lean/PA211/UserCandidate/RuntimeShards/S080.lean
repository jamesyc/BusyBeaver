module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S080
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s3936_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, true, false, false, true, true, false, false, true], rootFrame [true, true, true, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s3936_plain_checked : check 77 s3936_plain_contract = true := by decide +kernel
def s3936_plain : CertifiedContract :=
  ⟨3936, 3940, 0, .none, s3936_plain_contract, 77, s3936_plain_checked⟩

def s3937_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, true, true, true, true, true, false, false, true, true, false, true, false], rootFrame [true, true, true, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s3937_zero_checked : check 312 s3937_zero_contract = true := by decide +kernel
def s3937_zero : CertifiedContract :=
  ⟨3937, 3940, 0, .none, s3937_zero_contract, 312, s3937_zero_checked⟩

def s3937_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, true, true, true, true, true, false, false, true, true, false, true, false], rootFrame [true, true, true, true, true, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3937_positive_checked : check 315 s3937_positive_contract = true := by decide +kernel
def s3937_positive : CertifiedContract :=
  ⟨3937, 3938, 1, (.dec 5), s3937_positive_contract, 315, s3937_positive_checked⟩

def s3938_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, true, false, false, true, true, false, true, true, false], rootFrame [true, true, true, true, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3938_plain_checked : check 319 s3938_plain_contract = true := by decide +kernel
def s3938_plain : CertifiedContract :=
  ⟨3938, 3939, 0, (.inc 8), s3938_plain_contract, 319, s3938_plain_checked⟩

def s3939_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, true, true, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3939_plain_checked : check 80 s3939_plain_contract = true := by decide +kernel
def s3939_plain : CertifiedContract :=
  ⟨3939, 3937, 0, .none, s3939_plain_contract, 80, s3939_plain_checked⟩

def s3940_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, true, false, false, true, true, true], rootFrame [true, true, true, true, true, true, false, false, false] 0 .none⟩
theorem s3940_plain_checked : check 71 s3940_plain_contract = true := by decide +kernel
def s3940_plain : CertifiedContract :=
  ⟨3940, 3933, 0, .none, s3940_plain_contract, 71, s3940_plain_checked⟩

def s3941_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, true, true, true, true, true, false, true, false], rootFrame [true, true, true, true, true, true, true, false] 0 .none⟩
theorem s3941_zero_checked : check 258 s3941_zero_contract = true := by decide +kernel
def s3941_zero : CertifiedContract :=
  ⟨3941, 3944, 0, .none, s3941_zero_contract, 258, s3941_zero_checked⟩

def s3941_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, true, true, true, true, true, false, true, false], rootFrame [true, true, true, true, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3941_positive_checked : check 261 s3941_positive_contract = true := by decide +kernel
def s3941_positive : CertifiedContract :=
  ⟨3941, 3942, 1, (.dec 5), s3941_positive_contract, 261, s3941_positive_checked⟩

def s3942_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, true, false, true, true, false], rootFrame [true, true, true, true, true, true, false, true, true, true] 0 (.inc 0)⟩
theorem s3942_plain_checked : check 274 s3942_plain_contract = true := by decide +kernel
def s3942_plain : CertifiedContract :=
  ⟨3942, 3943, 0, (.inc 0), s3942_plain_contract, 274, s3942_plain_checked⟩

def s3943_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, true, false, true, true, true], rootFrame [true, true, true, true, true, true, false, true, false] 0 .none⟩
theorem s3943_plain_checked : check 65 s3943_plain_contract = true := by decide +kernel
def s3943_plain : CertifiedContract :=
  ⟨3943, 3941, 0, .none, s3943_plain_contract, 65, s3943_plain_checked⟩

def s3944_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, true, true, true, true, true, true, false], rootFrame [false, false, false, false] 1 .none⟩
theorem s3944_zero_checked : check 254 s3944_zero_contract = true := by decide +kernel
def s3944_zero : CertifiedContract :=
  ⟨3944, 0, 1, .none, s3944_zero_contract, 254, s3944_zero_checked⟩

def s3944_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, true, true, true, true, true, true, false], rootFrame [true, true, true, true, true, true, true, true, false] 1 (.dec 8)⟩
theorem s3944_positive_checked : check 234 s3944_positive_contract = true := by decide +kernel
def s3944_positive : CertifiedContract :=
  ⟨3944, 3945, 1, (.dec 8), s3944_positive_contract, 234, s3944_positive_checked⟩

def s3945_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, true, true, true, false], rootFrame [true, true, true, true, true, true, true, true, true] 0 (.inc 7)⟩
theorem s3945_plain_checked : check 265 s3945_plain_contract = true := by decide +kernel
def s3945_plain : CertifiedContract :=
  ⟨3945, 3946, 0, (.inc 7), s3945_plain_contract, 265, s3945_plain_checked⟩

def s3946_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, true, true, true, true], rootFrame [true, true, true, true, true, true, true, false] 0 .none⟩
theorem s3946_plain_checked : check 56 s3946_plain_contract = true := by decide +kernel
def s3946_plain : CertifiedContract :=
  ⟨3946, 3944, 0, .none, s3946_plain_contract, 56, s3946_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S080
