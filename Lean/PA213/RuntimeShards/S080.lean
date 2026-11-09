module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S080
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s3936_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, true, false, false, true, true, false, false, true], rootFrame [true, true, true, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s3936_plain_checked : check 76 s3936_plain_contract = true := by decide +kernel
def s3936_plain : CertifiedContract :=
  ⟨3936, 3940, 0, .none, s3936_plain_contract, 76, s3936_plain_checked⟩

def s3937_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, true, true, true, true, true, false, false, true, true, false, true, false], rootFrame [true, true, true, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s3937_zero_checked : check 311 s3937_zero_contract = true := by decide +kernel
def s3937_zero : CertifiedContract :=
  ⟨3937, 3940, 0, .none, s3937_zero_contract, 311, s3937_zero_checked⟩

def s3937_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, true, true, true, true, true, false, false, true, true, false, true, false], rootFrame [true, true, true, true, true, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3937_positive_checked : check 314 s3937_positive_contract = true := by decide +kernel
def s3937_positive : CertifiedContract :=
  ⟨3937, 3938, 1, (.dec 5), s3937_positive_contract, 314, s3937_positive_checked⟩

def s3938_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, true, false, false, true, true, false, true, true, false], rootFrame [true, true, true, true, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3938_plain_checked : check 318 s3938_plain_contract = true := by decide +kernel
def s3938_plain : CertifiedContract :=
  ⟨3938, 3939, 0, (.inc 8), s3938_plain_contract, 318, s3938_plain_checked⟩

def s3939_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, true, true, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3939_plain_checked : check 79 s3939_plain_contract = true := by decide +kernel
def s3939_plain : CertifiedContract :=
  ⟨3939, 3937, 0, .none, s3939_plain_contract, 79, s3939_plain_checked⟩

def s3940_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, true, false, false, true, true, true], rootFrame [true, true, true, true, true, true, false, false, false] 0 .none⟩
theorem s3940_plain_checked : check 70 s3940_plain_contract = true := by decide +kernel
def s3940_plain : CertifiedContract :=
  ⟨3940, 3933, 0, .none, s3940_plain_contract, 70, s3940_plain_checked⟩

def s3941_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, true, true, true, true, true, false, true, false], rootFrame [true, true, true, true, true, true, true, false] 0 .none⟩
theorem s3941_zero_checked : check 257 s3941_zero_contract = true := by decide +kernel
def s3941_zero : CertifiedContract :=
  ⟨3941, 3944, 0, .none, s3941_zero_contract, 257, s3941_zero_checked⟩

def s3941_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, true, true, true, true, true, false, true, false], rootFrame [true, true, true, true, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3941_positive_checked : check 260 s3941_positive_contract = true := by decide +kernel
def s3941_positive : CertifiedContract :=
  ⟨3941, 3942, 1, (.dec 5), s3941_positive_contract, 260, s3941_positive_checked⟩

def s3942_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, true, false, true, true, false], rootFrame [true, true, true, true, true, true, false, true, true, true] 0 (.inc 0)⟩
theorem s3942_plain_checked : check 273 s3942_plain_contract = true := by decide +kernel
def s3942_plain : CertifiedContract :=
  ⟨3942, 3943, 0, (.inc 0), s3942_plain_contract, 273, s3942_plain_checked⟩

def s3943_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, true, false, true, true, true], rootFrame [true, true, true, true, true, true, false, true, false] 0 .none⟩
theorem s3943_plain_checked : check 64 s3943_plain_contract = true := by decide +kernel
def s3943_plain : CertifiedContract :=
  ⟨3943, 3941, 0, .none, s3943_plain_contract, 64, s3943_plain_checked⟩

def s3944_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, true, true, true, true, true, true, false], rootFrame [false, false, false, false] 1 .none⟩
theorem s3944_zero_checked : check 253 s3944_zero_contract = true := by decide +kernel
def s3944_zero : CertifiedContract :=
  ⟨3944, 0, 1, .none, s3944_zero_contract, 253, s3944_zero_checked⟩

def s3944_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, true, true, true, true, true, true, false], rootFrame [true, true, true, true, true, true, true, true, false] 1 (.dec 8)⟩
theorem s3944_positive_checked : check 233 s3944_positive_contract = true := by decide +kernel
def s3944_positive : CertifiedContract :=
  ⟨3944, 3945, 1, (.dec 8), s3944_positive_contract, 233, s3944_positive_checked⟩

def s3945_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, true, true, true, false], rootFrame [true, true, true, true, true, true, true, true, true] 0 (.inc 7)⟩
theorem s3945_plain_checked : check 264 s3945_plain_contract = true := by decide +kernel
def s3945_plain : CertifiedContract :=
  ⟨3945, 3946, 0, (.inc 7), s3945_plain_contract, 264, s3945_plain_checked⟩

def s3946_plain_contract : Contract :=
  ⟨(none), rootFrame [true, true, true, true, true, true, true, true, true], rootFrame [true, true, true, true, true, true, true, false] 0 .none⟩
theorem s3946_plain_checked : check 55 s3946_plain_contract = true := by decide +kernel
def s3946_plain : CertifiedContract :=
  ⟨3946, 3944, 0, .none, s3946_plain_contract, 55, s3946_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s3936_plain,
  s3937_zero,
  s3937_positive,
  s3938_plain,
  s3939_plain,
  s3940_plain,
  s3941_zero,
  s3941_positive,
  s3942_plain,
  s3943_plain,
  s3944_zero,
  s3944_positive,
  s3945_plain,
  s3946_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S080
