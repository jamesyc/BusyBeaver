import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S003
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s0145_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0145_plain_checked : check 337 s0145_plain_contract = true := by decide +kernel
def s0145_plain : CertifiedContract :=
  ⟨145, 146, 0, (.inc 2), s0145_plain_contract, 337, s0145_plain_checked⟩

def s0146_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0146_plain_checked : check 89 s0146_plain_contract = true := by decide +kernel
def s0146_plain : CertifiedContract :=
  ⟨146, 144, 0, .none, s0146_plain_contract, 89, s0146_plain_checked⟩

def s0147_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0147_plain_checked : check 92 s0147_plain_contract = true := by decide +kernel
def s0147_plain : CertifiedContract :=
  ⟨147, 138, 0, .none, s0147_plain_contract, 92, s0147_plain_checked⟩

def s0148_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s0148_zero_checked : check 309 s0148_zero_contract = true := by decide +kernel
def s0148_zero : CertifiedContract :=
  ⟨148, 151, 0, .none, s0148_zero_contract, 309, s0148_zero_checked⟩

def s0148_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0148_positive_checked : check 306 s0148_positive_contract = true := by decide +kernel
def s0148_positive : CertifiedContract :=
  ⟨148, 149, 1, (.dec 5), s0148_positive_contract, 306, s0148_positive_checked⟩

def s0149_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0149_plain_checked : check 319 s0149_plain_contract = true := by decide +kernel
def s0149_plain : CertifiedContract :=
  ⟨149, 150, 0, (.inc 0), s0149_plain_contract, 319, s0149_plain_checked⟩

def s0150_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s0150_plain_checked : check 80 s0150_plain_contract = true := by decide +kernel
def s0150_plain : CertifiedContract :=
  ⟨150, 148, 0, .none, s0150_plain_contract, 80, s0150_plain_checked⟩

def s0151_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s0151_zero_checked : check 273 s0151_zero_contract = true := by decide +kernel
def s0151_zero : CertifiedContract :=
  ⟨151, 155, 0, .none, s0151_zero_contract, 273, s0151_zero_checked⟩

def s0151_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, false, true, true, false, true, false] 1 (.dec 3)⟩
theorem s0151_positive_checked : check 279 s0151_positive_contract = true := by decide +kernel
def s0151_positive : CertifiedContract :=
  ⟨151, 152, 1, (.dec 3), s0151_positive_contract, 279, s0151_positive_checked⟩

def s0152_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0152_plain_checked : check 292 s0152_plain_contract = true := by decide +kernel
def s0152_plain : CertifiedContract :=
  ⟨152, 153, 0, (.inc 2), s0152_plain_contract, 292, s0152_plain_checked⟩

def s0153_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0153_plain_checked : check 319 s0153_plain_contract = true := by decide +kernel
def s0153_plain : CertifiedContract :=
  ⟨153, 154, 0, (.inc 8), s0153_plain_contract, 319, s0153_plain_checked⟩

def s0154_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s0154_plain_checked : check 80 s0154_plain_contract = true := by decide +kernel
def s0154_plain : CertifiedContract :=
  ⟨154, 151, 0, .none, s0154_plain_contract, 80, s0154_plain_checked⟩

def s0155_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, false] 0 .none⟩
theorem s0155_zero_checked : check 282 s0155_zero_contract = true := by decide +kernel
def s0155_zero : CertifiedContract :=
  ⟨155, 158, 0, .none, s0155_zero_contract, 282, s0155_zero_checked⟩

def s0155_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s0155_positive_checked : check 279 s0155_positive_contract = true := by decide +kernel
def s0155_positive : CertifiedContract :=
  ⟨155, 156, 1, (.dec 8), s0155_positive_contract, 279, s0155_positive_checked⟩

def s0156_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, false, true, true, true, true, true] 0 (.inc 3)⟩
theorem s0156_plain_checked : check 295 s0156_plain_contract = true := by decide +kernel
def s0156_plain : CertifiedContract :=
  ⟨156, 157, 0, (.inc 3), s0156_plain_contract, 295, s0156_plain_checked⟩

def s0157_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s0157_plain_checked : check 71 s0157_plain_contract = true := by decide +kernel
def s0157_plain : CertifiedContract :=
  ⟨157, 155, 0, .none, s0157_plain_contract, 71, s0157_plain_checked⟩

def s0158_zero_contract : Contract :=
  ⟨(some (1, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, true, false] 0 .none⟩
theorem s0158_zero_checked : check 303 s0158_zero_contract = true := by decide +kernel
def s0158_zero : CertifiedContract :=
  ⟨158, 166, 0, .none, s0158_zero_contract, 303, s0158_zero_checked⟩

def s0158_positive_contract : Contract :=
  ⟨(some (1, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, true, false] 1 (.dec 1)⟩
theorem s0158_positive_checked : check 309 s0158_positive_contract = true := by decide +kernel
def s0158_positive : CertifiedContract :=
  ⟨158, 159, 1, (.dec 1), s0158_positive_contract, 309, s0158_positive_checked⟩

def s0159_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0159_plain_checked : check 301 s0159_plain_contract = true := by decide +kernel
def s0159_plain : CertifiedContract :=
  ⟨159, 160, 0, (.inc 5), s0159_plain_contract, 301, s0159_plain_checked⟩

def s0160_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0160_zero_checked : check 327 s0160_zero_contract = true := by decide +kernel
def s0160_zero : CertifiedContract :=
  ⟨160, 162, 0, .none, s0160_zero_contract, 327, s0160_zero_checked⟩

def s0160_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0160_positive_checked : check 333 s0160_positive_contract = true := by decide +kernel
def s0160_positive : CertifiedContract :=
  ⟨160, 161, 1, (.dec 8), s0160_positive_contract, 333, s0160_positive_checked⟩

def s0161_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s0161_plain_checked : check 86 s0161_plain_contract = true := by decide +kernel
def s0161_plain : CertifiedContract :=
  ⟨161, 165, 0, .none, s0161_plain_contract, 86, s0161_plain_checked⟩

def s0162_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s0162_zero_checked : check 339 s0162_zero_contract = true := by decide +kernel
def s0162_zero : CertifiedContract :=
  ⟨162, 165, 0, .none, s0162_zero_contract, 339, s0162_zero_checked⟩

def s0162_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0162_positive_checked : check 342 s0162_positive_contract = true := by decide +kernel
def s0162_positive : CertifiedContract :=
  ⟨162, 163, 1, (.dec 5), s0162_positive_contract, 342, s0162_positive_checked⟩

def s0163_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0163_plain_checked : check 346 s0163_plain_contract = true := by decide +kernel
def s0163_plain : CertifiedContract :=
  ⟨163, 164, 0, (.inc 8), s0163_plain_contract, 346, s0163_plain_checked⟩

def s0164_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0164_plain_checked : check 89 s0164_plain_contract = true := by decide +kernel
def s0164_plain : CertifiedContract :=
  ⟨164, 162, 0, .none, s0164_plain_contract, 89, s0164_plain_checked⟩

def s0165_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, false, false] 0 .none⟩
theorem s0165_plain_checked : check 80 s0165_plain_contract = true := by decide +kernel
def s0165_plain : CertifiedContract :=
  ⟨165, 158, 0, .none, s0165_plain_contract, 80, s0165_plain_checked⟩

def s0166_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s0166_zero_checked : check 303 s0166_zero_contract = true := by decide +kernel
def s0166_zero : CertifiedContract :=
  ⟨166, 169, 0, .none, s0166_zero_contract, 303, s0166_zero_checked⟩

def s0166_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0166_positive_checked : check 306 s0166_positive_contract = true := by decide +kernel
def s0166_positive : CertifiedContract :=
  ⟨166, 167, 1, (.dec 5), s0166_positive_contract, 306, s0166_positive_checked⟩

def s0167_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, true, true, true] 0 (.inc 1)⟩
theorem s0167_plain_checked : check 319 s0167_plain_contract = true := by decide +kernel
def s0167_plain : CertifiedContract :=
  ⟨167, 168, 0, (.inc 1), s0167_plain_contract, 319, s0167_plain_checked⟩

def s0168_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, false, false, true, false] 0 .none⟩
theorem s0168_plain_checked : check 83 s0168_plain_contract = true := by decide +kernel
def s0168_plain : CertifiedContract :=
  ⟨168, 166, 0, .none, s0168_plain_contract, 83, s0168_plain_checked⟩

def s0169_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s0169_zero_checked : check 276 s0169_zero_contract = true := by decide +kernel
def s0169_zero : CertifiedContract :=
  ⟨169, 172, 0, .none, s0169_zero_contract, 276, s0169_zero_checked⟩

def s0169_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, false, true, true, false] 1 (.dec 8)⟩
theorem s0169_positive_checked : check 279 s0169_positive_contract = true := by decide +kernel
def s0169_positive : CertifiedContract :=
  ⟨169, 170, 1, (.dec 8), s0169_positive_contract, 279, s0169_positive_checked⟩

def s0170_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, false, true, true, true] 0 (.inc 7)⟩
theorem s0170_plain_checked : check 310 s0170_plain_contract = true := by decide +kernel
def s0170_plain : CertifiedContract :=
  ⟨170, 171, 0, (.inc 7), s0170_plain_contract, 310, s0170_plain_checked⟩

def s0171_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s0171_plain_checked : check 71 s0171_plain_contract = true := by decide +kernel
def s0171_plain : CertifiedContract :=
  ⟨171, 169, 0, .none, s0171_plain_contract, 71, s0171_plain_checked⟩

def s0172_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s0172_zero_checked : check 303 s0172_zero_contract = true := by decide +kernel
def s0172_zero : CertifiedContract :=
  ⟨172, 180, 0, .none, s0172_zero_contract, 303, s0172_zero_checked⟩

def s0172_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s0172_positive_checked : check 309 s0172_positive_contract = true := by decide +kernel
def s0172_positive : CertifiedContract :=
  ⟨172, 173, 1, (.dec 0), s0172_positive_contract, 309, s0172_positive_checked⟩

def s0173_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0173_plain_checked : check 319 s0173_plain_contract = true := by decide +kernel
def s0173_plain : CertifiedContract :=
  ⟨173, 174, 0, (.inc 5), s0173_plain_contract, 319, s0173_plain_checked⟩

def s0174_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0174_zero_checked : check 345 s0174_zero_contract = true := by decide +kernel
def s0174_zero : CertifiedContract :=
  ⟨174, 176, 0, .none, s0174_zero_contract, 345, s0174_zero_checked⟩

def s0174_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0174_positive_checked : check 351 s0174_positive_contract = true := by decide +kernel
def s0174_positive : CertifiedContract :=
  ⟨174, 175, 1, (.dec 8), s0174_positive_contract, 351, s0174_positive_checked⟩

def s0175_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s0175_plain_checked : check 92 s0175_plain_contract = true := by decide +kernel
def s0175_plain : CertifiedContract :=
  ⟨175, 179, 0, .none, s0175_plain_contract, 92, s0175_plain_checked⟩

def s0176_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s0176_zero_checked : check 357 s0176_zero_contract = true := by decide +kernel
def s0176_zero : CertifiedContract :=
  ⟨176, 179, 0, .none, s0176_zero_contract, 357, s0176_zero_checked⟩

def s0176_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0176_positive_checked : check 360 s0176_positive_contract = true := by decide +kernel
def s0176_positive : CertifiedContract :=
  ⟨176, 177, 1, (.dec 5), s0176_positive_contract, 360, s0176_positive_checked⟩

def s0177_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0177_plain_checked : check 364 s0177_plain_contract = true := by decide +kernel
def s0177_plain : CertifiedContract :=
  ⟨177, 178, 0, (.inc 8), s0177_plain_contract, 364, s0177_plain_checked⟩

def s0178_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0178_plain_checked : check 95 s0178_plain_contract = true := by decide +kernel
def s0178_plain : CertifiedContract :=
  ⟨178, 176, 0, .none, s0178_plain_contract, 95, s0178_plain_checked⟩

def s0179_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s0179_plain_checked : check 86 s0179_plain_contract = true := by decide +kernel
def s0179_plain : CertifiedContract :=
  ⟨179, 172, 0, .none, s0179_plain_contract, 86, s0179_plain_checked⟩

def s0180_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0180_zero_checked : check 303 s0180_zero_contract = true := by decide +kernel
def s0180_zero : CertifiedContract :=
  ⟨180, 183, 0, .none, s0180_zero_contract, 303, s0180_zero_checked⟩

def s0180_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0180_positive_checked : check 306 s0180_positive_contract = true := by decide +kernel
def s0180_positive : CertifiedContract :=
  ⟨180, 181, 1, (.dec 5), s0180_positive_contract, 306, s0180_positive_checked⟩

def s0181_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s0181_plain_checked : check 319 s0181_plain_contract = true := by decide +kernel
def s0181_plain : CertifiedContract :=
  ⟨181, 182, 0, (.inc 0), s0181_plain_contract, 319, s0181_plain_checked⟩

def s0182_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s0182_plain_checked : check 80 s0182_plain_contract = true := by decide +kernel
def s0182_plain : CertifiedContract :=
  ⟨182, 180, 0, .none, s0182_plain_contract, 80, s0182_plain_checked⟩

def s0183_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s0183_zero_checked : check 300 s0183_zero_contract = true := by decide +kernel
def s0183_zero : CertifiedContract :=
  ⟨183, 187, 0, .none, s0183_zero_contract, 300, s0183_zero_checked⟩

def s0183_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0183_positive_checked : check 306 s0183_positive_contract = true := by decide +kernel
def s0183_positive : CertifiedContract :=
  ⟨183, 184, 1, (.dec 2), s0183_positive_contract, 306, s0183_positive_checked⟩

def s0184_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0184_plain_checked : check 319 s0184_plain_contract = true := by decide +kernel
def s0184_plain : CertifiedContract :=
  ⟨184, 185, 0, (.inc 5), s0184_plain_contract, 319, s0184_plain_checked⟩

def s0185_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0185_plain_checked : check 346 s0185_plain_contract = true := by decide +kernel
def s0185_plain : CertifiedContract :=
  ⟨185, 186, 0, (.inc 8), s0185_plain_contract, 346, s0185_plain_checked⟩

def s0186_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0186_plain_checked : check 89 s0186_plain_contract = true := by decide +kernel
def s0186_plain : CertifiedContract :=
  ⟨186, 183, 0, .none, s0186_plain_contract, 89, s0186_plain_checked⟩

def s0187_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s0187_zero_checked : check 321 s0187_zero_contract = true := by decide +kernel
def s0187_zero : CertifiedContract :=
  ⟨187, 193, 0, .none, s0187_zero_contract, 321, s0187_zero_checked⟩

def s0187_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0187_positive_checked : check 324 s0187_positive_contract = true := by decide +kernel
def s0187_positive : CertifiedContract :=
  ⟨187, 188, 1, (.dec 8), s0187_positive_contract, 324, s0187_positive_checked⟩

def s0188_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0188_plain_checked : check 319 s0188_plain_contract = true := by decide +kernel
def s0188_plain : CertifiedContract :=
  ⟨188, 189, 0, (.inc 5), s0188_plain_contract, 319, s0188_plain_checked⟩

def s0189_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s0189_zero_checked : check 339 s0189_zero_contract = true := by decide +kernel
def s0189_zero : CertifiedContract :=
  ⟨189, 192, 0, .none, s0189_zero_contract, 339, s0189_zero_checked⟩

def s0189_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0189_positive_checked : check 342 s0189_positive_contract = true := by decide +kernel
def s0189_positive : CertifiedContract :=
  ⟨189, 190, 1, (.dec 8), s0189_positive_contract, 342, s0189_positive_checked⟩

def s0190_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0190_plain_checked : check 337 s0190_plain_contract = true := by decide +kernel
def s0190_plain : CertifiedContract :=
  ⟨190, 191, 0, (.inc 2), s0190_plain_contract, 337, s0190_plain_checked⟩

def s0191_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0191_plain_checked : check 89 s0191_plain_contract = true := by decide +kernel
def s0191_plain : CertifiedContract :=
  ⟨191, 189, 0, .none, s0191_plain_contract, 89, s0191_plain_checked⟩

def s0192_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0192_plain_checked : check 92 s0192_plain_contract = true := by decide +kernel
def s0192_plain : CertifiedContract :=
  ⟨192, 183, 0, .none, s0192_plain_contract, 92, s0192_plain_checked⟩

def s0193_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, false, false, false, false] 0 .none⟩
theorem s0193_zero_checked : check 306 s0193_zero_contract = true := by decide +kernel
def s0193_zero : CertifiedContract :=
  ⟨193, 199, 0, .none, s0193_zero_contract, 306, s0193_zero_checked⟩

end PA211.UserCandidate.RuntimeShards.S003
