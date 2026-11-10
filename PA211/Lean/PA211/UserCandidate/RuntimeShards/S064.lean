import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S064
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s3153_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3153_positive_checked : check 423 s3153_positive_contract = true := by decide +kernel
def s3153_positive : CertifiedContract :=
  ⟨3153, 3154, 1, (.dec 5), s3153_positive_contract, 423, s3153_positive_checked⟩

def s3154_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3154_plain_checked : check 427 s3154_plain_contract = true := by decide +kernel
def s3154_plain : CertifiedContract :=
  ⟨3154, 3155, 0, (.inc 8), s3154_plain_contract, 427, s3154_plain_checked⟩

def s3155_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s3155_plain_checked : check 116 s3155_plain_contract = true := by decide +kernel
def s3155_plain : CertifiedContract :=
  ⟨3155, 3153, 0, .none, s3155_plain_contract, 116, s3155_plain_checked⟩

def s3156_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s3156_plain_checked : check 107 s3156_plain_contract = true := by decide +kernel
def s3156_plain : CertifiedContract :=
  ⟨3156, 3149, 0, .none, s3156_plain_contract, 107, s3156_plain_checked⟩

def s3157_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s3157_zero_checked : check 366 s3157_zero_contract = true := by decide +kernel
def s3157_zero : CertifiedContract :=
  ⟨3157, 3160, 0, .none, s3157_zero_contract, 366, s3157_zero_checked⟩

def s3157_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3157_positive_checked : check 369 s3157_positive_contract = true := by decide +kernel
def s3157_positive : CertifiedContract :=
  ⟨3157, 3158, 1, (.dec 5), s3157_positive_contract, 369, s3157_positive_checked⟩

def s3158_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, true, true, true] 0 (.inc 0)⟩
theorem s3158_plain_checked : check 382 s3158_plain_contract = true := by decide +kernel
def s3158_plain : CertifiedContract :=
  ⟨3158, 3159, 0, (.inc 0), s3158_plain_contract, 382, s3158_plain_checked⟩

def s3159_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, false, true, false] 0 .none⟩
theorem s3159_plain_checked : check 101 s3159_plain_contract = true := by decide +kernel
def s3159_plain : CertifiedContract :=
  ⟨3159, 3157, 0, .none, s3159_plain_contract, 101, s3159_plain_checked⟩

def s3160_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3160_zero_checked : check 363 s3160_zero_contract = true := by decide +kernel
def s3160_zero : CertifiedContract :=
  ⟨3160, 3164, 0, .none, s3160_zero_contract, 363, s3160_zero_checked⟩

def s3160_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3160_positive_checked : check 369 s3160_positive_contract = true := by decide +kernel
def s3160_positive : CertifiedContract :=
  ⟨3160, 3161, 1, (.dec 2), s3160_positive_contract, 369, s3160_positive_checked⟩

def s3161_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3161_plain_checked : check 382 s3161_plain_contract = true := by decide +kernel
def s3161_plain : CertifiedContract :=
  ⟨3161, 3162, 0, (.inc 5), s3161_plain_contract, 382, s3161_plain_checked⟩

def s3162_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3162_plain_checked : check 409 s3162_plain_contract = true := by decide +kernel
def s3162_plain : CertifiedContract :=
  ⟨3162, 3163, 0, (.inc 8), s3162_plain_contract, 409, s3162_plain_checked⟩

def s3163_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s3163_plain_checked : check 110 s3163_plain_contract = true := by decide +kernel
def s3163_plain : CertifiedContract :=
  ⟨3163, 3160, 0, .none, s3163_plain_contract, 110, s3163_plain_checked⟩

def s3164_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s3164_zero_checked : check 384 s3164_zero_contract = true := by decide +kernel
def s3164_zero : CertifiedContract :=
  ⟨3164, 3170, 0, .none, s3164_zero_contract, 384, s3164_zero_checked⟩

def s3164_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3164_positive_checked : check 387 s3164_positive_contract = true := by decide +kernel
def s3164_positive : CertifiedContract :=
  ⟨3164, 3165, 1, (.dec 8), s3164_positive_contract, 387, s3164_positive_checked⟩

def s3165_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3165_plain_checked : check 382 s3165_plain_contract = true := by decide +kernel
def s3165_plain : CertifiedContract :=
  ⟨3165, 3166, 0, (.inc 5), s3165_plain_contract, 382, s3165_plain_checked⟩

def s3166_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s3166_zero_checked : check 402 s3166_zero_contract = true := by decide +kernel
def s3166_zero : CertifiedContract :=
  ⟨3166, 3169, 0, .none, s3166_zero_contract, 402, s3166_zero_checked⟩

def s3166_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3166_positive_checked : check 405 s3166_positive_contract = true := by decide +kernel
def s3166_positive : CertifiedContract :=
  ⟨3166, 3167, 1, (.dec 8), s3166_positive_contract, 405, s3166_positive_checked⟩

def s3167_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3167_plain_checked : check 400 s3167_plain_contract = true := by decide +kernel
def s3167_plain : CertifiedContract :=
  ⟨3167, 3168, 0, (.inc 2), s3167_plain_contract, 400, s3167_plain_checked⟩

def s3168_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3168_plain_checked : check 110 s3168_plain_contract = true := by decide +kernel
def s3168_plain : CertifiedContract :=
  ⟨3168, 3166, 0, .none, s3168_plain_contract, 110, s3168_plain_checked⟩

def s3169_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s3169_plain_checked : check 113 s3169_plain_contract = true := by decide +kernel
def s3169_plain : CertifiedContract :=
  ⟨3169, 3160, 0, .none, s3169_plain_contract, 113, s3169_plain_checked⟩

def s3170_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, false, false] 0 .none⟩
theorem s3170_zero_checked : check 372 s3170_zero_contract = true := by decide +kernel
def s3170_zero : CertifiedContract :=
  ⟨3170, 3176, 0, .none, s3170_zero_contract, 372, s3170_zero_checked⟩

def s3170_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s3170_positive_checked : check 369 s3170_positive_contract = true := by decide +kernel
def s3170_positive : CertifiedContract :=
  ⟨3170, 3171, 1, (.dec 5), s3170_positive_contract, 369, s3170_positive_checked⟩

def s3171_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s3171_plain_checked : check 382 s3171_plain_contract = true := by decide +kernel
def s3171_plain : CertifiedContract :=
  ⟨3171, 3172, 0, (.inc 2), s3171_plain_contract, 382, s3171_plain_checked⟩

def s3172_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s3172_plain_checked : check 385 s3172_plain_contract = true := by decide +kernel
def s3172_plain : CertifiedContract :=
  ⟨3172, 3173, 0, (.inc 2), s3172_plain_contract, 385, s3172_plain_checked⟩

def s3173_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3173_plain_checked : check 391 s3173_plain_contract = true := by decide +kernel
def s3173_plain : CertifiedContract :=
  ⟨3173, 3174, 0, (.inc 2), s3173_plain_contract, 391, s3173_plain_checked⟩

def s3174_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, true, true, true] 0 (.inc 2)⟩
theorem s3174_plain_checked : check 397 s3174_plain_contract = true := by decide +kernel
def s3174_plain : CertifiedContract :=
  ⟨3174, 3175, 0, (.inc 2), s3174_plain_contract, 397, s3174_plain_checked⟩

def s3175_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s3175_plain_checked : check 98 s3175_plain_contract = true := by decide +kernel
def s3175_plain : CertifiedContract :=
  ⟨3175, 3170, 0, .none, s3175_plain_contract, 98, s3175_plain_checked⟩

def s3176_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s3176_zero_checked : check 354 s3176_zero_contract = true := by decide +kernel
def s3176_zero : CertifiedContract :=
  ⟨3176, 3179, 0, .none, s3176_zero_contract, 354, s3176_zero_checked⟩

def s3176_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s3176_positive_checked : check 360 s3176_positive_contract = true := by decide +kernel
def s3176_positive : CertifiedContract :=
  ⟨3176, 3177, 1, (.dec 2), s3176_positive_contract, 360, s3176_positive_checked⟩

def s3177_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s3177_plain_checked : check 373 s3177_plain_contract = true := by decide +kernel
def s3177_plain : CertifiedContract :=
  ⟨3177, 3178, 0, (.inc 8), s3177_plain_contract, 373, s3177_plain_checked⟩

def s3178_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, false, false] 0 .none⟩
theorem s3178_plain_checked : check 98 s3178_plain_contract = true := by decide +kernel
def s3178_plain : CertifiedContract :=
  ⟨3178, 3176, 0, .none, s3178_plain_contract, 98, s3178_plain_checked⟩

def s3179_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s3179_zero_checked : check 375 s3179_zero_contract = true := by decide +kernel
def s3179_zero : CertifiedContract :=
  ⟨3179, 3182, 0, .none, s3179_zero_contract, 375, s3179_zero_checked⟩

def s3179_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s3179_positive_checked : check 381 s3179_positive_contract = true := by decide +kernel
def s3179_positive : CertifiedContract :=
  ⟨3179, 3180, 1, (.dec 0), s3179_positive_contract, 381, s3179_positive_checked⟩

def s3180_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s3180_plain_checked : check 373 s3180_plain_contract = true := by decide +kernel
def s3180_plain : CertifiedContract :=
  ⟨3180, 3181, 0, (.inc 2), s3180_plain_contract, 373, s3180_plain_checked⟩

def s3181_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s3181_plain_checked : check 101 s3181_plain_contract = true := by decide +kernel
def s3181_plain : CertifiedContract :=
  ⟨3181, 3179, 0, .none, s3181_plain_contract, 101, s3181_plain_checked⟩

def s3182_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3182_zero_checked : check 381 s3182_zero_contract = true := by decide +kernel
def s3182_zero : CertifiedContract :=
  ⟨3182, 3186, 0, .none, s3182_zero_contract, 381, s3182_zero_checked⟩

def s3182_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3182_positive_checked : check 387 s3182_positive_contract = true := by decide +kernel
def s3182_positive : CertifiedContract :=
  ⟨3182, 3183, 1, (.dec 2), s3182_positive_contract, 387, s3182_positive_checked⟩

def s3183_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3183_plain_checked : check 400 s3183_plain_contract = true := by decide +kernel
def s3183_plain : CertifiedContract :=
  ⟨3183, 3184, 0, (.inc 5), s3183_plain_contract, 400, s3183_plain_checked⟩

def s3184_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3184_plain_checked : check 427 s3184_plain_contract = true := by decide +kernel
def s3184_plain : CertifiedContract :=
  ⟨3184, 3185, 0, (.inc 8), s3184_plain_contract, 427, s3184_plain_checked⟩

def s3185_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s3185_plain_checked : check 116 s3185_plain_contract = true := by decide +kernel
def s3185_plain : CertifiedContract :=
  ⟨3185, 3182, 0, .none, s3185_plain_contract, 116, s3185_plain_checked⟩

def s3186_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, true, false] 0 .none⟩
theorem s3186_zero_checked : check 402 s3186_zero_contract = true := by decide +kernel
def s3186_zero : CertifiedContract :=
  ⟨3186, 3192, 0, .none, s3186_zero_contract, 402, s3186_zero_checked⟩

def s3186_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3186_positive_checked : check 405 s3186_positive_contract = true := by decide +kernel
def s3186_positive : CertifiedContract :=
  ⟨3186, 3187, 1, (.dec 8), s3186_positive_contract, 405, s3186_positive_checked⟩

def s3187_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3187_plain_checked : check 400 s3187_plain_contract = true := by decide +kernel
def s3187_plain : CertifiedContract :=
  ⟨3187, 3188, 0, (.inc 5), s3187_plain_contract, 400, s3187_plain_checked⟩

def s3188_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s3188_zero_checked : check 420 s3188_zero_contract = true := by decide +kernel
def s3188_zero : CertifiedContract :=
  ⟨3188, 3191, 0, .none, s3188_zero_contract, 420, s3188_zero_checked⟩

def s3188_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3188_positive_checked : check 423 s3188_positive_contract = true := by decide +kernel
def s3188_positive : CertifiedContract :=
  ⟨3188, 3189, 1, (.dec 8), s3188_positive_contract, 423, s3188_positive_checked⟩

def s3189_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3189_plain_checked : check 418 s3189_plain_contract = true := by decide +kernel
def s3189_plain : CertifiedContract :=
  ⟨3189, 3190, 0, (.inc 2), s3189_plain_contract, 418, s3189_plain_checked⟩

def s3190_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3190_plain_checked : check 116 s3190_plain_contract = true := by decide +kernel
def s3190_plain : CertifiedContract :=
  ⟨3190, 3188, 0, .none, s3190_plain_contract, 116, s3190_plain_checked⟩

def s3191_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s3191_plain_checked : check 119 s3191_plain_contract = true := by decide +kernel
def s3191_plain : CertifiedContract :=
  ⟨3191, 3182, 0, .none, s3191_plain_contract, 119, s3191_plain_checked⟩

def s3192_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s3192_zero_checked : check 390 s3192_zero_contract = true := by decide +kernel
def s3192_zero : CertifiedContract :=
  ⟨3192, 3195, 0, .none, s3192_zero_contract, 390, s3192_zero_checked⟩

def s3192_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s3192_positive_checked : check 387 s3192_positive_contract = true := by decide +kernel
def s3192_positive : CertifiedContract :=
  ⟨3192, 3193, 1, (.dec 5), s3192_positive_contract, 387, s3192_positive_checked⟩

def s3193_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s3193_plain_checked : check 400 s3193_plain_contract = true := by decide +kernel
def s3193_plain : CertifiedContract :=
  ⟨3193, 3194, 0, (.inc 0), s3193_plain_contract, 400, s3193_plain_checked⟩

def s3194_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, false, true, true, true, false] 0 .none⟩
theorem s3194_plain_checked : check 107 s3194_plain_contract = true := by decide +kernel
def s3194_plain : CertifiedContract :=
  ⟨3194, 3192, 0, .none, s3194_plain_contract, 107, s3194_plain_checked⟩

def s3195_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, true, false] 0 .none⟩
theorem s3195_zero_checked : check 354 s3195_zero_contract = true := by decide +kernel
def s3195_zero : CertifiedContract :=
  ⟨3195, 3199, 0, .none, s3195_zero_contract, 354, s3195_zero_checked⟩

def s3195_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, false, true, false] 1 (.dec 4)⟩
theorem s3195_positive_checked : check 360 s3195_positive_contract = true := by decide +kernel
def s3195_positive : CertifiedContract :=
  ⟨3195, 3196, 1, (.dec 4), s3195_positive_contract, 360, s3195_positive_checked⟩

def s3196_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s3196_plain_checked : check 373 s3196_plain_contract = true := by decide +kernel
def s3196_plain : CertifiedContract :=
  ⟨3196, 3197, 0, (.inc 2), s3196_plain_contract, 373, s3196_plain_checked⟩

def s3197_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3197_plain_checked : check 400 s3197_plain_contract = true := by decide +kernel
def s3197_plain : CertifiedContract :=
  ⟨3197, 3198, 0, (.inc 8), s3197_plain_contract, 400, s3197_plain_checked⟩

def s3198_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s3198_plain_checked : check 107 s3198_plain_contract = true := by decide +kernel
def s3198_plain : CertifiedContract :=
  ⟨3198, 3195, 0, .none, s3198_plain_contract, 107, s3198_plain_checked⟩

def s3199_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s3199_zero_checked : check 360 s3199_zero_contract = true := by decide +kernel
def s3199_zero : CertifiedContract :=
  ⟨3199, 3202, 0, .none, s3199_zero_contract, 360, s3199_zero_checked⟩

def s3199_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s3199_positive_checked : check 360 s3199_positive_contract = true := by decide +kernel
def s3199_positive : CertifiedContract :=
  ⟨3199, 3200, 1, (.dec 8), s3199_positive_contract, 360, s3199_positive_checked⟩

def s3200_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, true, true, true] 0 (.inc 4)⟩
theorem s3200_plain_checked : check 364 s3200_plain_contract = true := by decide +kernel
def s3200_plain : CertifiedContract :=
  ⟨3200, 3201, 0, (.inc 4), s3200_plain_contract, 364, s3200_plain_checked⟩

def s3201_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, false, true, true, false] 0 .none⟩
theorem s3201_plain_checked : check 98 s3201_plain_contract = true := by decide +kernel
def s3201_plain : CertifiedContract :=
  ⟨3201, 3199, 0, .none, s3201_plain_contract, 98, s3201_plain_checked⟩

def s3202_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s3202_zero_checked : check 354 s3202_zero_contract = true := by decide +kernel
def s3202_zero : CertifiedContract :=
  ⟨3202, 3205, 0, .none, s3202_zero_contract, 354, s3202_zero_checked⟩

def s3202_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3202_positive_checked : check 360 s3202_positive_contract = true := by decide +kernel
def s3202_positive : CertifiedContract :=
  ⟨3202, 3203, 1, (.dec 2), s3202_positive_contract, 360, s3202_positive_checked⟩

end PA211.UserCandidate.RuntimeShards.S064
