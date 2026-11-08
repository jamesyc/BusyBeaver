import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S066
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s3252_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s3252_plain_checked : check 381 s3252_plain_contract = true := by decide +kernel
def s3252_plain : CertifiedContract :=
  ⟨3252, 3253, 0, (.inc 2), s3252_plain_contract, 381, s3252_plain_checked⟩

def s3253_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s3253_plain_checked : check 387 s3253_plain_contract = true := by decide +kernel
def s3253_plain : CertifiedContract :=
  ⟨3253, 3254, 0, (.inc 2), s3253_plain_contract, 387, s3253_plain_checked⟩

def s3254_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, false] 0 .none⟩
theorem s3254_plain_checked : check 97 s3254_plain_contract = true := by decide +kernel
def s3254_plain : CertifiedContract :=
  ⟨3254, 3249, 0, .none, s3254_plain_contract, 97, s3254_plain_checked⟩

def s3255_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, false, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, false, false] 0 (.inc 2)⟩
theorem s3255_plain_checked : check 354 s3255_plain_contract = true := by decide +kernel
def s3255_plain : CertifiedContract :=
  ⟨3255, 3256, 0, (.inc 2), s3255_plain_contract, 354, s3255_plain_checked⟩

def s3256_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s3256_zero_checked : check 326 s3256_zero_contract = true := by decide +kernel
def s3256_zero : CertifiedContract :=
  ⟨3256, 3259, 0, .none, s3256_zero_contract, 326, s3256_zero_checked⟩

def s3256_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s3256_positive_checked : check 332 s3256_positive_contract = true := by decide +kernel
def s3256_positive : CertifiedContract :=
  ⟨3256, 3257, 1, (.dec 2), s3256_positive_contract, 332, s3256_positive_checked⟩

def s3257_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s3257_plain_checked : check 345 s3257_plain_contract = true := by decide +kernel
def s3257_plain : CertifiedContract :=
  ⟨3257, 3258, 0, (.inc 8), s3257_plain_contract, 345, s3257_plain_checked⟩

def s3258_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s3258_plain_checked : check 88 s3258_plain_contract = true := by decide +kernel
def s3258_plain : CertifiedContract :=
  ⟨3258, 3256, 0, .none, s3258_plain_contract, 88, s3258_plain_checked⟩

def s3259_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s3259_zero_checked : check 347 s3259_zero_contract = true := by decide +kernel
def s3259_zero : CertifiedContract :=
  ⟨3259, 3262, 0, .none, s3259_zero_contract, 347, s3259_zero_checked⟩

def s3259_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s3259_positive_checked : check 353 s3259_positive_contract = true := by decide +kernel
def s3259_positive : CertifiedContract :=
  ⟨3259, 3260, 1, (.dec 0), s3259_positive_contract, 353, s3259_positive_checked⟩

def s3260_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s3260_plain_checked : check 345 s3260_plain_contract = true := by decide +kernel
def s3260_plain : CertifiedContract :=
  ⟨3260, 3261, 0, (.inc 2), s3260_plain_contract, 345, s3260_plain_checked⟩

def s3261_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s3261_plain_checked : check 91 s3261_plain_contract = true := by decide +kernel
def s3261_plain : CertifiedContract :=
  ⟨3261, 3259, 0, .none, s3261_plain_contract, 91, s3261_plain_checked⟩

def s3262_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3262_zero_checked : check 353 s3262_zero_contract = true := by decide +kernel
def s3262_zero : CertifiedContract :=
  ⟨3262, 3266, 0, .none, s3262_zero_contract, 353, s3262_zero_checked⟩

def s3262_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3262_positive_checked : check 359 s3262_positive_contract = true := by decide +kernel
def s3262_positive : CertifiedContract :=
  ⟨3262, 3263, 1, (.dec 2), s3262_positive_contract, 359, s3262_positive_checked⟩

def s3263_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3263_plain_checked : check 372 s3263_plain_contract = true := by decide +kernel
def s3263_plain : CertifiedContract :=
  ⟨3263, 3264, 0, (.inc 5), s3263_plain_contract, 372, s3263_plain_checked⟩

def s3264_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3264_plain_checked : check 399 s3264_plain_contract = true := by decide +kernel
def s3264_plain : CertifiedContract :=
  ⟨3264, 3265, 0, (.inc 8), s3264_plain_contract, 399, s3264_plain_checked⟩

def s3265_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s3265_plain_checked : check 106 s3265_plain_contract = true := by decide +kernel
def s3265_plain : CertifiedContract :=
  ⟨3265, 3262, 0, .none, s3265_plain_contract, 106, s3265_plain_checked⟩

def s3266_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s3266_zero_checked : check 374 s3266_zero_contract = true := by decide +kernel
def s3266_zero : CertifiedContract :=
  ⟨3266, 3272, 0, .none, s3266_zero_contract, 374, s3266_zero_checked⟩

def s3266_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3266_positive_checked : check 377 s3266_positive_contract = true := by decide +kernel
def s3266_positive : CertifiedContract :=
  ⟨3266, 3267, 1, (.dec 8), s3266_positive_contract, 377, s3266_positive_checked⟩

def s3267_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3267_plain_checked : check 372 s3267_plain_contract = true := by decide +kernel
def s3267_plain : CertifiedContract :=
  ⟨3267, 3268, 0, (.inc 5), s3267_plain_contract, 372, s3267_plain_checked⟩

def s3268_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s3268_zero_checked : check 392 s3268_zero_contract = true := by decide +kernel
def s3268_zero : CertifiedContract :=
  ⟨3268, 3271, 0, .none, s3268_zero_contract, 392, s3268_zero_checked⟩

def s3268_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3268_positive_checked : check 395 s3268_positive_contract = true := by decide +kernel
def s3268_positive : CertifiedContract :=
  ⟨3268, 3269, 1, (.dec 8), s3268_positive_contract, 395, s3268_positive_checked⟩

def s3269_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3269_plain_checked : check 390 s3269_plain_contract = true := by decide +kernel
def s3269_plain : CertifiedContract :=
  ⟨3269, 3270, 0, (.inc 2), s3269_plain_contract, 390, s3269_plain_checked⟩

def s3270_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s3270_plain_checked : check 106 s3270_plain_contract = true := by decide +kernel
def s3270_plain : CertifiedContract :=
  ⟨3270, 3268, 0, .none, s3270_plain_contract, 106, s3270_plain_checked⟩

def s3271_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s3271_plain_checked : check 109 s3271_plain_contract = true := by decide +kernel
def s3271_plain : CertifiedContract :=
  ⟨3271, 3262, 0, .none, s3271_plain_contract, 109, s3271_plain_checked⟩

def s3272_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s3272_zero_checked : check 362 s3272_zero_contract = true := by decide +kernel
def s3272_zero : CertifiedContract :=
  ⟨3272, 3275, 0, .none, s3272_zero_contract, 362, s3272_zero_checked⟩

def s3272_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s3272_positive_checked : check 359 s3272_positive_contract = true := by decide +kernel
def s3272_positive : CertifiedContract :=
  ⟨3272, 3273, 1, (.dec 5), s3272_positive_contract, 359, s3272_positive_checked⟩

def s3273_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s3273_plain_checked : check 372 s3273_plain_contract = true := by decide +kernel
def s3273_plain : CertifiedContract :=
  ⟨3273, 3274, 0, (.inc 0), s3273_plain_contract, 372, s3273_plain_checked⟩

def s3274_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s3274_plain_checked : check 97 s3274_plain_contract = true := by decide +kernel
def s3274_plain : CertifiedContract :=
  ⟨3274, 3272, 0, .none, s3274_plain_contract, 97, s3274_plain_checked⟩

def s3275_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s3275_zero_checked : check 326 s3275_zero_contract = true := by decide +kernel
def s3275_zero : CertifiedContract :=
  ⟨3275, 3279, 0, .none, s3275_zero_contract, 326, s3275_zero_checked⟩

def s3275_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, false, true, false] 1 (.dec 4)⟩
theorem s3275_positive_checked : check 332 s3275_positive_contract = true := by decide +kernel
def s3275_positive : CertifiedContract :=
  ⟨3275, 3276, 1, (.dec 4), s3275_positive_contract, 332, s3275_positive_checked⟩

def s3276_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s3276_plain_checked : check 345 s3276_plain_contract = true := by decide +kernel
def s3276_plain : CertifiedContract :=
  ⟨3276, 3277, 0, (.inc 2), s3276_plain_contract, 345, s3276_plain_checked⟩

def s3277_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3277_plain_checked : check 372 s3277_plain_contract = true := by decide +kernel
def s3277_plain : CertifiedContract :=
  ⟨3277, 3278, 0, (.inc 8), s3277_plain_contract, 372, s3277_plain_checked⟩

def s3278_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s3278_plain_checked : check 97 s3278_plain_contract = true := by decide +kernel
def s3278_plain : CertifiedContract :=
  ⟨3278, 3275, 0, .none, s3278_plain_contract, 97, s3278_plain_checked⟩

def s3279_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, false] 0 .none⟩
theorem s3279_zero_checked : check 332 s3279_zero_contract = true := by decide +kernel
def s3279_zero : CertifiedContract :=
  ⟨3279, 3282, 0, .none, s3279_zero_contract, 332, s3279_zero_checked⟩

def s3279_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s3279_positive_checked : check 332 s3279_positive_contract = true := by decide +kernel
def s3279_positive : CertifiedContract :=
  ⟨3279, 3280, 1, (.dec 8), s3279_positive_contract, 332, s3279_positive_checked⟩

def s3280_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, true, true, true] 0 (.inc 4)⟩
theorem s3280_plain_checked : check 336 s3280_plain_contract = true := by decide +kernel
def s3280_plain : CertifiedContract :=
  ⟨3280, 3281, 0, (.inc 4), s3280_plain_contract, 336, s3280_plain_checked⟩

def s3281_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s3281_plain_checked : check 88 s3281_plain_contract = true := by decide +kernel
def s3281_plain : CertifiedContract :=
  ⟨3281, 3279, 0, .none, s3281_plain_contract, 88, s3281_plain_checked⟩

def s3282_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, true, false] 0 .none⟩
theorem s3282_zero_checked : check 356 s3282_zero_contract = true := by decide +kernel
def s3282_zero : CertifiedContract :=
  ⟨3282, 3290, 0, .none, s3282_zero_contract, 356, s3282_zero_checked⟩

def s3282_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s3282_positive_checked : check 362 s3282_positive_contract = true := by decide +kernel
def s3282_positive : CertifiedContract :=
  ⟨3282, 3283, 1, (.dec 0), s3282_positive_contract, 362, s3282_positive_checked⟩

def s3283_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s3283_plain_checked : check 372 s3283_plain_contract = true := by decide +kernel
def s3283_plain : CertifiedContract :=
  ⟨3283, 3284, 0, (.inc 5), s3283_plain_contract, 372, s3283_plain_checked⟩

def s3284_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3284_zero_checked : check 398 s3284_zero_contract = true := by decide +kernel
def s3284_zero : CertifiedContract :=
  ⟨3284, 3286, 0, .none, s3284_zero_contract, 398, s3284_zero_checked⟩

def s3284_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s3284_positive_checked : check 404 s3284_positive_contract = true := by decide +kernel
def s3284_positive : CertifiedContract :=
  ⟨3284, 3285, 1, (.dec 8), s3284_positive_contract, 404, s3284_positive_checked⟩

def s3285_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s3285_plain_checked : check 109 s3285_plain_contract = true := by decide +kernel
def s3285_plain : CertifiedContract :=
  ⟨3285, 3289, 0, .none, s3285_plain_contract, 109, s3285_plain_checked⟩

def s3286_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s3286_zero_checked : check 410 s3286_zero_contract = true := by decide +kernel
def s3286_zero : CertifiedContract :=
  ⟨3286, 3289, 0, .none, s3286_zero_contract, 410, s3286_zero_checked⟩

def s3286_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s3286_positive_checked : check 413 s3286_positive_contract = true := by decide +kernel
def s3286_positive : CertifiedContract :=
  ⟨3286, 3287, 1, (.dec 5), s3286_positive_contract, 413, s3286_positive_checked⟩

def s3287_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s3287_plain_checked : check 417 s3287_plain_contract = true := by decide +kernel
def s3287_plain : CertifiedContract :=
  ⟨3287, 3288, 0, (.inc 8), s3287_plain_contract, 417, s3287_plain_checked⟩

def s3288_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s3288_plain_checked : check 112 s3288_plain_contract = true := by decide +kernel
def s3288_plain : CertifiedContract :=
  ⟨3288, 3286, 0, .none, s3288_plain_contract, 112, s3288_plain_checked⟩

def s3289_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, false] 0 .none⟩
theorem s3289_plain_checked : check 103 s3289_plain_contract = true := by decide +kernel
def s3289_plain : CertifiedContract :=
  ⟨3289, 3282, 0, .none, s3289_plain_contract, 103, s3289_plain_checked⟩

def s3290_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s3290_zero_checked : check 356 s3290_zero_contract = true := by decide +kernel
def s3290_zero : CertifiedContract :=
  ⟨3290, 3293, 0, .none, s3290_zero_contract, 356, s3290_zero_checked⟩

def s3290_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s3290_positive_checked : check 359 s3290_positive_contract = true := by decide +kernel
def s3290_positive : CertifiedContract :=
  ⟨3290, 3291, 1, (.dec 5), s3290_positive_contract, 359, s3290_positive_checked⟩

def s3291_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s3291_plain_checked : check 372 s3291_plain_contract = true := by decide +kernel
def s3291_plain : CertifiedContract :=
  ⟨3291, 3292, 0, (.inc 0), s3291_plain_contract, 372, s3291_plain_checked⟩

def s3292_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, true, false] 0 .none⟩
theorem s3292_plain_checked : check 97 s3292_plain_contract = true := by decide +kernel
def s3292_plain : CertifiedContract :=
  ⟨3292, 3290, 0, .none, s3292_plain_contract, 97, s3292_plain_checked⟩

def s3293_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, true, false] 0 .none⟩
theorem s3293_zero_checked : check 353 s3293_zero_contract = true := by decide +kernel
def s3293_zero : CertifiedContract :=
  ⟨3293, 3297, 0, .none, s3293_zero_contract, 353, s3293_zero_checked⟩

def s3293_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s3293_positive_checked : check 359 s3293_positive_contract = true := by decide +kernel
def s3293_positive : CertifiedContract :=
  ⟨3293, 3294, 1, (.dec 2), s3293_positive_contract, 359, s3293_positive_checked⟩

def s3294_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s3294_plain_checked : check 372 s3294_plain_contract = true := by decide +kernel
def s3294_plain : CertifiedContract :=
  ⟨3294, 3295, 0, (.inc 5), s3294_plain_contract, 372, s3294_plain_checked⟩

def s3295_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s3295_plain_checked : check 399 s3295_plain_contract = true := by decide +kernel
def s3295_plain : CertifiedContract :=
  ⟨3295, 3296, 0, (.inc 8), s3295_plain_contract, 399, s3295_plain_checked⟩

def s3296_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s3296_plain_checked : check 106 s3296_plain_contract = true := by decide +kernel
def s3296_plain : CertifiedContract :=
  ⟨3296, 3293, 0, .none, s3296_plain_contract, 106, s3296_plain_checked⟩

def s3297_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, true, false] 0 .none⟩
theorem s3297_zero_checked : check 374 s3297_zero_contract = true := by decide +kernel
def s3297_zero : CertifiedContract :=
  ⟨3297, 3303, 0, .none, s3297_zero_contract, 374, s3297_zero_checked⟩

def s3297_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s3297_positive_checked : check 377 s3297_positive_contract = true := by decide +kernel
def s3297_positive : CertifiedContract :=
  ⟨3297, 3298, 1, (.dec 8), s3297_positive_contract, 377, s3297_positive_checked⟩

def s3298_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s3298_plain_checked : check 372 s3298_plain_contract = true := by decide +kernel
def s3298_plain : CertifiedContract :=
  ⟨3298, 3299, 0, (.inc 5), s3298_plain_contract, 372, s3298_plain_checked⟩

def s3299_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, true, true, true] 0 .none⟩
theorem s3299_zero_checked : check 392 s3299_zero_contract = true := by decide +kernel
def s3299_zero : CertifiedContract :=
  ⟨3299, 3302, 0, .none, s3299_zero_contract, 392, s3299_zero_checked⟩

def s3299_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s3299_positive_checked : check 395 s3299_positive_contract = true := by decide +kernel
def s3299_positive : CertifiedContract :=
  ⟨3299, 3300, 1, (.dec 8), s3299_positive_contract, 395, s3299_positive_checked⟩

def s3300_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s3300_plain_checked : check 390 s3300_plain_contract = true := by decide +kernel
def s3300_plain : CertifiedContract :=
  ⟨3300, 3301, 0, (.inc 2), s3300_plain_contract, 390, s3300_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s3252_plain,
  s3253_plain,
  s3254_plain,
  s3255_plain,
  s3256_zero,
  s3256_positive,
  s3257_plain,
  s3258_plain,
  s3259_zero,
  s3259_positive,
  s3260_plain,
  s3261_plain,
  s3262_zero,
  s3262_positive,
  s3263_plain,
  s3264_plain,
  s3265_plain,
  s3266_zero,
  s3266_positive,
  s3267_plain,
  s3268_zero,
  s3268_positive,
  s3269_plain,
  s3270_plain,
  s3271_plain,
  s3272_zero,
  s3272_positive,
  s3273_plain,
  s3274_plain,
  s3275_zero,
  s3275_positive,
  s3276_plain,
  s3277_plain,
  s3278_plain,
  s3279_zero,
  s3279_positive,
  s3280_plain,
  s3281_plain,
  s3282_zero,
  s3282_positive,
  s3283_plain,
  s3284_zero,
  s3284_positive,
  s3285_plain,
  s3286_zero,
  s3286_positive,
  s3287_plain,
  s3288_plain,
  s3289_plain,
  s3290_zero,
  s3290_positive,
  s3291_plain,
  s3292_plain,
  s3293_zero,
  s3293_positive,
  s3294_plain,
  s3295_plain,
  s3296_plain,
  s3297_zero,
  s3297_positive,
  s3298_plain,
  s3299_zero,
  s3299_positive,
  s3300_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S066
