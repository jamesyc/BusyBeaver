import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S005
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s0242_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s0242_plain_checked : check 94 s0242_plain_contract = true := by decide +kernel
def s0242_plain : CertifiedContract :=
  ⟨242, 246, 0, .none, s0242_plain_contract, 94, s0242_plain_checked⟩

def s0243_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s0243_zero_checked : check 365 s0243_zero_contract = true := by decide +kernel
def s0243_zero : CertifiedContract :=
  ⟨243, 246, 0, .none, s0243_zero_contract, 365, s0243_zero_checked⟩

def s0243_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0243_positive_checked : check 368 s0243_positive_contract = true := by decide +kernel
def s0243_positive : CertifiedContract :=
  ⟨243, 244, 1, (.dec 5), s0243_positive_contract, 368, s0243_positive_checked⟩

def s0244_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0244_plain_checked : check 372 s0244_plain_contract = true := by decide +kernel
def s0244_plain : CertifiedContract :=
  ⟨244, 245, 0, (.inc 8), s0244_plain_contract, 372, s0244_plain_checked⟩

def s0245_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s0245_plain_checked : check 97 s0245_plain_contract = true := by decide +kernel
def s0245_plain : CertifiedContract :=
  ⟨245, 243, 0, .none, s0245_plain_contract, 97, s0245_plain_checked⟩

def s0246_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, false] 0 .none⟩
theorem s0246_plain_checked : check 88 s0246_plain_contract = true := by decide +kernel
def s0246_plain : CertifiedContract :=
  ⟨246, 239, 0, .none, s0246_plain_contract, 88, s0246_plain_checked⟩

def s0247_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s0247_zero_checked : check 311 s0247_zero_contract = true := by decide +kernel
def s0247_zero : CertifiedContract :=
  ⟨247, 250, 0, .none, s0247_zero_contract, 311, s0247_zero_checked⟩

def s0247_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0247_positive_checked : check 314 s0247_positive_contract = true := by decide +kernel
def s0247_positive : CertifiedContract :=
  ⟨247, 248, 1, (.dec 5), s0247_positive_contract, 314, s0247_positive_checked⟩

def s0248_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, true, true, true] 0 (.inc 0)⟩
theorem s0248_plain_checked : check 327 s0248_plain_contract = true := by decide +kernel
def s0248_plain : CertifiedContract :=
  ⟨248, 249, 0, (.inc 0), s0248_plain_contract, 327, s0248_plain_checked⟩

def s0249_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, false, true, false] 0 .none⟩
theorem s0249_plain_checked : check 82 s0249_plain_contract = true := by decide +kernel
def s0249_plain : CertifiedContract :=
  ⟨249, 247, 0, .none, s0249_plain_contract, 82, s0249_plain_checked⟩

def s0250_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, true, false] 0 .none⟩
theorem s0250_zero_checked : check 308 s0250_zero_contract = true := by decide +kernel
def s0250_zero : CertifiedContract :=
  ⟨250, 254, 0, .none, s0250_zero_contract, 308, s0250_zero_checked⟩

def s0250_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0250_positive_checked : check 314 s0250_positive_contract = true := by decide +kernel
def s0250_positive : CertifiedContract :=
  ⟨250, 251, 1, (.dec 2), s0250_positive_contract, 314, s0250_positive_checked⟩

def s0251_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0251_plain_checked : check 327 s0251_plain_contract = true := by decide +kernel
def s0251_plain : CertifiedContract :=
  ⟨251, 252, 0, (.inc 5), s0251_plain_contract, 327, s0251_plain_checked⟩

def s0252_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0252_plain_checked : check 354 s0252_plain_contract = true := by decide +kernel
def s0252_plain : CertifiedContract :=
  ⟨252, 253, 0, (.inc 8), s0252_plain_contract, 354, s0252_plain_checked⟩

def s0253_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s0253_plain_checked : check 91 s0253_plain_contract = true := by decide +kernel
def s0253_plain : CertifiedContract :=
  ⟨253, 250, 0, .none, s0253_plain_contract, 91, s0253_plain_checked⟩

def s0254_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, true, false] 0 .none⟩
theorem s0254_zero_checked : check 329 s0254_zero_contract = true := by decide +kernel
def s0254_zero : CertifiedContract :=
  ⟨254, 260, 0, .none, s0254_zero_contract, 329, s0254_zero_checked⟩

def s0254_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0254_positive_checked : check 332 s0254_positive_contract = true := by decide +kernel
def s0254_positive : CertifiedContract :=
  ⟨254, 255, 1, (.dec 8), s0254_positive_contract, 332, s0254_positive_checked⟩

def s0255_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0255_plain_checked : check 327 s0255_plain_contract = true := by decide +kernel
def s0255_plain : CertifiedContract :=
  ⟨255, 256, 0, (.inc 5), s0255_plain_contract, 327, s0255_plain_checked⟩

def s0256_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, true, true, true] 0 .none⟩
theorem s0256_zero_checked : check 347 s0256_zero_contract = true := by decide +kernel
def s0256_zero : CertifiedContract :=
  ⟨256, 259, 0, .none, s0256_zero_contract, 347, s0256_zero_checked⟩

def s0256_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0256_positive_checked : check 350 s0256_positive_contract = true := by decide +kernel
def s0256_positive : CertifiedContract :=
  ⟨256, 257, 1, (.dec 8), s0256_positive_contract, 350, s0256_positive_checked⟩

def s0257_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0257_plain_checked : check 345 s0257_plain_contract = true := by decide +kernel
def s0257_plain : CertifiedContract :=
  ⟨257, 258, 0, (.inc 2), s0257_plain_contract, 345, s0257_plain_checked⟩

def s0258_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0258_plain_checked : check 91 s0258_plain_contract = true := by decide +kernel
def s0258_plain : CertifiedContract :=
  ⟨258, 256, 0, .none, s0258_plain_contract, 91, s0258_plain_checked⟩

def s0259_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s0259_plain_checked : check 94 s0259_plain_contract = true := by decide +kernel
def s0259_plain : CertifiedContract :=
  ⟨259, 250, 0, .none, s0259_plain_contract, 94, s0259_plain_checked⟩

def s0260_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, false, false] 0 .none⟩
theorem s0260_zero_checked : check 323 s0260_zero_contract = true := by decide +kernel
def s0260_zero : CertifiedContract :=
  ⟨260, 266, 0, .none, s0260_zero_contract, 323, s0260_zero_checked⟩

def s0260_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0260_positive_checked : check 314 s0260_positive_contract = true := by decide +kernel
def s0260_positive : CertifiedContract :=
  ⟨260, 261, 1, (.dec 5), s0260_positive_contract, 314, s0260_positive_checked⟩

def s0261_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0261_plain_checked : check 327 s0261_plain_contract = true := by decide +kernel
def s0261_plain : CertifiedContract :=
  ⟨261, 262, 0, (.inc 2), s0261_plain_contract, 327, s0261_plain_checked⟩

def s0262_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0262_plain_checked : check 330 s0262_plain_contract = true := by decide +kernel
def s0262_plain : CertifiedContract :=
  ⟨262, 263, 0, (.inc 2), s0262_plain_contract, 330, s0262_plain_checked⟩

def s0263_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0263_plain_checked : check 327 s0263_plain_contract = true := by decide +kernel
def s0263_plain : CertifiedContract :=
  ⟨263, 264, 0, (.inc 2), s0263_plain_contract, 327, s0263_plain_checked⟩

def s0264_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, true, true, true] 0 (.inc 2)⟩
theorem s0264_plain_checked : check 333 s0264_plain_contract = true := by decide +kernel
def s0264_plain : CertifiedContract :=
  ⟨264, 265, 0, (.inc 2), s0264_plain_contract, 333, s0264_plain_checked⟩

def s0265_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, false, true, true, true, true, true, false] 0 .none⟩
theorem s0265_plain_checked : check 79 s0265_plain_contract = true := by decide +kernel
def s0265_plain : CertifiedContract :=
  ⟨265, 260, 0, .none, s0265_plain_contract, 79, s0265_plain_checked⟩

def s0266_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s0266_zero_checked : check 290 s0266_zero_contract = true := by decide +kernel
def s0266_zero : CertifiedContract :=
  ⟨266, 269, 0, .none, s0266_zero_contract, 290, s0266_zero_checked⟩

def s0266_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s0266_positive_checked : check 296 s0266_positive_contract = true := by decide +kernel
def s0266_positive : CertifiedContract :=
  ⟨266, 267, 1, (.dec 2), s0266_positive_contract, 296, s0266_positive_checked⟩

def s0267_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s0267_plain_checked : check 309 s0267_plain_contract = true := by decide +kernel
def s0267_plain : CertifiedContract :=
  ⟨267, 268, 0, (.inc 8), s0267_plain_contract, 309, s0267_plain_checked⟩

def s0268_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, false, false] 0 .none⟩
theorem s0268_plain_checked : check 76 s0268_plain_contract = true := by decide +kernel
def s0268_plain : CertifiedContract :=
  ⟨268, 266, 0, .none, s0268_plain_contract, 76, s0268_plain_checked⟩

def s0269_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0269_zero_checked : check 311 s0269_zero_contract = true := by decide +kernel
def s0269_zero : CertifiedContract :=
  ⟨269, 272, 0, .none, s0269_zero_contract, 311, s0269_zero_checked⟩

def s0269_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0269_positive_checked : check 317 s0269_positive_contract = true := by decide +kernel
def s0269_positive : CertifiedContract :=
  ⟨269, 270, 1, (.dec 0), s0269_positive_contract, 317, s0269_positive_checked⟩

def s0270_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0270_plain_checked : check 309 s0270_plain_contract = true := by decide +kernel
def s0270_plain : CertifiedContract :=
  ⟨270, 271, 0, (.inc 2), s0270_plain_contract, 309, s0270_plain_checked⟩

def s0271_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s0271_plain_checked : check 79 s0271_plain_contract = true := by decide +kernel
def s0271_plain : CertifiedContract :=
  ⟨271, 269, 0, .none, s0271_plain_contract, 79, s0271_plain_checked⟩

def s0272_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0272_zero_checked : check 317 s0272_zero_contract = true := by decide +kernel
def s0272_zero : CertifiedContract :=
  ⟨272, 276, 0, .none, s0272_zero_contract, 317, s0272_zero_checked⟩

def s0272_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0272_positive_checked : check 323 s0272_positive_contract = true := by decide +kernel
def s0272_positive : CertifiedContract :=
  ⟨272, 273, 1, (.dec 2), s0272_positive_contract, 323, s0272_positive_checked⟩

def s0273_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0273_plain_checked : check 336 s0273_plain_contract = true := by decide +kernel
def s0273_plain : CertifiedContract :=
  ⟨273, 274, 0, (.inc 5), s0273_plain_contract, 336, s0273_plain_checked⟩

def s0274_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0274_plain_checked : check 363 s0274_plain_contract = true := by decide +kernel
def s0274_plain : CertifiedContract :=
  ⟨274, 275, 0, (.inc 8), s0274_plain_contract, 363, s0274_plain_checked⟩

def s0275_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0275_plain_checked : check 94 s0275_plain_contract = true := by decide +kernel
def s0275_plain : CertifiedContract :=
  ⟨275, 272, 0, .none, s0275_plain_contract, 94, s0275_plain_checked⟩

def s0276_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, true, false] 0 .none⟩
theorem s0276_zero_checked : check 338 s0276_zero_contract = true := by decide +kernel
def s0276_zero : CertifiedContract :=
  ⟨276, 282, 0, .none, s0276_zero_contract, 338, s0276_zero_checked⟩

def s0276_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0276_positive_checked : check 341 s0276_positive_contract = true := by decide +kernel
def s0276_positive : CertifiedContract :=
  ⟨276, 277, 1, (.dec 8), s0276_positive_contract, 341, s0276_positive_checked⟩

def s0277_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0277_plain_checked : check 336 s0277_plain_contract = true := by decide +kernel
def s0277_plain : CertifiedContract :=
  ⟨277, 278, 0, (.inc 5), s0277_plain_contract, 336, s0277_plain_checked⟩

def s0278_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s0278_zero_checked : check 356 s0278_zero_contract = true := by decide +kernel
def s0278_zero : CertifiedContract :=
  ⟨278, 281, 0, .none, s0278_zero_contract, 356, s0278_zero_checked⟩

def s0278_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0278_positive_checked : check 359 s0278_positive_contract = true := by decide +kernel
def s0278_positive : CertifiedContract :=
  ⟨278, 279, 1, (.dec 8), s0278_positive_contract, 359, s0278_positive_checked⟩

def s0279_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0279_plain_checked : check 354 s0279_plain_contract = true := by decide +kernel
def s0279_plain : CertifiedContract :=
  ⟨279, 280, 0, (.inc 2), s0279_plain_contract, 354, s0279_plain_checked⟩

def s0280_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0280_plain_checked : check 94 s0280_plain_contract = true := by decide +kernel
def s0280_plain : CertifiedContract :=
  ⟨280, 278, 0, .none, s0280_plain_contract, 94, s0280_plain_checked⟩

def s0281_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0281_plain_checked : check 97 s0281_plain_contract = true := by decide +kernel
def s0281_plain : CertifiedContract :=
  ⟨281, 272, 0, .none, s0281_plain_contract, 97, s0281_plain_checked⟩

def s0282_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, true, false, false] 0 .none⟩
theorem s0282_zero_checked : check 326 s0282_zero_contract = true := by decide +kernel
def s0282_zero : CertifiedContract :=
  ⟨282, 285, 0, .none, s0282_zero_contract, 326, s0282_zero_checked⟩

def s0282_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0282_positive_checked : check 323 s0282_positive_contract = true := by decide +kernel
def s0282_positive : CertifiedContract :=
  ⟨282, 283, 1, (.dec 5), s0282_positive_contract, 323, s0282_positive_checked⟩

def s0283_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0283_plain_checked : check 336 s0283_plain_contract = true := by decide +kernel
def s0283_plain : CertifiedContract :=
  ⟨283, 284, 0, (.inc 0), s0283_plain_contract, 336, s0283_plain_checked⟩

def s0284_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, true, false] 0 .none⟩
theorem s0284_plain_checked : check 85 s0284_plain_contract = true := by decide +kernel
def s0284_plain : CertifiedContract :=
  ⟨284, 282, 0, .none, s0284_plain_contract, 85, s0284_plain_checked⟩

def s0285_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, true, true, false] 0 .none⟩
theorem s0285_zero_checked : check 290 s0285_zero_contract = true := by decide +kernel
def s0285_zero : CertifiedContract :=
  ⟨285, 289, 0, .none, s0285_zero_contract, 290, s0285_zero_checked⟩

def s0285_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, true, false, true, false] 1 (.dec 3)⟩
theorem s0285_positive_checked : check 296 s0285_positive_contract = true := by decide +kernel
def s0285_positive : CertifiedContract :=
  ⟨285, 286, 1, (.dec 3), s0285_positive_contract, 296, s0285_positive_checked⟩

def s0286_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0286_plain_checked : check 309 s0286_plain_contract = true := by decide +kernel
def s0286_plain : CertifiedContract :=
  ⟨286, 287, 0, (.inc 2), s0286_plain_contract, 309, s0286_plain_checked⟩

def s0287_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0287_plain_checked : check 336 s0287_plain_contract = true := by decide +kernel
def s0287_plain : CertifiedContract :=
  ⟨287, 288, 0, (.inc 8), s0287_plain_contract, 336, s0287_plain_checked⟩

def s0288_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, true, false, false] 0 .none⟩
theorem s0288_plain_checked : check 85 s0288_plain_contract = true := by decide +kernel
def s0288_plain : CertifiedContract :=
  ⟨288, 285, 0, .none, s0288_plain_contract, 85, s0288_plain_checked⟩

def s0289_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s0289_zero_checked : check 296 s0289_zero_contract = true := by decide +kernel
def s0289_zero : CertifiedContract :=
  ⟨289, 292, 0, .none, s0289_zero_contract, 296, s0289_zero_checked⟩

def s0289_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s0289_positive_checked : check 296 s0289_positive_contract = true := by decide +kernel
def s0289_positive : CertifiedContract :=
  ⟨289, 290, 1, (.dec 8), s0289_positive_contract, 296, s0289_positive_checked⟩

def s0290_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, true, true, true, true] 0 (.inc 3)⟩
theorem s0290_plain_checked : check 312 s0290_plain_contract = true := by decide +kernel
def s0290_plain : CertifiedContract :=
  ⟨290, 291, 0, (.inc 3), s0290_plain_contract, 312, s0290_plain_checked⟩

def s0291_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, false, true, true, false] 0 .none⟩
theorem s0291_plain_checked : check 76 s0291_plain_contract = true := by decide +kernel
def s0291_plain : CertifiedContract :=
  ⟨291, 289, 0, .none, s0291_plain_contract, 76, s0291_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s0242_plain,
  s0243_zero,
  s0243_positive,
  s0244_plain,
  s0245_plain,
  s0246_plain,
  s0247_zero,
  s0247_positive,
  s0248_plain,
  s0249_plain,
  s0250_zero,
  s0250_positive,
  s0251_plain,
  s0252_plain,
  s0253_plain,
  s0254_zero,
  s0254_positive,
  s0255_plain,
  s0256_zero,
  s0256_positive,
  s0257_plain,
  s0258_plain,
  s0259_plain,
  s0260_zero,
  s0260_positive,
  s0261_plain,
  s0262_plain,
  s0263_plain,
  s0264_plain,
  s0265_plain,
  s0266_zero,
  s0266_positive,
  s0267_plain,
  s0268_plain,
  s0269_zero,
  s0269_positive,
  s0270_plain,
  s0271_plain,
  s0272_zero,
  s0272_positive,
  s0273_plain,
  s0274_plain,
  s0275_plain,
  s0276_zero,
  s0276_positive,
  s0277_plain,
  s0278_zero,
  s0278_positive,
  s0279_plain,
  s0280_plain,
  s0281_plain,
  s0282_zero,
  s0282_positive,
  s0283_plain,
  s0284_plain,
  s0285_zero,
  s0285_positive,
  s0286_plain,
  s0287_plain,
  s0288_plain,
  s0289_zero,
  s0289_positive,
  s0290_plain,
  s0291_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S005
