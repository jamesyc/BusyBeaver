import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S008
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s0390_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, true, false] 0 .none⟩
theorem s0390_zero_checked : check 309 s0390_zero_contract = true := by decide +kernel
def s0390_zero : CertifiedContract :=
  ⟨390, 394, 0, .none, s0390_zero_contract, 309, s0390_zero_checked⟩

def s0390_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, false, true, false] 1 (.dec 4)⟩
theorem s0390_positive_checked : check 315 s0390_positive_contract = true := by decide +kernel
def s0390_positive : CertifiedContract :=
  ⟨390, 391, 1, (.dec 4), s0390_positive_contract, 315, s0390_positive_checked⟩

def s0391_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0391_plain_checked : check 328 s0391_plain_contract = true := by decide +kernel
def s0391_plain : CertifiedContract :=
  ⟨391, 392, 0, (.inc 2), s0391_plain_contract, 328, s0391_plain_checked⟩

def s0392_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0392_plain_checked : check 355 s0392_plain_contract = true := by decide +kernel
def s0392_plain : CertifiedContract :=
  ⟨392, 393, 0, (.inc 8), s0392_plain_contract, 355, s0392_plain_checked⟩

def s0393_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, false, false] 0 .none⟩
theorem s0393_plain_checked : check 92 s0393_plain_contract = true := by decide +kernel
def s0393_plain : CertifiedContract :=
  ⟨393, 390, 0, .none, s0393_plain_contract, 92, s0393_plain_checked⟩

def s0394_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, false] 0 .none⟩
theorem s0394_zero_checked : check 321 s0394_zero_contract = true := by decide +kernel
def s0394_zero : CertifiedContract :=
  ⟨394, 397, 0, .none, s0394_zero_contract, 321, s0394_zero_checked⟩

def s0394_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, true, true, false] 1 (.dec 8)⟩
theorem s0394_positive_checked : check 315 s0394_positive_contract = true := by decide +kernel
def s0394_positive : CertifiedContract :=
  ⟨394, 395, 1, (.dec 8), s0394_positive_contract, 315, s0394_positive_checked⟩

def s0395_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, true, true, true] 0 (.inc 4)⟩
theorem s0395_plain_checked : check 319 s0395_plain_contract = true := by decide +kernel
def s0395_plain : CertifiedContract :=
  ⟨395, 396, 0, (.inc 4), s0395_plain_contract, 319, s0395_plain_checked⟩

def s0396_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, true, true, true, false] 0 .none⟩
theorem s0396_plain_checked : check 83 s0396_plain_contract = true := by decide +kernel
def s0396_plain : CertifiedContract :=
  ⟨396, 394, 0, .none, s0396_plain_contract, 83, s0396_plain_checked⟩

def s0397_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, true, false] 0 .none⟩
theorem s0397_zero_checked : check 321 s0397_zero_contract = true := by decide +kernel
def s0397_zero : CertifiedContract :=
  ⟨397, 405, 0, .none, s0397_zero_contract, 321, s0397_zero_checked⟩

def s0397_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s0397_positive_checked : check 327 s0397_positive_contract = true := by decide +kernel
def s0397_positive : CertifiedContract :=
  ⟨397, 398, 1, (.dec 0), s0397_positive_contract, 327, s0397_positive_checked⟩

def s0398_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0398_plain_checked : check 337 s0398_plain_contract = true := by decide +kernel
def s0398_plain : CertifiedContract :=
  ⟨398, 399, 0, (.inc 5), s0398_plain_contract, 337, s0398_plain_checked⟩

def s0399_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0399_zero_checked : check 363 s0399_zero_contract = true := by decide +kernel
def s0399_zero : CertifiedContract :=
  ⟨399, 401, 0, .none, s0399_zero_contract, 363, s0399_zero_checked⟩

def s0399_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0399_positive_checked : check 369 s0399_positive_contract = true := by decide +kernel
def s0399_positive : CertifiedContract :=
  ⟨399, 400, 1, (.dec 8), s0399_positive_contract, 369, s0399_positive_checked⟩

def s0400_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s0400_plain_checked : check 98 s0400_plain_contract = true := by decide +kernel
def s0400_plain : CertifiedContract :=
  ⟨400, 404, 0, .none, s0400_plain_contract, 98, s0400_plain_checked⟩

def s0401_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s0401_zero_checked : check 375 s0401_zero_contract = true := by decide +kernel
def s0401_zero : CertifiedContract :=
  ⟨401, 404, 0, .none, s0401_zero_contract, 375, s0401_zero_checked⟩

def s0401_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0401_positive_checked : check 378 s0401_positive_contract = true := by decide +kernel
def s0401_positive : CertifiedContract :=
  ⟨401, 402, 1, (.dec 5), s0401_positive_contract, 378, s0401_positive_checked⟩

def s0402_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0402_plain_checked : check 382 s0402_plain_contract = true := by decide +kernel
def s0402_plain : CertifiedContract :=
  ⟨402, 403, 0, (.inc 8), s0402_plain_contract, 382, s0402_plain_checked⟩

def s0403_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0403_plain_checked : check 101 s0403_plain_contract = true := by decide +kernel
def s0403_plain : CertifiedContract :=
  ⟨403, 401, 0, .none, s0403_plain_contract, 101, s0403_plain_checked⟩

def s0404_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, false] 0 .none⟩
theorem s0404_plain_checked : check 92 s0404_plain_contract = true := by decide +kernel
def s0404_plain : CertifiedContract :=
  ⟨404, 397, 0, .none, s0404_plain_contract, 92, s0404_plain_checked⟩

def s0405_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0405_zero_checked : check 321 s0405_zero_contract = true := by decide +kernel
def s0405_zero : CertifiedContract :=
  ⟨405, 408, 0, .none, s0405_zero_contract, 321, s0405_zero_checked⟩

def s0405_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0405_positive_checked : check 324 s0405_positive_contract = true := by decide +kernel
def s0405_positive : CertifiedContract :=
  ⟨405, 406, 1, (.dec 5), s0405_positive_contract, 324, s0405_positive_checked⟩

def s0406_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s0406_plain_checked : check 337 s0406_plain_contract = true := by decide +kernel
def s0406_plain : CertifiedContract :=
  ⟨406, 407, 0, (.inc 0), s0406_plain_contract, 337, s0406_plain_checked⟩

def s0407_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, true, false] 0 .none⟩
theorem s0407_plain_checked : check 86 s0407_plain_contract = true := by decide +kernel
def s0407_plain : CertifiedContract :=
  ⟨407, 405, 0, .none, s0407_plain_contract, 86, s0407_plain_checked⟩

def s0408_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, true, false] 0 .none⟩
theorem s0408_zero_checked : check 318 s0408_zero_contract = true := by decide +kernel
def s0408_zero : CertifiedContract :=
  ⟨408, 412, 0, .none, s0408_zero_contract, 318, s0408_zero_checked⟩

def s0408_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0408_positive_checked : check 324 s0408_positive_contract = true := by decide +kernel
def s0408_positive : CertifiedContract :=
  ⟨408, 409, 1, (.dec 2), s0408_positive_contract, 324, s0408_positive_checked⟩

def s0409_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0409_plain_checked : check 337 s0409_plain_contract = true := by decide +kernel
def s0409_plain : CertifiedContract :=
  ⟨409, 410, 0, (.inc 5), s0409_plain_contract, 337, s0409_plain_checked⟩

def s0410_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0410_plain_checked : check 364 s0410_plain_contract = true := by decide +kernel
def s0410_plain : CertifiedContract :=
  ⟨410, 411, 0, (.inc 8), s0410_plain_contract, 364, s0410_plain_checked⟩

def s0411_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0411_plain_checked : check 95 s0411_plain_contract = true := by decide +kernel
def s0411_plain : CertifiedContract :=
  ⟨411, 408, 0, .none, s0411_plain_contract, 95, s0411_plain_checked⟩

def s0412_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, false] 0 .none⟩
theorem s0412_zero_checked : check 339 s0412_zero_contract = true := by decide +kernel
def s0412_zero : CertifiedContract :=
  ⟨412, 418, 0, .none, s0412_zero_contract, 339, s0412_zero_checked⟩

def s0412_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0412_positive_checked : check 342 s0412_positive_contract = true := by decide +kernel
def s0412_positive : CertifiedContract :=
  ⟨412, 413, 1, (.dec 8), s0412_positive_contract, 342, s0412_positive_checked⟩

def s0413_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0413_plain_checked : check 337 s0413_plain_contract = true := by decide +kernel
def s0413_plain : CertifiedContract :=
  ⟨413, 414, 0, (.inc 5), s0413_plain_contract, 337, s0413_plain_checked⟩

def s0414_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, true, true, true] 0 .none⟩
theorem s0414_zero_checked : check 357 s0414_zero_contract = true := by decide +kernel
def s0414_zero : CertifiedContract :=
  ⟨414, 417, 0, .none, s0414_zero_contract, 357, s0414_zero_checked⟩

def s0414_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0414_positive_checked : check 360 s0414_positive_contract = true := by decide +kernel
def s0414_positive : CertifiedContract :=
  ⟨414, 415, 1, (.dec 8), s0414_positive_contract, 360, s0414_positive_checked⟩

def s0415_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0415_plain_checked : check 355 s0415_plain_contract = true := by decide +kernel
def s0415_plain : CertifiedContract :=
  ⟨415, 416, 0, (.inc 2), s0415_plain_contract, 355, s0415_plain_checked⟩

def s0416_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0416_plain_checked : check 95 s0416_plain_contract = true := by decide +kernel
def s0416_plain : CertifiedContract :=
  ⟨416, 414, 0, .none, s0416_plain_contract, 95, s0416_plain_checked⟩

def s0417_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0417_plain_checked : check 98 s0417_plain_contract = true := by decide +kernel
def s0417_plain : CertifiedContract :=
  ⟨417, 408, 0, .none, s0417_plain_contract, 98, s0417_plain_checked⟩

def s0418_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s0418_zero_checked : check 324 s0418_zero_contract = true := by decide +kernel
def s0418_zero : CertifiedContract :=
  ⟨418, 424, 0, .none, s0418_zero_contract, 324, s0418_zero_checked⟩

def s0418_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0418_positive_checked : check 324 s0418_positive_contract = true := by decide +kernel
def s0418_positive : CertifiedContract :=
  ⟨418, 419, 1, (.dec 5), s0418_positive_contract, 324, s0418_positive_checked⟩

def s0419_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0419_plain_checked : check 337 s0419_plain_contract = true := by decide +kernel
def s0419_plain : CertifiedContract :=
  ⟨419, 420, 0, (.inc 2), s0419_plain_contract, 337, s0419_plain_checked⟩

def s0420_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0420_plain_checked : check 340 s0420_plain_contract = true := by decide +kernel
def s0420_plain : CertifiedContract :=
  ⟨420, 421, 0, (.inc 2), s0420_plain_contract, 340, s0420_plain_checked⟩

def s0421_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0421_plain_checked : check 346 s0421_plain_contract = true := by decide +kernel
def s0421_plain : CertifiedContract :=
  ⟨421, 422, 0, (.inc 2), s0421_plain_contract, 346, s0421_plain_checked⟩

def s0422_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s0422_plain_checked : check 352 s0422_plain_contract = true := by decide +kernel
def s0422_plain : CertifiedContract :=
  ⟨422, 423, 0, (.inc 2), s0422_plain_contract, 352, s0422_plain_checked⟩

def s0423_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, false, true, true, false] 0 .none⟩
theorem s0423_plain_checked : check 83 s0423_plain_contract = true := by decide +kernel
def s0423_plain : CertifiedContract :=
  ⟨423, 418, 0, .none, s0423_plain_contract, 83, s0423_plain_checked⟩

def s0424_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, true, false] 0 .none⟩
theorem s0424_zero_checked : check 330 s0424_zero_contract = true := by decide +kernel
def s0424_zero : CertifiedContract :=
  ⟨424, 432, 0, .none, s0424_zero_contract, 330, s0424_zero_checked⟩

def s0424_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, true, false] 1 (.dec 0)⟩
theorem s0424_positive_checked : check 336 s0424_positive_contract = true := by decide +kernel
def s0424_positive : CertifiedContract :=
  ⟨424, 425, 1, (.dec 0), s0424_positive_contract, 336, s0424_positive_checked⟩

def s0425_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0425_plain_checked : check 346 s0425_plain_contract = true := by decide +kernel
def s0425_plain : CertifiedContract :=
  ⟨425, 426, 0, (.inc 5), s0425_plain_contract, 346, s0425_plain_checked⟩

def s0426_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s0426_zero_checked : check 372 s0426_zero_contract = true := by decide +kernel
def s0426_zero : CertifiedContract :=
  ⟨426, 428, 0, .none, s0426_zero_contract, 372, s0426_zero_checked⟩

def s0426_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0426_positive_checked : check 378 s0426_positive_contract = true := by decide +kernel
def s0426_positive : CertifiedContract :=
  ⟨426, 427, 1, (.dec 8), s0426_positive_contract, 378, s0426_positive_checked⟩

def s0427_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, true, true, true] 0 .none⟩
theorem s0427_plain_checked : check 101 s0427_plain_contract = true := by decide +kernel
def s0427_plain : CertifiedContract :=
  ⟨427, 431, 0, .none, s0427_plain_contract, 101, s0427_plain_checked⟩

def s0428_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, true, true, true] 0 .none⟩
theorem s0428_zero_checked : check 384 s0428_zero_contract = true := by decide +kernel
def s0428_zero : CertifiedContract :=
  ⟨428, 431, 0, .none, s0428_zero_contract, 384, s0428_zero_checked⟩

def s0428_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0428_positive_checked : check 387 s0428_positive_contract = true := by decide +kernel
def s0428_positive : CertifiedContract :=
  ⟨428, 429, 1, (.dec 5), s0428_positive_contract, 387, s0428_positive_checked⟩

def s0429_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0429_plain_checked : check 391 s0429_plain_contract = true := by decide +kernel
def s0429_plain : CertifiedContract :=
  ⟨429, 430, 0, (.inc 8), s0429_plain_contract, 391, s0429_plain_checked⟩

def s0430_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s0430_plain_checked : check 104 s0430_plain_contract = true := by decide +kernel
def s0430_plain : CertifiedContract :=
  ⟨430, 428, 0, .none, s0430_plain_contract, 104, s0430_plain_checked⟩

def s0431_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s0431_plain_checked : check 95 s0431_plain_contract = true := by decide +kernel
def s0431_plain : CertifiedContract :=
  ⟨431, 424, 0, .none, s0431_plain_contract, 95, s0431_plain_checked⟩

def s0432_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0432_zero_checked : check 330 s0432_zero_contract = true := by decide +kernel
def s0432_zero : CertifiedContract :=
  ⟨432, 435, 0, .none, s0432_zero_contract, 330, s0432_zero_checked⟩

def s0432_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0432_positive_checked : check 333 s0432_positive_contract = true := by decide +kernel
def s0432_positive : CertifiedContract :=
  ⟨432, 433, 1, (.dec 5), s0432_positive_contract, 333, s0432_positive_checked⟩

def s0433_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, true, true, true] 0 (.inc 0)⟩
theorem s0433_plain_checked : check 346 s0433_plain_contract = true := by decide +kernel
def s0433_plain : CertifiedContract :=
  ⟨433, 434, 0, (.inc 0), s0433_plain_contract, 346, s0433_plain_checked⟩

def s0434_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, false, true, false] 0 .none⟩
theorem s0434_plain_checked : check 89 s0434_plain_contract = true := by decide +kernel
def s0434_plain : CertifiedContract :=
  ⟨434, 432, 0, .none, s0434_plain_contract, 89, s0434_plain_checked⟩

def s0435_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0435_zero_checked : check 327 s0435_zero_contract = true := by decide +kernel
def s0435_zero : CertifiedContract :=
  ⟨435, 439, 0, .none, s0435_zero_contract, 327, s0435_zero_checked⟩

def s0435_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0435_positive_checked : check 333 s0435_positive_contract = true := by decide +kernel
def s0435_positive : CertifiedContract :=
  ⟨435, 436, 1, (.dec 2), s0435_positive_contract, 333, s0435_positive_checked⟩

def s0436_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0436_plain_checked : check 346 s0436_plain_contract = true := by decide +kernel
def s0436_plain : CertifiedContract :=
  ⟨436, 437, 0, (.inc 5), s0436_plain_contract, 346, s0436_plain_checked⟩

def s0437_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0437_plain_checked : check 373 s0437_plain_contract = true := by decide +kernel
def s0437_plain : CertifiedContract :=
  ⟨437, 438, 0, (.inc 8), s0437_plain_contract, 373, s0437_plain_checked⟩

def s0438_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0438_plain_checked : check 98 s0438_plain_contract = true := by decide +kernel
def s0438_plain : CertifiedContract :=
  ⟨438, 435, 0, .none, s0438_plain_contract, 98, s0438_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S008
