import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S011
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s0537_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s0537_plain_checked : check 101 s0537_plain_contract = true := by decide +kernel
def s0537_plain : CertifiedContract :=
  ⟨537, 530, 0, .none, s0537_plain_contract, 101, s0537_plain_checked⟩

def s0538_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0538_zero_checked : check 348 s0538_zero_contract = true := by decide +kernel
def s0538_zero : CertifiedContract :=
  ⟨538, 541, 0, .none, s0538_zero_contract, 348, s0538_zero_checked⟩

def s0538_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0538_positive_checked : check 351 s0538_positive_contract = true := by decide +kernel
def s0538_positive : CertifiedContract :=
  ⟨538, 539, 1, (.dec 5), s0538_positive_contract, 351, s0538_positive_checked⟩

def s0539_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s0539_plain_checked : check 364 s0539_plain_contract = true := by decide +kernel
def s0539_plain : CertifiedContract :=
  ⟨539, 540, 0, (.inc 0), s0539_plain_contract, 364, s0539_plain_checked⟩

def s0540_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s0540_plain_checked : check 95 s0540_plain_contract = true := by decide +kernel
def s0540_plain : CertifiedContract :=
  ⟨540, 538, 0, .none, s0540_plain_contract, 95, s0540_plain_checked⟩

def s0541_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s0541_zero_checked : check 345 s0541_zero_contract = true := by decide +kernel
def s0541_zero : CertifiedContract :=
  ⟨541, 545, 0, .none, s0541_zero_contract, 345, s0541_zero_checked⟩

def s0541_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0541_positive_checked : check 351 s0541_positive_contract = true := by decide +kernel
def s0541_positive : CertifiedContract :=
  ⟨541, 542, 1, (.dec 2), s0541_positive_contract, 351, s0541_positive_checked⟩

def s0542_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0542_plain_checked : check 364 s0542_plain_contract = true := by decide +kernel
def s0542_plain : CertifiedContract :=
  ⟨542, 543, 0, (.inc 5), s0542_plain_contract, 364, s0542_plain_checked⟩

def s0543_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0543_plain_checked : check 391 s0543_plain_contract = true := by decide +kernel
def s0543_plain : CertifiedContract :=
  ⟨543, 544, 0, (.inc 8), s0543_plain_contract, 391, s0543_plain_checked⟩

def s0544_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0544_plain_checked : check 104 s0544_plain_contract = true := by decide +kernel
def s0544_plain : CertifiedContract :=
  ⟨544, 541, 0, .none, s0544_plain_contract, 104, s0544_plain_checked⟩

def s0545_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s0545_zero_checked : check 366 s0545_zero_contract = true := by decide +kernel
def s0545_zero : CertifiedContract :=
  ⟨545, 551, 0, .none, s0545_zero_contract, 366, s0545_zero_checked⟩

def s0545_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0545_positive_checked : check 369 s0545_positive_contract = true := by decide +kernel
def s0545_positive : CertifiedContract :=
  ⟨545, 546, 1, (.dec 8), s0545_positive_contract, 369, s0545_positive_checked⟩

def s0546_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0546_plain_checked : check 364 s0546_plain_contract = true := by decide +kernel
def s0546_plain : CertifiedContract :=
  ⟨546, 547, 0, (.inc 5), s0546_plain_contract, 364, s0546_plain_checked⟩

def s0547_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s0547_zero_checked : check 384 s0547_zero_contract = true := by decide +kernel
def s0547_zero : CertifiedContract :=
  ⟨547, 550, 0, .none, s0547_zero_contract, 384, s0547_zero_checked⟩

def s0547_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0547_positive_checked : check 387 s0547_positive_contract = true := by decide +kernel
def s0547_positive : CertifiedContract :=
  ⟨547, 548, 1, (.dec 8), s0547_positive_contract, 387, s0547_positive_checked⟩

def s0548_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0548_plain_checked : check 382 s0548_plain_contract = true := by decide +kernel
def s0548_plain : CertifiedContract :=
  ⟨548, 549, 0, (.inc 2), s0548_plain_contract, 382, s0548_plain_checked⟩

def s0549_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0549_plain_checked : check 104 s0549_plain_contract = true := by decide +kernel
def s0549_plain : CertifiedContract :=
  ⟨549, 547, 0, .none, s0549_plain_contract, 104, s0549_plain_checked⟩

def s0550_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0550_plain_checked : check 107 s0550_plain_contract = true := by decide +kernel
def s0550_plain : CertifiedContract :=
  ⟨550, 541, 0, .none, s0550_plain_contract, 107, s0550_plain_checked⟩

def s0551_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, true] 0 .none⟩
theorem s0551_zero_checked : check 351 s0551_zero_contract = true := by decide +kernel
def s0551_zero : CertifiedContract :=
  ⟨551, 557, 0, .none, s0551_zero_contract, 351, s0551_zero_checked⟩

def s0551_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0551_positive_checked : check 351 s0551_positive_contract = true := by decide +kernel
def s0551_positive : CertifiedContract :=
  ⟨551, 552, 1, (.dec 5), s0551_positive_contract, 351, s0551_positive_checked⟩

def s0552_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0552_plain_checked : check 364 s0552_plain_contract = true := by decide +kernel
def s0552_plain : CertifiedContract :=
  ⟨552, 553, 0, (.inc 2), s0552_plain_contract, 364, s0552_plain_checked⟩

def s0553_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0553_plain_checked : check 367 s0553_plain_contract = true := by decide +kernel
def s0553_plain : CertifiedContract :=
  ⟨553, 554, 0, (.inc 2), s0553_plain_contract, 367, s0553_plain_checked⟩

def s0554_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0554_plain_checked : check 373 s0554_plain_contract = true := by decide +kernel
def s0554_plain : CertifiedContract :=
  ⟨554, 555, 0, (.inc 2), s0554_plain_contract, 373, s0554_plain_checked⟩

def s0555_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s0555_plain_checked : check 379 s0555_plain_contract = true := by decide +kernel
def s0555_plain : CertifiedContract :=
  ⟨555, 556, 0, (.inc 2), s0555_plain_contract, 379, s0555_plain_checked⟩

def s0556_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s0556_plain_checked : check 92 s0556_plain_contract = true := by decide +kernel
def s0556_plain : CertifiedContract :=
  ⟨556, 551, 0, .none, s0556_plain_contract, 92, s0556_plain_checked⟩

def s0557_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, false, false] 0 (.inc 2)⟩
theorem s0557_plain_checked : check 325 s0557_plain_contract = true := by decide +kernel
def s0557_plain : CertifiedContract :=
  ⟨557, 558, 0, (.inc 2), s0557_plain_contract, 325, s0557_plain_checked⟩

def s0558_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, false, true] 0 (.inc 2)⟩
theorem s0558_plain_checked : check 310 s0558_plain_contract = true := by decide +kernel
def s0558_plain : CertifiedContract :=
  ⟨558, 559, 0, (.inc 2), s0558_plain_contract, 310, s0558_plain_checked⟩

def s0559_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, false, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, false, false] 0 (.inc 2)⟩
theorem s0559_plain_checked : check 313 s0559_plain_contract = true := by decide +kernel
def s0559_plain : CertifiedContract :=
  ⟨559, 560, 0, (.inc 2), s0559_plain_contract, 313, s0559_plain_checked⟩

def s0560_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s0560_zero_checked : check 354 s0560_zero_contract = true := by decide +kernel
def s0560_zero : CertifiedContract :=
  ⟨560, 563, 0, .none, s0560_zero_contract, 354, s0560_zero_checked⟩

def s0560_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s0560_positive_checked : check 360 s0560_positive_contract = true := by decide +kernel
def s0560_positive : CertifiedContract :=
  ⟨560, 561, 1, (.dec 2), s0560_positive_contract, 360, s0560_positive_checked⟩

def s0561_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s0561_plain_checked : check 373 s0561_plain_contract = true := by decide +kernel
def s0561_plain : CertifiedContract :=
  ⟨561, 562, 0, (.inc 8), s0561_plain_contract, 373, s0561_plain_checked⟩

def s0562_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, false, false] 0 .none⟩
theorem s0562_plain_checked : check 98 s0562_plain_contract = true := by decide +kernel
def s0562_plain : CertifiedContract :=
  ⟨562, 560, 0, .none, s0562_plain_contract, 98, s0562_plain_checked⟩

def s0563_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0563_zero_checked : check 375 s0563_zero_contract = true := by decide +kernel
def s0563_zero : CertifiedContract :=
  ⟨563, 566, 0, .none, s0563_zero_contract, 375, s0563_zero_checked⟩

def s0563_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0563_positive_checked : check 381 s0563_positive_contract = true := by decide +kernel
def s0563_positive : CertifiedContract :=
  ⟨563, 564, 1, (.dec 0), s0563_positive_contract, 381, s0563_positive_checked⟩

def s0564_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0564_plain_checked : check 373 s0564_plain_contract = true := by decide +kernel
def s0564_plain : CertifiedContract :=
  ⟨564, 565, 0, (.inc 2), s0564_plain_contract, 373, s0564_plain_checked⟩

def s0565_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s0565_plain_checked : check 101 s0565_plain_contract = true := by decide +kernel
def s0565_plain : CertifiedContract :=
  ⟨565, 563, 0, .none, s0565_plain_contract, 101, s0565_plain_checked⟩

def s0566_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0566_zero_checked : check 381 s0566_zero_contract = true := by decide +kernel
def s0566_zero : CertifiedContract :=
  ⟨566, 570, 0, .none, s0566_zero_contract, 381, s0566_zero_checked⟩

def s0566_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0566_positive_checked : check 387 s0566_positive_contract = true := by decide +kernel
def s0566_positive : CertifiedContract :=
  ⟨566, 567, 1, (.dec 2), s0566_positive_contract, 387, s0566_positive_checked⟩

def s0567_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0567_plain_checked : check 400 s0567_plain_contract = true := by decide +kernel
def s0567_plain : CertifiedContract :=
  ⟨567, 568, 0, (.inc 5), s0567_plain_contract, 400, s0567_plain_checked⟩

def s0568_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0568_plain_checked : check 427 s0568_plain_contract = true := by decide +kernel
def s0568_plain : CertifiedContract :=
  ⟨568, 569, 0, (.inc 8), s0568_plain_contract, 427, s0568_plain_checked⟩

def s0569_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0569_plain_checked : check 116 s0569_plain_contract = true := by decide +kernel
def s0569_plain : CertifiedContract :=
  ⟨569, 566, 0, .none, s0569_plain_contract, 116, s0569_plain_checked⟩

def s0570_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, false] 0 .none⟩
theorem s0570_zero_checked : check 402 s0570_zero_contract = true := by decide +kernel
def s0570_zero : CertifiedContract :=
  ⟨570, 576, 0, .none, s0570_zero_contract, 402, s0570_zero_checked⟩

def s0570_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0570_positive_checked : check 405 s0570_positive_contract = true := by decide +kernel
def s0570_positive : CertifiedContract :=
  ⟨570, 571, 1, (.dec 8), s0570_positive_contract, 405, s0570_positive_checked⟩

def s0571_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0571_plain_checked : check 400 s0571_plain_contract = true := by decide +kernel
def s0571_plain : CertifiedContract :=
  ⟨571, 572, 0, (.inc 5), s0571_plain_contract, 400, s0571_plain_checked⟩

def s0572_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s0572_zero_checked : check 420 s0572_zero_contract = true := by decide +kernel
def s0572_zero : CertifiedContract :=
  ⟨572, 575, 0, .none, s0572_zero_contract, 420, s0572_zero_checked⟩

def s0572_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0572_positive_checked : check 423 s0572_positive_contract = true := by decide +kernel
def s0572_positive : CertifiedContract :=
  ⟨572, 573, 1, (.dec 8), s0572_positive_contract, 423, s0572_positive_checked⟩

def s0573_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0573_plain_checked : check 418 s0573_plain_contract = true := by decide +kernel
def s0573_plain : CertifiedContract :=
  ⟨573, 574, 0, (.inc 2), s0573_plain_contract, 418, s0573_plain_checked⟩

def s0574_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0574_plain_checked : check 116 s0574_plain_contract = true := by decide +kernel
def s0574_plain : CertifiedContract :=
  ⟨574, 572, 0, .none, s0574_plain_contract, 116, s0574_plain_checked⟩

def s0575_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0575_plain_checked : check 119 s0575_plain_contract = true := by decide +kernel
def s0575_plain : CertifiedContract :=
  ⟨575, 566, 0, .none, s0575_plain_contract, 119, s0575_plain_checked⟩

def s0576_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s0576_zero_checked : check 390 s0576_zero_contract = true := by decide +kernel
def s0576_zero : CertifiedContract :=
  ⟨576, 579, 0, .none, s0576_zero_contract, 390, s0576_zero_checked⟩

def s0576_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0576_positive_checked : check 387 s0576_positive_contract = true := by decide +kernel
def s0576_positive : CertifiedContract :=
  ⟨576, 577, 1, (.dec 5), s0576_positive_contract, 387, s0576_positive_checked⟩

def s0577_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0577_plain_checked : check 400 s0577_plain_contract = true := by decide +kernel
def s0577_plain : CertifiedContract :=
  ⟨577, 578, 0, (.inc 0), s0577_plain_contract, 400, s0577_plain_checked⟩

def s0578_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, false] 0 .none⟩
theorem s0578_plain_checked : check 107 s0578_plain_contract = true := by decide +kernel
def s0578_plain : CertifiedContract :=
  ⟨578, 576, 0, .none, s0578_plain_contract, 107, s0578_plain_checked⟩

def s0579_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, false] 0 .none⟩
theorem s0579_zero_checked : check 354 s0579_zero_contract = true := by decide +kernel
def s0579_zero : CertifiedContract :=
  ⟨579, 583, 0, .none, s0579_zero_contract, 354, s0579_zero_checked⟩

def s0579_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, false, true, false] 1 (.dec 4)⟩
theorem s0579_positive_checked : check 360 s0579_positive_contract = true := by decide +kernel
def s0579_positive : CertifiedContract :=
  ⟨579, 580, 1, (.dec 4), s0579_positive_contract, 360, s0579_positive_checked⟩

def s0580_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0580_plain_checked : check 373 s0580_plain_contract = true := by decide +kernel
def s0580_plain : CertifiedContract :=
  ⟨580, 581, 0, (.inc 2), s0580_plain_contract, 373, s0580_plain_checked⟩

def s0581_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0581_plain_checked : check 400 s0581_plain_contract = true := by decide +kernel
def s0581_plain : CertifiedContract :=
  ⟨581, 582, 0, (.inc 8), s0581_plain_contract, 400, s0581_plain_checked⟩

def s0582_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s0582_plain_checked : check 107 s0582_plain_contract = true := by decide +kernel
def s0582_plain : CertifiedContract :=
  ⟨582, 579, 0, .none, s0582_plain_contract, 107, s0582_plain_checked⟩

def s0583_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s0583_zero_checked : check 360 s0583_zero_contract = true := by decide +kernel
def s0583_zero : CertifiedContract :=
  ⟨583, 586, 0, .none, s0583_zero_contract, 360, s0583_zero_checked⟩

def s0583_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s0583_positive_checked : check 360 s0583_positive_contract = true := by decide +kernel
def s0583_positive : CertifiedContract :=
  ⟨583, 584, 1, (.dec 8), s0583_positive_contract, 360, s0583_positive_checked⟩

def s0584_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, true, true] 0 (.inc 4)⟩
theorem s0584_plain_checked : check 364 s0584_plain_contract = true := by decide +kernel
def s0584_plain : CertifiedContract :=
  ⟨584, 585, 0, (.inc 4), s0584_plain_contract, 364, s0584_plain_checked⟩

def s0585_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, false] 0 .none⟩
theorem s0585_plain_checked : check 98 s0585_plain_contract = true := by decide +kernel
def s0585_plain : CertifiedContract :=
  ⟨585, 583, 0, .none, s0585_plain_contract, 98, s0585_plain_checked⟩

def s0586_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s0586_zero_checked : check 354 s0586_zero_contract = true := by decide +kernel
def s0586_zero : CertifiedContract :=
  ⟨586, 589, 0, .none, s0586_zero_contract, 354, s0586_zero_checked⟩

def s0586_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0586_positive_checked : check 360 s0586_positive_contract = true := by decide +kernel
def s0586_positive : CertifiedContract :=
  ⟨586, 587, 1, (.dec 2), s0586_positive_contract, 360, s0586_positive_checked⟩

end PA211.UserCandidate.RuntimeShards.S011
