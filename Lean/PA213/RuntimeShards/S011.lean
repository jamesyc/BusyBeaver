import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S011
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s0537_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s0537_plain_checked : check 100 s0537_plain_contract = true := by decide +kernel
def s0537_plain : CertifiedContract :=
  ⟨537, 530, 0, .none, s0537_plain_contract, 100, s0537_plain_checked⟩

def s0538_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0538_zero_checked : check 347 s0538_zero_contract = true := by decide +kernel
def s0538_zero : CertifiedContract :=
  ⟨538, 541, 0, .none, s0538_zero_contract, 347, s0538_zero_checked⟩

def s0538_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0538_positive_checked : check 350 s0538_positive_contract = true := by decide +kernel
def s0538_positive : CertifiedContract :=
  ⟨538, 539, 1, (.dec 5), s0538_positive_contract, 350, s0538_positive_checked⟩

def s0539_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s0539_plain_checked : check 363 s0539_plain_contract = true := by decide +kernel
def s0539_plain : CertifiedContract :=
  ⟨539, 540, 0, (.inc 0), s0539_plain_contract, 363, s0539_plain_checked⟩

def s0540_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s0540_plain_checked : check 94 s0540_plain_contract = true := by decide +kernel
def s0540_plain : CertifiedContract :=
  ⟨540, 538, 0, .none, s0540_plain_contract, 94, s0540_plain_checked⟩

def s0541_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s0541_zero_checked : check 344 s0541_zero_contract = true := by decide +kernel
def s0541_zero : CertifiedContract :=
  ⟨541, 545, 0, .none, s0541_zero_contract, 344, s0541_zero_checked⟩

def s0541_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0541_positive_checked : check 350 s0541_positive_contract = true := by decide +kernel
def s0541_positive : CertifiedContract :=
  ⟨541, 542, 1, (.dec 2), s0541_positive_contract, 350, s0541_positive_checked⟩

def s0542_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0542_plain_checked : check 363 s0542_plain_contract = true := by decide +kernel
def s0542_plain : CertifiedContract :=
  ⟨542, 543, 0, (.inc 5), s0542_plain_contract, 363, s0542_plain_checked⟩

def s0543_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0543_plain_checked : check 390 s0543_plain_contract = true := by decide +kernel
def s0543_plain : CertifiedContract :=
  ⟨543, 544, 0, (.inc 8), s0543_plain_contract, 390, s0543_plain_checked⟩

def s0544_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0544_plain_checked : check 103 s0544_plain_contract = true := by decide +kernel
def s0544_plain : CertifiedContract :=
  ⟨544, 541, 0, .none, s0544_plain_contract, 103, s0544_plain_checked⟩

def s0545_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s0545_zero_checked : check 365 s0545_zero_contract = true := by decide +kernel
def s0545_zero : CertifiedContract :=
  ⟨545, 551, 0, .none, s0545_zero_contract, 365, s0545_zero_checked⟩

def s0545_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0545_positive_checked : check 368 s0545_positive_contract = true := by decide +kernel
def s0545_positive : CertifiedContract :=
  ⟨545, 546, 1, (.dec 8), s0545_positive_contract, 368, s0545_positive_checked⟩

def s0546_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0546_plain_checked : check 363 s0546_plain_contract = true := by decide +kernel
def s0546_plain : CertifiedContract :=
  ⟨546, 547, 0, (.inc 5), s0546_plain_contract, 363, s0546_plain_checked⟩

def s0547_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s0547_zero_checked : check 383 s0547_zero_contract = true := by decide +kernel
def s0547_zero : CertifiedContract :=
  ⟨547, 550, 0, .none, s0547_zero_contract, 383, s0547_zero_checked⟩

def s0547_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0547_positive_checked : check 386 s0547_positive_contract = true := by decide +kernel
def s0547_positive : CertifiedContract :=
  ⟨547, 548, 1, (.dec 8), s0547_positive_contract, 386, s0547_positive_checked⟩

def s0548_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0548_plain_checked : check 381 s0548_plain_contract = true := by decide +kernel
def s0548_plain : CertifiedContract :=
  ⟨548, 549, 0, (.inc 2), s0548_plain_contract, 381, s0548_plain_checked⟩

def s0549_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0549_plain_checked : check 103 s0549_plain_contract = true := by decide +kernel
def s0549_plain : CertifiedContract :=
  ⟨549, 547, 0, .none, s0549_plain_contract, 103, s0549_plain_checked⟩

def s0550_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0550_plain_checked : check 106 s0550_plain_contract = true := by decide +kernel
def s0550_plain : CertifiedContract :=
  ⟨550, 541, 0, .none, s0550_plain_contract, 106, s0550_plain_checked⟩

def s0551_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, true] 0 .none⟩
theorem s0551_zero_checked : check 350 s0551_zero_contract = true := by decide +kernel
def s0551_zero : CertifiedContract :=
  ⟨551, 557, 0, .none, s0551_zero_contract, 350, s0551_zero_checked⟩

def s0551_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0551_positive_checked : check 350 s0551_positive_contract = true := by decide +kernel
def s0551_positive : CertifiedContract :=
  ⟨551, 552, 1, (.dec 5), s0551_positive_contract, 350, s0551_positive_checked⟩

def s0552_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0552_plain_checked : check 363 s0552_plain_contract = true := by decide +kernel
def s0552_plain : CertifiedContract :=
  ⟨552, 553, 0, (.inc 2), s0552_plain_contract, 363, s0552_plain_checked⟩

def s0553_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0553_plain_checked : check 366 s0553_plain_contract = true := by decide +kernel
def s0553_plain : CertifiedContract :=
  ⟨553, 554, 0, (.inc 2), s0553_plain_contract, 366, s0553_plain_checked⟩

def s0554_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0554_plain_checked : check 363 s0554_plain_contract = true := by decide +kernel
def s0554_plain : CertifiedContract :=
  ⟨554, 555, 0, (.inc 2), s0554_plain_contract, 363, s0554_plain_checked⟩

def s0555_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s0555_plain_checked : check 369 s0555_plain_contract = true := by decide +kernel
def s0555_plain : CertifiedContract :=
  ⟨555, 556, 0, (.inc 2), s0555_plain_contract, 369, s0555_plain_checked⟩

def s0556_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s0556_plain_checked : check 91 s0556_plain_contract = true := by decide +kernel
def s0556_plain : CertifiedContract :=
  ⟨556, 551, 0, .none, s0556_plain_contract, 91, s0556_plain_checked⟩

def s0557_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, false, false] 0 (.inc 2)⟩
theorem s0557_plain_checked : check 324 s0557_plain_contract = true := by decide +kernel
def s0557_plain : CertifiedContract :=
  ⟨557, 558, 0, (.inc 2), s0557_plain_contract, 324, s0557_plain_checked⟩

def s0558_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, false, true] 0 (.inc 2)⟩
theorem s0558_plain_checked : check 309 s0558_plain_contract = true := by decide +kernel
def s0558_plain : CertifiedContract :=
  ⟨558, 559, 0, (.inc 2), s0558_plain_contract, 309, s0558_plain_checked⟩

def s0559_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, false, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, false, false] 0 (.inc 2)⟩
theorem s0559_plain_checked : check 312 s0559_plain_contract = true := by decide +kernel
def s0559_plain : CertifiedContract :=
  ⟨559, 560, 0, (.inc 2), s0559_plain_contract, 312, s0559_plain_checked⟩

def s0560_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s0560_zero_checked : check 344 s0560_zero_contract = true := by decide +kernel
def s0560_zero : CertifiedContract :=
  ⟨560, 563, 0, .none, s0560_zero_contract, 344, s0560_zero_checked⟩

def s0560_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s0560_positive_checked : check 350 s0560_positive_contract = true := by decide +kernel
def s0560_positive : CertifiedContract :=
  ⟨560, 561, 1, (.dec 2), s0560_positive_contract, 350, s0560_positive_checked⟩

def s0561_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s0561_plain_checked : check 363 s0561_plain_contract = true := by decide +kernel
def s0561_plain : CertifiedContract :=
  ⟨561, 562, 0, (.inc 8), s0561_plain_contract, 363, s0561_plain_checked⟩

def s0562_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, false, false] 0 .none⟩
theorem s0562_plain_checked : check 94 s0562_plain_contract = true := by decide +kernel
def s0562_plain : CertifiedContract :=
  ⟨562, 560, 0, .none, s0562_plain_contract, 94, s0562_plain_checked⟩

def s0563_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0563_zero_checked : check 365 s0563_zero_contract = true := by decide +kernel
def s0563_zero : CertifiedContract :=
  ⟨563, 566, 0, .none, s0563_zero_contract, 365, s0563_zero_checked⟩

def s0563_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0563_positive_checked : check 371 s0563_positive_contract = true := by decide +kernel
def s0563_positive : CertifiedContract :=
  ⟨563, 564, 1, (.dec 0), s0563_positive_contract, 371, s0563_positive_checked⟩

def s0564_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0564_plain_checked : check 363 s0564_plain_contract = true := by decide +kernel
def s0564_plain : CertifiedContract :=
  ⟨564, 565, 0, (.inc 2), s0564_plain_contract, 363, s0564_plain_checked⟩

def s0565_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s0565_plain_checked : check 97 s0565_plain_contract = true := by decide +kernel
def s0565_plain : CertifiedContract :=
  ⟨565, 563, 0, .none, s0565_plain_contract, 97, s0565_plain_checked⟩

def s0566_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0566_zero_checked : check 371 s0566_zero_contract = true := by decide +kernel
def s0566_zero : CertifiedContract :=
  ⟨566, 570, 0, .none, s0566_zero_contract, 371, s0566_zero_checked⟩

def s0566_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0566_positive_checked : check 377 s0566_positive_contract = true := by decide +kernel
def s0566_positive : CertifiedContract :=
  ⟨566, 567, 1, (.dec 2), s0566_positive_contract, 377, s0566_positive_checked⟩

def s0567_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0567_plain_checked : check 390 s0567_plain_contract = true := by decide +kernel
def s0567_plain : CertifiedContract :=
  ⟨567, 568, 0, (.inc 5), s0567_plain_contract, 390, s0567_plain_checked⟩

def s0568_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0568_plain_checked : check 417 s0568_plain_contract = true := by decide +kernel
def s0568_plain : CertifiedContract :=
  ⟨568, 569, 0, (.inc 8), s0568_plain_contract, 417, s0568_plain_checked⟩

def s0569_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0569_plain_checked : check 112 s0569_plain_contract = true := by decide +kernel
def s0569_plain : CertifiedContract :=
  ⟨569, 566, 0, .none, s0569_plain_contract, 112, s0569_plain_checked⟩

def s0570_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, false] 0 .none⟩
theorem s0570_zero_checked : check 392 s0570_zero_contract = true := by decide +kernel
def s0570_zero : CertifiedContract :=
  ⟨570, 576, 0, .none, s0570_zero_contract, 392, s0570_zero_checked⟩

def s0570_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0570_positive_checked : check 395 s0570_positive_contract = true := by decide +kernel
def s0570_positive : CertifiedContract :=
  ⟨570, 571, 1, (.dec 8), s0570_positive_contract, 395, s0570_positive_checked⟩

def s0571_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0571_plain_checked : check 390 s0571_plain_contract = true := by decide +kernel
def s0571_plain : CertifiedContract :=
  ⟨571, 572, 0, (.inc 5), s0571_plain_contract, 390, s0571_plain_checked⟩

def s0572_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s0572_zero_checked : check 410 s0572_zero_contract = true := by decide +kernel
def s0572_zero : CertifiedContract :=
  ⟨572, 575, 0, .none, s0572_zero_contract, 410, s0572_zero_checked⟩

def s0572_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0572_positive_checked : check 413 s0572_positive_contract = true := by decide +kernel
def s0572_positive : CertifiedContract :=
  ⟨572, 573, 1, (.dec 8), s0572_positive_contract, 413, s0572_positive_checked⟩

def s0573_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0573_plain_checked : check 408 s0573_plain_contract = true := by decide +kernel
def s0573_plain : CertifiedContract :=
  ⟨573, 574, 0, (.inc 2), s0573_plain_contract, 408, s0573_plain_checked⟩

def s0574_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0574_plain_checked : check 112 s0574_plain_contract = true := by decide +kernel
def s0574_plain : CertifiedContract :=
  ⟨574, 572, 0, .none, s0574_plain_contract, 112, s0574_plain_checked⟩

def s0575_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0575_plain_checked : check 115 s0575_plain_contract = true := by decide +kernel
def s0575_plain : CertifiedContract :=
  ⟨575, 566, 0, .none, s0575_plain_contract, 115, s0575_plain_checked⟩

def s0576_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s0576_zero_checked : check 380 s0576_zero_contract = true := by decide +kernel
def s0576_zero : CertifiedContract :=
  ⟨576, 579, 0, .none, s0576_zero_contract, 380, s0576_zero_checked⟩

def s0576_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0576_positive_checked : check 377 s0576_positive_contract = true := by decide +kernel
def s0576_positive : CertifiedContract :=
  ⟨576, 577, 1, (.dec 5), s0576_positive_contract, 377, s0576_positive_checked⟩

def s0577_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0577_plain_checked : check 390 s0577_plain_contract = true := by decide +kernel
def s0577_plain : CertifiedContract :=
  ⟨577, 578, 0, (.inc 0), s0577_plain_contract, 390, s0577_plain_checked⟩

def s0578_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, false] 0 .none⟩
theorem s0578_plain_checked : check 103 s0578_plain_contract = true := by decide +kernel
def s0578_plain : CertifiedContract :=
  ⟨578, 576, 0, .none, s0578_plain_contract, 103, s0578_plain_checked⟩

def s0579_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, false] 0 .none⟩
theorem s0579_zero_checked : check 344 s0579_zero_contract = true := by decide +kernel
def s0579_zero : CertifiedContract :=
  ⟨579, 583, 0, .none, s0579_zero_contract, 344, s0579_zero_checked⟩

def s0579_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, false, true, false] 1 (.dec 4)⟩
theorem s0579_positive_checked : check 350 s0579_positive_contract = true := by decide +kernel
def s0579_positive : CertifiedContract :=
  ⟨579, 580, 1, (.dec 4), s0579_positive_contract, 350, s0579_positive_checked⟩

def s0580_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0580_plain_checked : check 363 s0580_plain_contract = true := by decide +kernel
def s0580_plain : CertifiedContract :=
  ⟨580, 581, 0, (.inc 2), s0580_plain_contract, 363, s0580_plain_checked⟩

def s0581_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0581_plain_checked : check 390 s0581_plain_contract = true := by decide +kernel
def s0581_plain : CertifiedContract :=
  ⟨581, 582, 0, (.inc 8), s0581_plain_contract, 390, s0581_plain_checked⟩

def s0582_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s0582_plain_checked : check 103 s0582_plain_contract = true := by decide +kernel
def s0582_plain : CertifiedContract :=
  ⟨582, 579, 0, .none, s0582_plain_contract, 103, s0582_plain_checked⟩

def s0583_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s0583_zero_checked : check 350 s0583_zero_contract = true := by decide +kernel
def s0583_zero : CertifiedContract :=
  ⟨583, 586, 0, .none, s0583_zero_contract, 350, s0583_zero_checked⟩

def s0583_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s0583_positive_checked : check 350 s0583_positive_contract = true := by decide +kernel
def s0583_positive : CertifiedContract :=
  ⟨583, 584, 1, (.dec 8), s0583_positive_contract, 350, s0583_positive_checked⟩

def s0584_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, true, true] 0 (.inc 4)⟩
theorem s0584_plain_checked : check 354 s0584_plain_contract = true := by decide +kernel
def s0584_plain : CertifiedContract :=
  ⟨584, 585, 0, (.inc 4), s0584_plain_contract, 354, s0584_plain_checked⟩

def s0585_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, true, true, false] 0 .none⟩
theorem s0585_plain_checked : check 94 s0585_plain_contract = true := by decide +kernel
def s0585_plain : CertifiedContract :=
  ⟨585, 583, 0, .none, s0585_plain_contract, 94, s0585_plain_checked⟩

def s0586_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s0586_zero_checked : check 344 s0586_zero_contract = true := by decide +kernel
def s0586_zero : CertifiedContract :=
  ⟨586, 589, 0, .none, s0586_zero_contract, 344, s0586_zero_checked⟩

def s0586_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0586_positive_checked : check 350 s0586_positive_contract = true := by decide +kernel
def s0586_positive : CertifiedContract :=
  ⟨586, 587, 1, (.dec 2), s0586_positive_contract, 350, s0586_positive_checked⟩

def nonterminal : Array CertifiedContract := #[
  s0537_plain,
  s0538_zero,
  s0538_positive,
  s0539_plain,
  s0540_plain,
  s0541_zero,
  s0541_positive,
  s0542_plain,
  s0543_plain,
  s0544_plain,
  s0545_zero,
  s0545_positive,
  s0546_plain,
  s0547_zero,
  s0547_positive,
  s0548_plain,
  s0549_plain,
  s0550_plain,
  s0551_zero,
  s0551_positive,
  s0552_plain,
  s0553_plain,
  s0554_plain,
  s0555_plain,
  s0556_plain,
  s0557_plain,
  s0558_plain,
  s0559_plain,
  s0560_zero,
  s0560_positive,
  s0561_plain,
  s0562_plain,
  s0563_zero,
  s0563_positive,
  s0564_plain,
  s0565_plain,
  s0566_zero,
  s0566_positive,
  s0567_plain,
  s0568_plain,
  s0569_plain,
  s0570_zero,
  s0570_positive,
  s0571_plain,
  s0572_zero,
  s0572_positive,
  s0573_plain,
  s0574_plain,
  s0575_plain,
  s0576_zero,
  s0576_positive,
  s0577_plain,
  s0578_plain,
  s0579_zero,
  s0579_positive,
  s0580_plain,
  s0581_plain,
  s0582_plain,
  s0583_zero,
  s0583_positive,
  s0584_plain,
  s0585_plain,
  s0586_zero,
  s0586_positive
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S011
