module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S012
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s0587_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s0587_plain_checked : check 363 s0587_plain_contract = true := by decide +kernel
def s0587_plain : CertifiedContract :=
  ⟨587, 588, 0, (.inc 8), s0587_plain_contract, 363, s0587_plain_checked⟩

def s0588_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s0588_plain_checked : check 94 s0588_plain_contract = true := by decide +kernel
def s0588_plain : CertifiedContract :=
  ⟨588, 586, 0, .none, s0588_plain_contract, 94, s0588_plain_checked⟩

def s0589_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0589_zero_checked : check 365 s0589_zero_contract = true := by decide +kernel
def s0589_zero : CertifiedContract :=
  ⟨589, 592, 0, .none, s0589_zero_contract, 365, s0589_zero_checked⟩

def s0589_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0589_positive_checked : check 371 s0589_positive_contract = true := by decide +kernel
def s0589_positive : CertifiedContract :=
  ⟨589, 590, 1, (.dec 0), s0589_positive_contract, 371, s0589_positive_checked⟩

def s0590_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0590_plain_checked : check 363 s0590_plain_contract = true := by decide +kernel
def s0590_plain : CertifiedContract :=
  ⟨590, 591, 0, (.inc 2), s0590_plain_contract, 363, s0590_plain_checked⟩

def s0591_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s0591_plain_checked : check 97 s0591_plain_contract = true := by decide +kernel
def s0591_plain : CertifiedContract :=
  ⟨591, 589, 0, .none, s0591_plain_contract, 97, s0591_plain_checked⟩

def s0592_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0592_zero_checked : check 371 s0592_zero_contract = true := by decide +kernel
def s0592_zero : CertifiedContract :=
  ⟨592, 596, 0, .none, s0592_zero_contract, 371, s0592_zero_checked⟩

def s0592_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0592_positive_checked : check 377 s0592_positive_contract = true := by decide +kernel
def s0592_positive : CertifiedContract :=
  ⟨592, 593, 1, (.dec 2), s0592_positive_contract, 377, s0592_positive_checked⟩

def s0593_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0593_plain_checked : check 390 s0593_plain_contract = true := by decide +kernel
def s0593_plain : CertifiedContract :=
  ⟨593, 594, 0, (.inc 5), s0593_plain_contract, 390, s0593_plain_checked⟩

def s0594_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0594_plain_checked : check 417 s0594_plain_contract = true := by decide +kernel
def s0594_plain : CertifiedContract :=
  ⟨594, 595, 0, (.inc 8), s0594_plain_contract, 417, s0594_plain_checked⟩

def s0595_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0595_plain_checked : check 112 s0595_plain_contract = true := by decide +kernel
def s0595_plain : CertifiedContract :=
  ⟨595, 592, 0, .none, s0595_plain_contract, 112, s0595_plain_checked⟩

def s0596_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s0596_zero_checked : check 392 s0596_zero_contract = true := by decide +kernel
def s0596_zero : CertifiedContract :=
  ⟨596, 602, 0, .none, s0596_zero_contract, 392, s0596_zero_checked⟩

def s0596_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0596_positive_checked : check 395 s0596_positive_contract = true := by decide +kernel
def s0596_positive : CertifiedContract :=
  ⟨596, 597, 1, (.dec 8), s0596_positive_contract, 395, s0596_positive_checked⟩

def s0597_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0597_plain_checked : check 390 s0597_plain_contract = true := by decide +kernel
def s0597_plain : CertifiedContract :=
  ⟨597, 598, 0, (.inc 5), s0597_plain_contract, 390, s0597_plain_checked⟩

def s0598_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s0598_zero_checked : check 410 s0598_zero_contract = true := by decide +kernel
def s0598_zero : CertifiedContract :=
  ⟨598, 601, 0, .none, s0598_zero_contract, 410, s0598_zero_checked⟩

def s0598_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0598_positive_checked : check 413 s0598_positive_contract = true := by decide +kernel
def s0598_positive : CertifiedContract :=
  ⟨598, 599, 1, (.dec 8), s0598_positive_contract, 413, s0598_positive_checked⟩

def s0599_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0599_plain_checked : check 408 s0599_plain_contract = true := by decide +kernel
def s0599_plain : CertifiedContract :=
  ⟨599, 600, 0, (.inc 2), s0599_plain_contract, 408, s0599_plain_checked⟩

def s0600_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0600_plain_checked : check 112 s0600_plain_contract = true := by decide +kernel
def s0600_plain : CertifiedContract :=
  ⟨600, 598, 0, .none, s0600_plain_contract, 112, s0600_plain_checked⟩

def s0601_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0601_plain_checked : check 115 s0601_plain_contract = true := by decide +kernel
def s0601_plain : CertifiedContract :=
  ⟨601, 592, 0, .none, s0601_plain_contract, 115, s0601_plain_checked⟩

def s0602_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, false, false] 0 .none⟩
theorem s0602_zero_checked : check 380 s0602_zero_contract = true := by decide +kernel
def s0602_zero : CertifiedContract :=
  ⟨602, 605, 0, .none, s0602_zero_contract, 380, s0602_zero_checked⟩

def s0602_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0602_positive_checked : check 377 s0602_positive_contract = true := by decide +kernel
def s0602_positive : CertifiedContract :=
  ⟨602, 603, 1, (.dec 5), s0602_positive_contract, 377, s0602_positive_checked⟩

def s0603_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0603_plain_checked : check 390 s0603_plain_contract = true := by decide +kernel
def s0603_plain : CertifiedContract :=
  ⟨603, 604, 0, (.inc 0), s0603_plain_contract, 390, s0603_plain_checked⟩

def s0604_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s0604_plain_checked : check 103 s0604_plain_contract = true := by decide +kernel
def s0604_plain : CertifiedContract :=
  ⟨604, 602, 0, .none, s0604_plain_contract, 103, s0604_plain_checked⟩

def s0605_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s0605_zero_checked : check 344 s0605_zero_contract = true := by decide +kernel
def s0605_zero : CertifiedContract :=
  ⟨605, 609, 0, .none, s0605_zero_contract, 344, s0605_zero_checked⟩

def s0605_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s0605_positive_checked : check 350 s0605_positive_contract = true := by decide +kernel
def s0605_positive : CertifiedContract :=
  ⟨605, 606, 1, (.dec 7), s0605_positive_contract, 350, s0605_positive_checked⟩

def s0606_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0606_plain_checked : check 354 s0606_plain_contract = true := by decide +kernel
def s0606_plain : CertifiedContract :=
  ⟨606, 607, 0, (.inc 2), s0606_plain_contract, 354, s0606_plain_checked⟩

def s0607_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0607_plain_checked : check 381 s0607_plain_contract = true := by decide +kernel
def s0607_plain : CertifiedContract :=
  ⟨607, 608, 0, (.inc 8), s0607_plain_contract, 381, s0607_plain_checked⟩

def s0608_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, false, false] 0 .none⟩
theorem s0608_plain_checked : check 100 s0608_plain_contract = true := by decide +kernel
def s0608_plain : CertifiedContract :=
  ⟨608, 605, 0, .none, s0608_plain_contract, 100, s0608_plain_checked⟩

def s0609_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, false] 0 .none⟩
theorem s0609_zero_checked : check 353 s0609_zero_contract = true := by decide +kernel
def s0609_zero : CertifiedContract :=
  ⟨609, 612, 0, .none, s0609_zero_contract, 353, s0609_zero_checked⟩

def s0609_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s0609_positive_checked : check 350 s0609_positive_contract = true := by decide +kernel
def s0609_positive : CertifiedContract :=
  ⟨609, 610, 1, (.dec 8), s0609_positive_contract, 350, s0609_positive_checked⟩

def s0610_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s0610_plain_checked : check 381 s0610_plain_contract = true := by decide +kernel
def s0610_plain : CertifiedContract :=
  ⟨610, 611, 0, (.inc 7), s0610_plain_contract, 381, s0610_plain_checked⟩

def s0611_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s0611_plain_checked : check 94 s0611_plain_contract = true := by decide +kernel
def s0611_plain : CertifiedContract :=
  ⟨611, 609, 0, .none, s0611_plain_contract, 94, s0611_plain_checked⟩

def s0612_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, true, false] 0 .none⟩
theorem s0612_zero_checked : check 356 s0612_zero_contract = true := by decide +kernel
def s0612_zero : CertifiedContract :=
  ⟨612, 620, 0, .none, s0612_zero_contract, 356, s0612_zero_checked⟩

def s0612_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s0612_positive_checked : check 362 s0612_positive_contract = true := by decide +kernel
def s0612_positive : CertifiedContract :=
  ⟨612, 613, 1, (.dec 0), s0612_positive_contract, 362, s0612_positive_checked⟩

def s0613_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0613_plain_checked : check 372 s0613_plain_contract = true := by decide +kernel
def s0613_plain : CertifiedContract :=
  ⟨613, 614, 0, (.inc 5), s0613_plain_contract, 372, s0613_plain_checked⟩

def s0614_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0614_zero_checked : check 398 s0614_zero_contract = true := by decide +kernel
def s0614_zero : CertifiedContract :=
  ⟨614, 616, 0, .none, s0614_zero_contract, 398, s0614_zero_checked⟩

def s0614_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0614_positive_checked : check 404 s0614_positive_contract = true := by decide +kernel
def s0614_positive : CertifiedContract :=
  ⟨614, 615, 1, (.dec 8), s0614_positive_contract, 404, s0614_positive_checked⟩

def s0615_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s0615_plain_checked : check 109 s0615_plain_contract = true := by decide +kernel
def s0615_plain : CertifiedContract :=
  ⟨615, 619, 0, .none, s0615_plain_contract, 109, s0615_plain_checked⟩

def s0616_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s0616_zero_checked : check 410 s0616_zero_contract = true := by decide +kernel
def s0616_zero : CertifiedContract :=
  ⟨616, 619, 0, .none, s0616_zero_contract, 410, s0616_zero_checked⟩

def s0616_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0616_positive_checked : check 413 s0616_positive_contract = true := by decide +kernel
def s0616_positive : CertifiedContract :=
  ⟨616, 617, 1, (.dec 5), s0616_positive_contract, 413, s0616_positive_checked⟩

def s0617_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0617_plain_checked : check 417 s0617_plain_contract = true := by decide +kernel
def s0617_plain : CertifiedContract :=
  ⟨617, 618, 0, (.inc 8), s0617_plain_contract, 417, s0617_plain_checked⟩

def s0618_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0618_plain_checked : check 112 s0618_plain_contract = true := by decide +kernel
def s0618_plain : CertifiedContract :=
  ⟨618, 616, 0, .none, s0618_plain_contract, 112, s0618_plain_checked⟩

def s0619_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, false, false] 0 .none⟩
theorem s0619_plain_checked : check 103 s0619_plain_contract = true := by decide +kernel
def s0619_plain : CertifiedContract :=
  ⟨619, 612, 0, .none, s0619_plain_contract, 103, s0619_plain_checked⟩

def s0620_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s0620_zero_checked : check 356 s0620_zero_contract = true := by decide +kernel
def s0620_zero : CertifiedContract :=
  ⟨620, 623, 0, .none, s0620_zero_contract, 356, s0620_zero_checked⟩

def s0620_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0620_positive_checked : check 359 s0620_positive_contract = true := by decide +kernel
def s0620_positive : CertifiedContract :=
  ⟨620, 621, 1, (.dec 5), s0620_positive_contract, 359, s0620_positive_checked⟩

def s0621_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s0621_plain_checked : check 372 s0621_plain_contract = true := by decide +kernel
def s0621_plain : CertifiedContract :=
  ⟨621, 622, 0, (.inc 0), s0621_plain_contract, 372, s0621_plain_checked⟩

def s0622_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, true, false] 0 .none⟩
theorem s0622_plain_checked : check 97 s0622_plain_contract = true := by decide +kernel
def s0622_plain : CertifiedContract :=
  ⟨622, 620, 0, .none, s0622_plain_contract, 97, s0622_plain_checked⟩

def s0623_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, true, false] 0 .none⟩
theorem s0623_zero_checked : check 353 s0623_zero_contract = true := by decide +kernel
def s0623_zero : CertifiedContract :=
  ⟨623, 627, 0, .none, s0623_zero_contract, 353, s0623_zero_checked⟩

def s0623_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0623_positive_checked : check 359 s0623_positive_contract = true := by decide +kernel
def s0623_positive : CertifiedContract :=
  ⟨623, 624, 1, (.dec 2), s0623_positive_contract, 359, s0623_positive_checked⟩

def s0624_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0624_plain_checked : check 372 s0624_plain_contract = true := by decide +kernel
def s0624_plain : CertifiedContract :=
  ⟨624, 625, 0, (.inc 5), s0624_plain_contract, 372, s0624_plain_checked⟩

def s0625_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0625_plain_checked : check 399 s0625_plain_contract = true := by decide +kernel
def s0625_plain : CertifiedContract :=
  ⟨625, 626, 0, (.inc 8), s0625_plain_contract, 399, s0625_plain_checked⟩

def s0626_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s0626_plain_checked : check 106 s0626_plain_contract = true := by decide +kernel
def s0626_plain : CertifiedContract :=
  ⟨626, 623, 0, .none, s0626_plain_contract, 106, s0626_plain_checked⟩

def s0627_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true, false] 0 .none⟩
theorem s0627_zero_checked : check 374 s0627_zero_contract = true := by decide +kernel
def s0627_zero : CertifiedContract :=
  ⟨627, 633, 0, .none, s0627_zero_contract, 374, s0627_zero_checked⟩

def s0627_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0627_positive_checked : check 377 s0627_positive_contract = true := by decide +kernel
def s0627_positive : CertifiedContract :=
  ⟨627, 628, 1, (.dec 8), s0627_positive_contract, 377, s0627_positive_checked⟩

def s0628_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0628_plain_checked : check 372 s0628_plain_contract = true := by decide +kernel
def s0628_plain : CertifiedContract :=
  ⟨628, 629, 0, (.inc 5), s0628_plain_contract, 372, s0628_plain_checked⟩

def s0629_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, true, true, true] 0 .none⟩
theorem s0629_zero_checked : check 392 s0629_zero_contract = true := by decide +kernel
def s0629_zero : CertifiedContract :=
  ⟨629, 632, 0, .none, s0629_zero_contract, 392, s0629_zero_checked⟩

def s0629_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0629_positive_checked : check 395 s0629_positive_contract = true := by decide +kernel
def s0629_positive : CertifiedContract :=
  ⟨629, 630, 1, (.dec 8), s0629_positive_contract, 395, s0629_positive_checked⟩

def s0630_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0630_plain_checked : check 390 s0630_plain_contract = true := by decide +kernel
def s0630_plain : CertifiedContract :=
  ⟨630, 631, 0, (.inc 2), s0630_plain_contract, 390, s0630_plain_checked⟩

def s0631_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0631_plain_checked : check 106 s0631_plain_contract = true := by decide +kernel
def s0631_plain : CertifiedContract :=
  ⟨631, 629, 0, .none, s0631_plain_contract, 106, s0631_plain_checked⟩

def s0632_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s0632_plain_checked : check 109 s0632_plain_contract = true := by decide +kernel
def s0632_plain : CertifiedContract :=
  ⟨632, 623, 0, .none, s0632_plain_contract, 109, s0632_plain_checked⟩

def s0633_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true] 0 .none⟩
theorem s0633_zero_checked : check 359 s0633_zero_contract = true := by decide +kernel
def s0633_zero : CertifiedContract :=
  ⟨633, 639, 0, .none, s0633_zero_contract, 359, s0633_zero_checked⟩

def s0633_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0633_positive_checked : check 359 s0633_positive_contract = true := by decide +kernel
def s0633_positive : CertifiedContract :=
  ⟨633, 634, 1, (.dec 5), s0633_positive_contract, 359, s0633_positive_checked⟩

def s0634_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0634_plain_checked : check 372 s0634_plain_contract = true := by decide +kernel
def s0634_plain : CertifiedContract :=
  ⟨634, 635, 0, (.inc 2), s0634_plain_contract, 372, s0634_plain_checked⟩

def s0635_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0635_plain_checked : check 375 s0635_plain_contract = true := by decide +kernel
def s0635_plain : CertifiedContract :=
  ⟨635, 636, 0, (.inc 2), s0635_plain_contract, 375, s0635_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s0587_plain,
  s0588_plain,
  s0589_zero,
  s0589_positive,
  s0590_plain,
  s0591_plain,
  s0592_zero,
  s0592_positive,
  s0593_plain,
  s0594_plain,
  s0595_plain,
  s0596_zero,
  s0596_positive,
  s0597_plain,
  s0598_zero,
  s0598_positive,
  s0599_plain,
  s0600_plain,
  s0601_plain,
  s0602_zero,
  s0602_positive,
  s0603_plain,
  s0604_plain,
  s0605_zero,
  s0605_positive,
  s0606_plain,
  s0607_plain,
  s0608_plain,
  s0609_zero,
  s0609_positive,
  s0610_plain,
  s0611_plain,
  s0612_zero,
  s0612_positive,
  s0613_plain,
  s0614_zero,
  s0614_positive,
  s0615_plain,
  s0616_zero,
  s0616_positive,
  s0617_plain,
  s0618_plain,
  s0619_plain,
  s0620_zero,
  s0620_positive,
  s0621_plain,
  s0622_plain,
  s0623_zero,
  s0623_positive,
  s0624_plain,
  s0625_plain,
  s0626_plain,
  s0627_zero,
  s0627_positive,
  s0628_plain,
  s0629_zero,
  s0629_positive,
  s0630_plain,
  s0631_plain,
  s0632_plain,
  s0633_zero,
  s0633_positive,
  s0634_plain,
  s0635_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S012
