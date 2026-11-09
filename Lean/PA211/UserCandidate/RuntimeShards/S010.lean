module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S010
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s0488_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0488_positive_checked : check 387 s0488_positive_contract = true := by decide +kernel
def s0488_positive : CertifiedContract :=
  ⟨488, 489, 1, (.dec 8), s0488_positive_contract, 387, s0488_positive_checked⟩

def s0489_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0489_plain_checked : check 382 s0489_plain_contract = true := by decide +kernel
def s0489_plain : CertifiedContract :=
  ⟨489, 490, 0, (.inc 5), s0489_plain_contract, 382, s0489_plain_checked⟩

def s0490_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s0490_zero_checked : check 402 s0490_zero_contract = true := by decide +kernel
def s0490_zero : CertifiedContract :=
  ⟨490, 493, 0, .none, s0490_zero_contract, 402, s0490_zero_checked⟩

def s0490_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0490_positive_checked : check 405 s0490_positive_contract = true := by decide +kernel
def s0490_positive : CertifiedContract :=
  ⟨490, 491, 1, (.dec 8), s0490_positive_contract, 405, s0490_positive_checked⟩

def s0491_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0491_plain_checked : check 400 s0491_plain_contract = true := by decide +kernel
def s0491_plain : CertifiedContract :=
  ⟨491, 492, 0, (.inc 2), s0491_plain_contract, 400, s0491_plain_checked⟩

def s0492_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0492_plain_checked : check 110 s0492_plain_contract = true := by decide +kernel
def s0492_plain : CertifiedContract :=
  ⟨492, 490, 0, .none, s0492_plain_contract, 110, s0492_plain_checked⟩

def s0493_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0493_plain_checked : check 113 s0493_plain_contract = true := by decide +kernel
def s0493_plain : CertifiedContract :=
  ⟨493, 484, 0, .none, s0493_plain_contract, 113, s0493_plain_checked⟩

def s0494_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s0494_zero_checked : check 372 s0494_zero_contract = true := by decide +kernel
def s0494_zero : CertifiedContract :=
  ⟨494, 497, 0, .none, s0494_zero_contract, 372, s0494_zero_checked⟩

def s0494_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0494_positive_checked : check 369 s0494_positive_contract = true := by decide +kernel
def s0494_positive : CertifiedContract :=
  ⟨494, 495, 1, (.dec 5), s0494_positive_contract, 369, s0494_positive_checked⟩

def s0495_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0495_plain_checked : check 382 s0495_plain_contract = true := by decide +kernel
def s0495_plain : CertifiedContract :=
  ⟨495, 496, 0, (.inc 0), s0495_plain_contract, 382, s0495_plain_checked⟩

def s0496_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s0496_plain_checked : check 101 s0496_plain_contract = true := by decide +kernel
def s0496_plain : CertifiedContract :=
  ⟨496, 494, 0, .none, s0496_plain_contract, 101, s0496_plain_checked⟩

def s0497_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s0497_zero_checked : check 336 s0497_zero_contract = true := by decide +kernel
def s0497_zero : CertifiedContract :=
  ⟨497, 501, 0, .none, s0497_zero_contract, 336, s0497_zero_checked⟩

def s0497_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, false, true, false] 1 (.dec 4)⟩
theorem s0497_positive_checked : check 342 s0497_positive_contract = true := by decide +kernel
def s0497_positive : CertifiedContract :=
  ⟨497, 498, 1, (.dec 4), s0497_positive_contract, 342, s0497_positive_checked⟩

def s0498_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0498_plain_checked : check 355 s0498_plain_contract = true := by decide +kernel
def s0498_plain : CertifiedContract :=
  ⟨498, 499, 0, (.inc 2), s0498_plain_contract, 355, s0498_plain_checked⟩

def s0499_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0499_plain_checked : check 382 s0499_plain_contract = true := by decide +kernel
def s0499_plain : CertifiedContract :=
  ⟨499, 500, 0, (.inc 8), s0499_plain_contract, 382, s0499_plain_checked⟩

def s0500_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s0500_plain_checked : check 101 s0500_plain_contract = true := by decide +kernel
def s0500_plain : CertifiedContract :=
  ⟨500, 497, 0, .none, s0500_plain_contract, 101, s0500_plain_checked⟩

def s0501_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0501_zero_checked : check 342 s0501_zero_contract = true := by decide +kernel
def s0501_zero : CertifiedContract :=
  ⟨501, 504, 0, .none, s0501_zero_contract, 342, s0501_zero_checked⟩

def s0501_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s0501_positive_checked : check 342 s0501_positive_contract = true := by decide +kernel
def s0501_positive : CertifiedContract :=
  ⟨501, 502, 1, (.dec 8), s0501_positive_contract, 342, s0501_positive_checked⟩

def s0502_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, true, true, true] 0 (.inc 4)⟩
theorem s0502_plain_checked : check 346 s0502_plain_contract = true := by decide +kernel
def s0502_plain : CertifiedContract :=
  ⟨502, 503, 0, (.inc 4), s0502_plain_contract, 346, s0502_plain_checked⟩

def s0503_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s0503_plain_checked : check 92 s0503_plain_contract = true := by decide +kernel
def s0503_plain : CertifiedContract :=
  ⟨503, 501, 0, .none, s0503_plain_contract, 92, s0503_plain_checked⟩

def s0504_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s0504_zero_checked : check 336 s0504_zero_contract = true := by decide +kernel
def s0504_zero : CertifiedContract :=
  ⟨504, 507, 0, .none, s0504_zero_contract, 336, s0504_zero_checked⟩

def s0504_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0504_positive_checked : check 342 s0504_positive_contract = true := by decide +kernel
def s0504_positive : CertifiedContract :=
  ⟨504, 505, 1, (.dec 2), s0504_positive_contract, 342, s0504_positive_checked⟩

def s0505_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s0505_plain_checked : check 355 s0505_plain_contract = true := by decide +kernel
def s0505_plain : CertifiedContract :=
  ⟨505, 506, 0, (.inc 8), s0505_plain_contract, 355, s0505_plain_checked⟩

def s0506_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0506_plain_checked : check 92 s0506_plain_contract = true := by decide +kernel
def s0506_plain : CertifiedContract :=
  ⟨506, 504, 0, .none, s0506_plain_contract, 92, s0506_plain_checked⟩

def s0507_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0507_zero_checked : check 357 s0507_zero_contract = true := by decide +kernel
def s0507_zero : CertifiedContract :=
  ⟨507, 510, 0, .none, s0507_zero_contract, 357, s0507_zero_checked⟩

def s0507_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0507_positive_checked : check 363 s0507_positive_contract = true := by decide +kernel
def s0507_positive : CertifiedContract :=
  ⟨507, 508, 1, (.dec 0), s0507_positive_contract, 363, s0507_positive_checked⟩

def s0508_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0508_plain_checked : check 355 s0508_plain_contract = true := by decide +kernel
def s0508_plain : CertifiedContract :=
  ⟨508, 509, 0, (.inc 2), s0508_plain_contract, 355, s0508_plain_checked⟩

def s0509_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s0509_plain_checked : check 95 s0509_plain_contract = true := by decide +kernel
def s0509_plain : CertifiedContract :=
  ⟨509, 507, 0, .none, s0509_plain_contract, 95, s0509_plain_checked⟩

def s0510_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0510_zero_checked : check 363 s0510_zero_contract = true := by decide +kernel
def s0510_zero : CertifiedContract :=
  ⟨510, 514, 0, .none, s0510_zero_contract, 363, s0510_zero_checked⟩

def s0510_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0510_positive_checked : check 369 s0510_positive_contract = true := by decide +kernel
def s0510_positive : CertifiedContract :=
  ⟨510, 511, 1, (.dec 2), s0510_positive_contract, 369, s0510_positive_checked⟩

def s0511_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0511_plain_checked : check 382 s0511_plain_contract = true := by decide +kernel
def s0511_plain : CertifiedContract :=
  ⟨511, 512, 0, (.inc 5), s0511_plain_contract, 382, s0511_plain_checked⟩

def s0512_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0512_plain_checked : check 409 s0512_plain_contract = true := by decide +kernel
def s0512_plain : CertifiedContract :=
  ⟨512, 513, 0, (.inc 8), s0512_plain_contract, 409, s0512_plain_checked⟩

def s0513_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0513_plain_checked : check 110 s0513_plain_contract = true := by decide +kernel
def s0513_plain : CertifiedContract :=
  ⟨513, 510, 0, .none, s0513_plain_contract, 110, s0513_plain_checked⟩

def s0514_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s0514_zero_checked : check 384 s0514_zero_contract = true := by decide +kernel
def s0514_zero : CertifiedContract :=
  ⟨514, 520, 0, .none, s0514_zero_contract, 384, s0514_zero_checked⟩

def s0514_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0514_positive_checked : check 387 s0514_positive_contract = true := by decide +kernel
def s0514_positive : CertifiedContract :=
  ⟨514, 515, 1, (.dec 8), s0514_positive_contract, 387, s0514_positive_checked⟩

def s0515_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0515_plain_checked : check 382 s0515_plain_contract = true := by decide +kernel
def s0515_plain : CertifiedContract :=
  ⟨515, 516, 0, (.inc 5), s0515_plain_contract, 382, s0515_plain_checked⟩

def s0516_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s0516_zero_checked : check 402 s0516_zero_contract = true := by decide +kernel
def s0516_zero : CertifiedContract :=
  ⟨516, 519, 0, .none, s0516_zero_contract, 402, s0516_zero_checked⟩

def s0516_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0516_positive_checked : check 405 s0516_positive_contract = true := by decide +kernel
def s0516_positive : CertifiedContract :=
  ⟨516, 517, 1, (.dec 8), s0516_positive_contract, 405, s0516_positive_checked⟩

def s0517_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0517_plain_checked : check 400 s0517_plain_contract = true := by decide +kernel
def s0517_plain : CertifiedContract :=
  ⟨517, 518, 0, (.inc 2), s0517_plain_contract, 400, s0517_plain_checked⟩

def s0518_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0518_plain_checked : check 110 s0518_plain_contract = true := by decide +kernel
def s0518_plain : CertifiedContract :=
  ⟨518, 516, 0, .none, s0518_plain_contract, 110, s0518_plain_checked⟩

def s0519_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0519_plain_checked : check 113 s0519_plain_contract = true := by decide +kernel
def s0519_plain : CertifiedContract :=
  ⟨519, 510, 0, .none, s0519_plain_contract, 113, s0519_plain_checked⟩

def s0520_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s0520_zero_checked : check 372 s0520_zero_contract = true := by decide +kernel
def s0520_zero : CertifiedContract :=
  ⟨520, 523, 0, .none, s0520_zero_contract, 372, s0520_zero_checked⟩

def s0520_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0520_positive_checked : check 369 s0520_positive_contract = true := by decide +kernel
def s0520_positive : CertifiedContract :=
  ⟨520, 521, 1, (.dec 5), s0520_positive_contract, 369, s0520_positive_checked⟩

def s0521_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0521_plain_checked : check 382 s0521_plain_contract = true := by decide +kernel
def s0521_plain : CertifiedContract :=
  ⟨521, 522, 0, (.inc 0), s0521_plain_contract, 382, s0521_plain_checked⟩

def s0522_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s0522_plain_checked : check 101 s0522_plain_contract = true := by decide +kernel
def s0522_plain : CertifiedContract :=
  ⟨522, 520, 0, .none, s0522_plain_contract, 101, s0522_plain_checked⟩

def s0523_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s0523_zero_checked : check 336 s0523_zero_contract = true := by decide +kernel
def s0523_zero : CertifiedContract :=
  ⟨523, 527, 0, .none, s0523_zero_contract, 336, s0523_zero_checked⟩

def s0523_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, true, false, true, false] 1 (.dec 3)⟩
theorem s0523_positive_checked : check 342 s0523_positive_contract = true := by decide +kernel
def s0523_positive : CertifiedContract :=
  ⟨523, 524, 1, (.dec 3), s0523_positive_contract, 342, s0523_positive_checked⟩

def s0524_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0524_plain_checked : check 355 s0524_plain_contract = true := by decide +kernel
def s0524_plain : CertifiedContract :=
  ⟨524, 525, 0, (.inc 2), s0524_plain_contract, 355, s0524_plain_checked⟩

def s0525_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0525_plain_checked : check 382 s0525_plain_contract = true := by decide +kernel
def s0525_plain : CertifiedContract :=
  ⟨525, 526, 0, (.inc 8), s0525_plain_contract, 382, s0525_plain_checked⟩

def s0526_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s0526_plain_checked : check 101 s0526_plain_contract = true := by decide +kernel
def s0526_plain : CertifiedContract :=
  ⟨526, 523, 0, .none, s0526_plain_contract, 101, s0526_plain_checked⟩

def s0527_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s0527_zero_checked : check 345 s0527_zero_contract = true := by decide +kernel
def s0527_zero : CertifiedContract :=
  ⟨527, 530, 0, .none, s0527_zero_contract, 345, s0527_zero_checked⟩

def s0527_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s0527_positive_checked : check 342 s0527_positive_contract = true := by decide +kernel
def s0527_positive : CertifiedContract :=
  ⟨527, 528, 1, (.dec 8), s0527_positive_contract, 342, s0527_positive_checked⟩

def s0528_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, true, true, true, true] 0 (.inc 3)⟩
theorem s0528_plain_checked : check 358 s0528_plain_contract = true := by decide +kernel
def s0528_plain : CertifiedContract :=
  ⟨528, 529, 0, (.inc 3), s0528_plain_contract, 358, s0528_plain_checked⟩

def s0529_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s0529_plain_checked : check 92 s0529_plain_contract = true := by decide +kernel
def s0529_plain : CertifiedContract :=
  ⟨529, 527, 0, .none, s0529_plain_contract, 92, s0529_plain_checked⟩

def s0530_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s0530_zero_checked : check 348 s0530_zero_contract = true := by decide +kernel
def s0530_zero : CertifiedContract :=
  ⟨530, 538, 0, .none, s0530_zero_contract, 348, s0530_zero_checked⟩

def s0530_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s0530_positive_checked : check 354 s0530_positive_contract = true := by decide +kernel
def s0530_positive : CertifiedContract :=
  ⟨530, 531, 1, (.dec 0), s0530_positive_contract, 354, s0530_positive_checked⟩

def s0531_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0531_plain_checked : check 364 s0531_plain_contract = true := by decide +kernel
def s0531_plain : CertifiedContract :=
  ⟨531, 532, 0, (.inc 5), s0531_plain_contract, 364, s0531_plain_checked⟩

def s0532_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0532_zero_checked : check 390 s0532_zero_contract = true := by decide +kernel
def s0532_zero : CertifiedContract :=
  ⟨532, 534, 0, .none, s0532_zero_contract, 390, s0532_zero_checked⟩

def s0532_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0532_positive_checked : check 396 s0532_positive_contract = true := by decide +kernel
def s0532_positive : CertifiedContract :=
  ⟨532, 533, 1, (.dec 8), s0532_positive_contract, 396, s0532_positive_checked⟩

def s0533_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s0533_plain_checked : check 107 s0533_plain_contract = true := by decide +kernel
def s0533_plain : CertifiedContract :=
  ⟨533, 537, 0, .none, s0533_plain_contract, 107, s0533_plain_checked⟩

def s0534_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s0534_zero_checked : check 402 s0534_zero_contract = true := by decide +kernel
def s0534_zero : CertifiedContract :=
  ⟨534, 537, 0, .none, s0534_zero_contract, 402, s0534_zero_checked⟩

def s0534_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0534_positive_checked : check 405 s0534_positive_contract = true := by decide +kernel
def s0534_positive : CertifiedContract :=
  ⟨534, 535, 1, (.dec 5), s0534_positive_contract, 405, s0534_positive_checked⟩

def s0535_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0535_plain_checked : check 409 s0535_plain_contract = true := by decide +kernel
def s0535_plain : CertifiedContract :=
  ⟨535, 536, 0, (.inc 8), s0535_plain_contract, 409, s0535_plain_checked⟩

def s0536_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0536_plain_checked : check 110 s0536_plain_contract = true := by decide +kernel
def s0536_plain : CertifiedContract :=
  ⟨536, 534, 0, .none, s0536_plain_contract, 110, s0536_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S010
