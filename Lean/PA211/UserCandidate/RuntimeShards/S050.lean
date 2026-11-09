module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S050
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s2463_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2463_positive_checked : check 396 s2463_positive_contract = true := by decide +kernel
def s2463_positive : CertifiedContract :=
  ⟨2463, 2464, 1, (.dec 2), s2463_positive_contract, 396, s2463_positive_checked⟩

def s2464_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s2464_plain_checked : check 409 s2464_plain_contract = true := by decide +kernel
def s2464_plain : CertifiedContract :=
  ⟨2464, 2465, 0, (.inc 8), s2464_plain_contract, 409, s2464_plain_checked⟩

def s2465_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s2465_plain_checked : check 110 s2465_plain_contract = true := by decide +kernel
def s2465_plain : CertifiedContract :=
  ⟨2465, 2463, 0, .none, s2465_plain_contract, 110, s2465_plain_checked⟩

def s2466_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2466_zero_checked : check 411 s2466_zero_contract = true := by decide +kernel
def s2466_zero : CertifiedContract :=
  ⟨2466, 2469, 0, .none, s2466_zero_contract, 411, s2466_zero_checked⟩

def s2466_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2466_positive_checked : check 417 s2466_positive_contract = true := by decide +kernel
def s2466_positive : CertifiedContract :=
  ⟨2466, 2467, 1, (.dec 0), s2466_positive_contract, 417, s2466_positive_checked⟩

def s2467_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2467_plain_checked : check 409 s2467_plain_contract = true := by decide +kernel
def s2467_plain : CertifiedContract :=
  ⟨2467, 2468, 0, (.inc 2), s2467_plain_contract, 409, s2467_plain_checked⟩

def s2468_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s2468_plain_checked : check 113 s2468_plain_contract = true := by decide +kernel
def s2468_plain : CertifiedContract :=
  ⟨2468, 2466, 0, .none, s2468_plain_contract, 113, s2468_plain_checked⟩

def s2469_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2469_zero_checked : check 417 s2469_zero_contract = true := by decide +kernel
def s2469_zero : CertifiedContract :=
  ⟨2469, 2473, 0, .none, s2469_zero_contract, 417, s2469_zero_checked⟩

def s2469_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2469_positive_checked : check 423 s2469_positive_contract = true := by decide +kernel
def s2469_positive : CertifiedContract :=
  ⟨2469, 2470, 1, (.dec 2), s2469_positive_contract, 423, s2469_positive_checked⟩

def s2470_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2470_plain_checked : check 436 s2470_plain_contract = true := by decide +kernel
def s2470_plain : CertifiedContract :=
  ⟨2470, 2471, 0, (.inc 5), s2470_plain_contract, 436, s2470_plain_checked⟩

def s2471_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2471_plain_checked : check 463 s2471_plain_contract = true := by decide +kernel
def s2471_plain : CertifiedContract :=
  ⟨2471, 2472, 0, (.inc 8), s2471_plain_contract, 463, s2471_plain_checked⟩

def s2472_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2472_plain_checked : check 128 s2472_plain_contract = true := by decide +kernel
def s2472_plain : CertifiedContract :=
  ⟨2472, 2469, 0, .none, s2472_plain_contract, 128, s2472_plain_checked⟩

def s2473_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s2473_zero_checked : check 438 s2473_zero_contract = true := by decide +kernel
def s2473_zero : CertifiedContract :=
  ⟨2473, 2479, 0, .none, s2473_zero_contract, 438, s2473_zero_checked⟩

def s2473_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2473_positive_checked : check 441 s2473_positive_contract = true := by decide +kernel
def s2473_positive : CertifiedContract :=
  ⟨2473, 2474, 1, (.dec 8), s2473_positive_contract, 441, s2473_positive_checked⟩

def s2474_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2474_plain_checked : check 436 s2474_plain_contract = true := by decide +kernel
def s2474_plain : CertifiedContract :=
  ⟨2474, 2475, 0, (.inc 5), s2474_plain_contract, 436, s2474_plain_checked⟩

def s2475_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s2475_zero_checked : check 456 s2475_zero_contract = true := by decide +kernel
def s2475_zero : CertifiedContract :=
  ⟨2475, 2478, 0, .none, s2475_zero_contract, 456, s2475_zero_checked⟩

def s2475_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2475_positive_checked : check 459 s2475_positive_contract = true := by decide +kernel
def s2475_positive : CertifiedContract :=
  ⟨2475, 2476, 1, (.dec 8), s2475_positive_contract, 459, s2475_positive_checked⟩

def s2476_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2476_plain_checked : check 454 s2476_plain_contract = true := by decide +kernel
def s2476_plain : CertifiedContract :=
  ⟨2476, 2477, 0, (.inc 2), s2476_plain_contract, 454, s2476_plain_checked⟩

def s2477_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2477_plain_checked : check 128 s2477_plain_contract = true := by decide +kernel
def s2477_plain : CertifiedContract :=
  ⟨2477, 2475, 0, .none, s2477_plain_contract, 128, s2477_plain_checked⟩

def s2478_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2478_plain_checked : check 131 s2478_plain_contract = true := by decide +kernel
def s2478_plain : CertifiedContract :=
  ⟨2478, 2469, 0, .none, s2478_plain_contract, 131, s2478_plain_checked⟩

def s2479_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s2479_zero_checked : check 426 s2479_zero_contract = true := by decide +kernel
def s2479_zero : CertifiedContract :=
  ⟨2479, 2482, 0, .none, s2479_zero_contract, 426, s2479_zero_checked⟩

def s2479_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2479_positive_checked : check 423 s2479_positive_contract = true := by decide +kernel
def s2479_positive : CertifiedContract :=
  ⟨2479, 2480, 1, (.dec 5), s2479_positive_contract, 423, s2479_positive_checked⟩

def s2480_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2480_plain_checked : check 436 s2480_plain_contract = true := by decide +kernel
def s2480_plain : CertifiedContract :=
  ⟨2480, 2481, 0, (.inc 0), s2480_plain_contract, 436, s2480_plain_checked⟩

def s2481_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s2481_plain_checked : check 119 s2481_plain_contract = true := by decide +kernel
def s2481_plain : CertifiedContract :=
  ⟨2481, 2479, 0, .none, s2481_plain_contract, 119, s2481_plain_checked⟩

def s2482_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s2482_zero_checked : check 390 s2482_zero_contract = true := by decide +kernel
def s2482_zero : CertifiedContract :=
  ⟨2482, 2486, 0, .none, s2482_zero_contract, 390, s2482_zero_checked⟩

def s2482_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s2482_positive_checked : check 396 s2482_positive_contract = true := by decide +kernel
def s2482_positive : CertifiedContract :=
  ⟨2482, 2483, 1, (.dec 7), s2482_positive_contract, 396, s2482_positive_checked⟩

def s2483_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2483_plain_checked : check 400 s2483_plain_contract = true := by decide +kernel
def s2483_plain : CertifiedContract :=
  ⟨2483, 2484, 0, (.inc 2), s2483_plain_contract, 400, s2483_plain_checked⟩

def s2484_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2484_plain_checked : check 427 s2484_plain_contract = true := by decide +kernel
def s2484_plain : CertifiedContract :=
  ⟨2484, 2485, 0, (.inc 8), s2484_plain_contract, 427, s2484_plain_checked⟩

def s2485_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s2485_plain_checked : check 116 s2485_plain_contract = true := by decide +kernel
def s2485_plain : CertifiedContract :=
  ⟨2485, 2482, 0, .none, s2485_plain_contract, 116, s2485_plain_checked⟩

def s2486_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s2486_zero_checked : check 399 s2486_zero_contract = true := by decide +kernel
def s2486_zero : CertifiedContract :=
  ⟨2486, 2489, 0, .none, s2486_zero_contract, 399, s2486_zero_checked⟩

def s2486_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s2486_positive_checked : check 396 s2486_positive_contract = true := by decide +kernel
def s2486_positive : CertifiedContract :=
  ⟨2486, 2487, 1, (.dec 8), s2486_positive_contract, 396, s2486_positive_checked⟩

def s2487_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s2487_plain_checked : check 427 s2487_plain_contract = true := by decide +kernel
def s2487_plain : CertifiedContract :=
  ⟨2487, 2488, 0, (.inc 7), s2487_plain_contract, 427, s2487_plain_checked⟩

def s2488_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s2488_plain_checked : check 110 s2488_plain_contract = true := by decide +kernel
def s2488_plain : CertifiedContract :=
  ⟨2488, 2486, 0, .none, s2488_plain_contract, 110, s2488_plain_checked⟩

def s2489_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s2489_zero_checked : check 393 s2489_zero_contract = true := by decide +kernel
def s2489_zero : CertifiedContract :=
  ⟨2489, 2497, 0, .none, s2489_zero_contract, 393, s2489_zero_checked⟩

def s2489_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s2489_positive_checked : check 399 s2489_positive_contract = true := by decide +kernel
def s2489_positive : CertifiedContract :=
  ⟨2489, 2490, 1, (.dec 0), s2489_positive_contract, 399, s2489_positive_checked⟩

def s2490_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2490_plain_checked : check 409 s2490_plain_contract = true := by decide +kernel
def s2490_plain : CertifiedContract :=
  ⟨2490, 2491, 0, (.inc 5), s2490_plain_contract, 409, s2490_plain_checked⟩

def s2491_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2491_zero_checked : check 435 s2491_zero_contract = true := by decide +kernel
def s2491_zero : CertifiedContract :=
  ⟨2491, 2493, 0, .none, s2491_zero_contract, 435, s2491_zero_checked⟩

def s2491_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2491_positive_checked : check 441 s2491_positive_contract = true := by decide +kernel
def s2491_positive : CertifiedContract :=
  ⟨2491, 2492, 1, (.dec 8), s2491_positive_contract, 441, s2491_positive_checked⟩

def s2492_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s2492_plain_checked : check 122 s2492_plain_contract = true := by decide +kernel
def s2492_plain : CertifiedContract :=
  ⟨2492, 2496, 0, .none, s2492_plain_contract, 122, s2492_plain_checked⟩

def s2493_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s2493_zero_checked : check 447 s2493_zero_contract = true := by decide +kernel
def s2493_zero : CertifiedContract :=
  ⟨2493, 2496, 0, .none, s2493_zero_contract, 447, s2493_zero_checked⟩

def s2493_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2493_positive_checked : check 450 s2493_positive_contract = true := by decide +kernel
def s2493_positive : CertifiedContract :=
  ⟨2493, 2494, 1, (.dec 5), s2493_positive_contract, 450, s2493_positive_checked⟩

def s2494_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2494_plain_checked : check 454 s2494_plain_contract = true := by decide +kernel
def s2494_plain : CertifiedContract :=
  ⟨2494, 2495, 0, (.inc 8), s2494_plain_contract, 454, s2494_plain_checked⟩

def s2495_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2495_plain_checked : check 125 s2495_plain_contract = true := by decide +kernel
def s2495_plain : CertifiedContract :=
  ⟨2495, 2493, 0, .none, s2495_plain_contract, 125, s2495_plain_checked⟩

def s2496_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s2496_plain_checked : check 116 s2496_plain_contract = true := by decide +kernel
def s2496_plain : CertifiedContract :=
  ⟨2496, 2489, 0, .none, s2496_plain_contract, 116, s2496_plain_checked⟩

def s2497_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2497_zero_checked : check 393 s2497_zero_contract = true := by decide +kernel
def s2497_zero : CertifiedContract :=
  ⟨2497, 2500, 0, .none, s2497_zero_contract, 393, s2497_zero_checked⟩

def s2497_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s2497_positive_checked : check 396 s2497_positive_contract = true := by decide +kernel
def s2497_positive : CertifiedContract :=
  ⟨2497, 2498, 1, (.dec 5), s2497_positive_contract, 396, s2497_positive_checked⟩

def s2498_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s2498_plain_checked : check 409 s2498_plain_contract = true := by decide +kernel
def s2498_plain : CertifiedContract :=
  ⟨2498, 2499, 0, (.inc 0), s2498_plain_contract, 409, s2498_plain_checked⟩

def s2499_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s2499_plain_checked : check 110 s2499_plain_contract = true := by decide +kernel
def s2499_plain : CertifiedContract :=
  ⟨2499, 2497, 0, .none, s2499_plain_contract, 110, s2499_plain_checked⟩

def s2500_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s2500_zero_checked : check 390 s2500_zero_contract = true := by decide +kernel
def s2500_zero : CertifiedContract :=
  ⟨2500, 2504, 0, .none, s2500_zero_contract, 390, s2500_zero_checked⟩

def s2500_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2500_positive_checked : check 396 s2500_positive_contract = true := by decide +kernel
def s2500_positive : CertifiedContract :=
  ⟨2500, 2501, 1, (.dec 2), s2500_positive_contract, 396, s2500_positive_checked⟩

def s2501_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2501_plain_checked : check 409 s2501_plain_contract = true := by decide +kernel
def s2501_plain : CertifiedContract :=
  ⟨2501, 2502, 0, (.inc 5), s2501_plain_contract, 409, s2501_plain_checked⟩

def s2502_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2502_plain_checked : check 436 s2502_plain_contract = true := by decide +kernel
def s2502_plain : CertifiedContract :=
  ⟨2502, 2503, 0, (.inc 8), s2502_plain_contract, 436, s2502_plain_checked⟩

def s2503_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2503_plain_checked : check 119 s2503_plain_contract = true := by decide +kernel
def s2503_plain : CertifiedContract :=
  ⟨2503, 2500, 0, .none, s2503_plain_contract, 119, s2503_plain_checked⟩

def s2504_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s2504_zero_checked : check 411 s2504_zero_contract = true := by decide +kernel
def s2504_zero : CertifiedContract :=
  ⟨2504, 2510, 0, .none, s2504_zero_contract, 411, s2504_zero_checked⟩

def s2504_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2504_positive_checked : check 414 s2504_positive_contract = true := by decide +kernel
def s2504_positive : CertifiedContract :=
  ⟨2504, 2505, 1, (.dec 8), s2504_positive_contract, 414, s2504_positive_checked⟩

def s2505_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2505_plain_checked : check 409 s2505_plain_contract = true := by decide +kernel
def s2505_plain : CertifiedContract :=
  ⟨2505, 2506, 0, (.inc 5), s2505_plain_contract, 409, s2505_plain_checked⟩

def s2506_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s2506_zero_checked : check 429 s2506_zero_contract = true := by decide +kernel
def s2506_zero : CertifiedContract :=
  ⟨2506, 2509, 0, .none, s2506_zero_contract, 429, s2506_zero_checked⟩

def s2506_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2506_positive_checked : check 432 s2506_positive_contract = true := by decide +kernel
def s2506_positive : CertifiedContract :=
  ⟨2506, 2507, 1, (.dec 8), s2506_positive_contract, 432, s2506_positive_checked⟩

def s2507_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2507_plain_checked : check 427 s2507_plain_contract = true := by decide +kernel
def s2507_plain : CertifiedContract :=
  ⟨2507, 2508, 0, (.inc 2), s2507_plain_contract, 427, s2507_plain_checked⟩

def s2508_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2508_plain_checked : check 119 s2508_plain_contract = true := by decide +kernel
def s2508_plain : CertifiedContract :=
  ⟨2508, 2506, 0, .none, s2508_plain_contract, 119, s2508_plain_checked⟩

def s2509_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2509_plain_checked : check 122 s2509_plain_contract = true := by decide +kernel
def s2509_plain : CertifiedContract :=
  ⟨2509, 2500, 0, .none, s2509_plain_contract, 122, s2509_plain_checked⟩

def s2510_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, true, false] 0 .none⟩
theorem s2510_zero_checked : check 396 s2510_zero_contract = true := by decide +kernel
def s2510_zero : CertifiedContract :=
  ⟨2510, 2516, 0, .none, s2510_zero_contract, 396, s2510_zero_checked⟩

def s2510_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2510_positive_checked : check 396 s2510_positive_contract = true := by decide +kernel
def s2510_positive : CertifiedContract :=
  ⟨2510, 2511, 1, (.dec 5), s2510_positive_contract, 396, s2510_positive_checked⟩

def s2511_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2511_plain_checked : check 409 s2511_plain_contract = true := by decide +kernel
def s2511_plain : CertifiedContract :=
  ⟨2511, 2512, 0, (.inc 2), s2511_plain_contract, 409, s2511_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S050
