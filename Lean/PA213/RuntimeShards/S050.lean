module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S050
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s2463_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2463_positive_checked : check 395 s2463_positive_contract = true := by decide +kernel
def s2463_positive : CertifiedContract :=
  ⟨2463, 2464, 1, (.dec 2), s2463_positive_contract, 395, s2463_positive_checked⟩

def s2464_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s2464_plain_checked : check 408 s2464_plain_contract = true := by decide +kernel
def s2464_plain : CertifiedContract :=
  ⟨2464, 2465, 0, (.inc 8), s2464_plain_contract, 408, s2464_plain_checked⟩

def s2465_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s2465_plain_checked : check 109 s2465_plain_contract = true := by decide +kernel
def s2465_plain : CertifiedContract :=
  ⟨2465, 2463, 0, .none, s2465_plain_contract, 109, s2465_plain_checked⟩

def s2466_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2466_zero_checked : check 410 s2466_zero_contract = true := by decide +kernel
def s2466_zero : CertifiedContract :=
  ⟨2466, 2469, 0, .none, s2466_zero_contract, 410, s2466_zero_checked⟩

def s2466_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2466_positive_checked : check 416 s2466_positive_contract = true := by decide +kernel
def s2466_positive : CertifiedContract :=
  ⟨2466, 2467, 1, (.dec 0), s2466_positive_contract, 416, s2466_positive_checked⟩

def s2467_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2467_plain_checked : check 408 s2467_plain_contract = true := by decide +kernel
def s2467_plain : CertifiedContract :=
  ⟨2467, 2468, 0, (.inc 2), s2467_plain_contract, 408, s2467_plain_checked⟩

def s2468_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s2468_plain_checked : check 112 s2468_plain_contract = true := by decide +kernel
def s2468_plain : CertifiedContract :=
  ⟨2468, 2466, 0, .none, s2468_plain_contract, 112, s2468_plain_checked⟩

def s2469_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2469_zero_checked : check 416 s2469_zero_contract = true := by decide +kernel
def s2469_zero : CertifiedContract :=
  ⟨2469, 2473, 0, .none, s2469_zero_contract, 416, s2469_zero_checked⟩

def s2469_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2469_positive_checked : check 422 s2469_positive_contract = true := by decide +kernel
def s2469_positive : CertifiedContract :=
  ⟨2469, 2470, 1, (.dec 2), s2469_positive_contract, 422, s2469_positive_checked⟩

def s2470_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2470_plain_checked : check 435 s2470_plain_contract = true := by decide +kernel
def s2470_plain : CertifiedContract :=
  ⟨2470, 2471, 0, (.inc 5), s2470_plain_contract, 435, s2470_plain_checked⟩

def s2471_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2471_plain_checked : check 462 s2471_plain_contract = true := by decide +kernel
def s2471_plain : CertifiedContract :=
  ⟨2471, 2472, 0, (.inc 8), s2471_plain_contract, 462, s2471_plain_checked⟩

def s2472_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2472_plain_checked : check 127 s2472_plain_contract = true := by decide +kernel
def s2472_plain : CertifiedContract :=
  ⟨2472, 2469, 0, .none, s2472_plain_contract, 127, s2472_plain_checked⟩

def s2473_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s2473_zero_checked : check 437 s2473_zero_contract = true := by decide +kernel
def s2473_zero : CertifiedContract :=
  ⟨2473, 2479, 0, .none, s2473_zero_contract, 437, s2473_zero_checked⟩

def s2473_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2473_positive_checked : check 440 s2473_positive_contract = true := by decide +kernel
def s2473_positive : CertifiedContract :=
  ⟨2473, 2474, 1, (.dec 8), s2473_positive_contract, 440, s2473_positive_checked⟩

def s2474_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2474_plain_checked : check 435 s2474_plain_contract = true := by decide +kernel
def s2474_plain : CertifiedContract :=
  ⟨2474, 2475, 0, (.inc 5), s2474_plain_contract, 435, s2474_plain_checked⟩

def s2475_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s2475_zero_checked : check 455 s2475_zero_contract = true := by decide +kernel
def s2475_zero : CertifiedContract :=
  ⟨2475, 2478, 0, .none, s2475_zero_contract, 455, s2475_zero_checked⟩

def s2475_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2475_positive_checked : check 458 s2475_positive_contract = true := by decide +kernel
def s2475_positive : CertifiedContract :=
  ⟨2475, 2476, 1, (.dec 8), s2475_positive_contract, 458, s2475_positive_checked⟩

def s2476_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2476_plain_checked : check 453 s2476_plain_contract = true := by decide +kernel
def s2476_plain : CertifiedContract :=
  ⟨2476, 2477, 0, (.inc 2), s2476_plain_contract, 453, s2476_plain_checked⟩

def s2477_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2477_plain_checked : check 127 s2477_plain_contract = true := by decide +kernel
def s2477_plain : CertifiedContract :=
  ⟨2477, 2475, 0, .none, s2477_plain_contract, 127, s2477_plain_checked⟩

def s2478_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2478_plain_checked : check 130 s2478_plain_contract = true := by decide +kernel
def s2478_plain : CertifiedContract :=
  ⟨2478, 2469, 0, .none, s2478_plain_contract, 130, s2478_plain_checked⟩

def s2479_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s2479_zero_checked : check 425 s2479_zero_contract = true := by decide +kernel
def s2479_zero : CertifiedContract :=
  ⟨2479, 2482, 0, .none, s2479_zero_contract, 425, s2479_zero_checked⟩

def s2479_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2479_positive_checked : check 422 s2479_positive_contract = true := by decide +kernel
def s2479_positive : CertifiedContract :=
  ⟨2479, 2480, 1, (.dec 5), s2479_positive_contract, 422, s2479_positive_checked⟩

def s2480_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2480_plain_checked : check 435 s2480_plain_contract = true := by decide +kernel
def s2480_plain : CertifiedContract :=
  ⟨2480, 2481, 0, (.inc 0), s2480_plain_contract, 435, s2480_plain_checked⟩

def s2481_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s2481_plain_checked : check 118 s2481_plain_contract = true := by decide +kernel
def s2481_plain : CertifiedContract :=
  ⟨2481, 2479, 0, .none, s2481_plain_contract, 118, s2481_plain_checked⟩

def s2482_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s2482_zero_checked : check 389 s2482_zero_contract = true := by decide +kernel
def s2482_zero : CertifiedContract :=
  ⟨2482, 2486, 0, .none, s2482_zero_contract, 389, s2482_zero_checked⟩

def s2482_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s2482_positive_checked : check 395 s2482_positive_contract = true := by decide +kernel
def s2482_positive : CertifiedContract :=
  ⟨2482, 2483, 1, (.dec 7), s2482_positive_contract, 395, s2482_positive_checked⟩

def s2483_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2483_plain_checked : check 399 s2483_plain_contract = true := by decide +kernel
def s2483_plain : CertifiedContract :=
  ⟨2483, 2484, 0, (.inc 2), s2483_plain_contract, 399, s2483_plain_checked⟩

def s2484_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2484_plain_checked : check 426 s2484_plain_contract = true := by decide +kernel
def s2484_plain : CertifiedContract :=
  ⟨2484, 2485, 0, (.inc 8), s2484_plain_contract, 426, s2484_plain_checked⟩

def s2485_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s2485_plain_checked : check 115 s2485_plain_contract = true := by decide +kernel
def s2485_plain : CertifiedContract :=
  ⟨2485, 2482, 0, .none, s2485_plain_contract, 115, s2485_plain_checked⟩

def s2486_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s2486_zero_checked : check 398 s2486_zero_contract = true := by decide +kernel
def s2486_zero : CertifiedContract :=
  ⟨2486, 2489, 0, .none, s2486_zero_contract, 398, s2486_zero_checked⟩

def s2486_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s2486_positive_checked : check 395 s2486_positive_contract = true := by decide +kernel
def s2486_positive : CertifiedContract :=
  ⟨2486, 2487, 1, (.dec 8), s2486_positive_contract, 395, s2486_positive_checked⟩

def s2487_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s2487_plain_checked : check 426 s2487_plain_contract = true := by decide +kernel
def s2487_plain : CertifiedContract :=
  ⟨2487, 2488, 0, (.inc 7), s2487_plain_contract, 426, s2487_plain_checked⟩

def s2488_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s2488_plain_checked : check 109 s2488_plain_contract = true := by decide +kernel
def s2488_plain : CertifiedContract :=
  ⟨2488, 2486, 0, .none, s2488_plain_contract, 109, s2488_plain_checked⟩

def s2489_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s2489_zero_checked : check 392 s2489_zero_contract = true := by decide +kernel
def s2489_zero : CertifiedContract :=
  ⟨2489, 2497, 0, .none, s2489_zero_contract, 392, s2489_zero_checked⟩

def s2489_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s2489_positive_checked : check 398 s2489_positive_contract = true := by decide +kernel
def s2489_positive : CertifiedContract :=
  ⟨2489, 2490, 1, (.dec 0), s2489_positive_contract, 398, s2489_positive_checked⟩

def s2490_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2490_plain_checked : check 408 s2490_plain_contract = true := by decide +kernel
def s2490_plain : CertifiedContract :=
  ⟨2490, 2491, 0, (.inc 5), s2490_plain_contract, 408, s2490_plain_checked⟩

def s2491_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2491_zero_checked : check 434 s2491_zero_contract = true := by decide +kernel
def s2491_zero : CertifiedContract :=
  ⟨2491, 2493, 0, .none, s2491_zero_contract, 434, s2491_zero_checked⟩

def s2491_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2491_positive_checked : check 440 s2491_positive_contract = true := by decide +kernel
def s2491_positive : CertifiedContract :=
  ⟨2491, 2492, 1, (.dec 8), s2491_positive_contract, 440, s2491_positive_checked⟩

def s2492_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s2492_plain_checked : check 121 s2492_plain_contract = true := by decide +kernel
def s2492_plain : CertifiedContract :=
  ⟨2492, 2496, 0, .none, s2492_plain_contract, 121, s2492_plain_checked⟩

def s2493_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s2493_zero_checked : check 446 s2493_zero_contract = true := by decide +kernel
def s2493_zero : CertifiedContract :=
  ⟨2493, 2496, 0, .none, s2493_zero_contract, 446, s2493_zero_checked⟩

def s2493_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2493_positive_checked : check 449 s2493_positive_contract = true := by decide +kernel
def s2493_positive : CertifiedContract :=
  ⟨2493, 2494, 1, (.dec 5), s2493_positive_contract, 449, s2493_positive_checked⟩

def s2494_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2494_plain_checked : check 453 s2494_plain_contract = true := by decide +kernel
def s2494_plain : CertifiedContract :=
  ⟨2494, 2495, 0, (.inc 8), s2494_plain_contract, 453, s2494_plain_checked⟩

def s2495_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2495_plain_checked : check 124 s2495_plain_contract = true := by decide +kernel
def s2495_plain : CertifiedContract :=
  ⟨2495, 2493, 0, .none, s2495_plain_contract, 124, s2495_plain_checked⟩

def s2496_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s2496_plain_checked : check 115 s2496_plain_contract = true := by decide +kernel
def s2496_plain : CertifiedContract :=
  ⟨2496, 2489, 0, .none, s2496_plain_contract, 115, s2496_plain_checked⟩

def s2497_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2497_zero_checked : check 392 s2497_zero_contract = true := by decide +kernel
def s2497_zero : CertifiedContract :=
  ⟨2497, 2500, 0, .none, s2497_zero_contract, 392, s2497_zero_checked⟩

def s2497_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s2497_positive_checked : check 395 s2497_positive_contract = true := by decide +kernel
def s2497_positive : CertifiedContract :=
  ⟨2497, 2498, 1, (.dec 5), s2497_positive_contract, 395, s2497_positive_checked⟩

def s2498_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s2498_plain_checked : check 408 s2498_plain_contract = true := by decide +kernel
def s2498_plain : CertifiedContract :=
  ⟨2498, 2499, 0, (.inc 0), s2498_plain_contract, 408, s2498_plain_checked⟩

def s2499_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s2499_plain_checked : check 109 s2499_plain_contract = true := by decide +kernel
def s2499_plain : CertifiedContract :=
  ⟨2499, 2497, 0, .none, s2499_plain_contract, 109, s2499_plain_checked⟩

def s2500_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s2500_zero_checked : check 389 s2500_zero_contract = true := by decide +kernel
def s2500_zero : CertifiedContract :=
  ⟨2500, 2504, 0, .none, s2500_zero_contract, 389, s2500_zero_checked⟩

def s2500_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2500_positive_checked : check 395 s2500_positive_contract = true := by decide +kernel
def s2500_positive : CertifiedContract :=
  ⟨2500, 2501, 1, (.dec 2), s2500_positive_contract, 395, s2500_positive_checked⟩

def s2501_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2501_plain_checked : check 408 s2501_plain_contract = true := by decide +kernel
def s2501_plain : CertifiedContract :=
  ⟨2501, 2502, 0, (.inc 5), s2501_plain_contract, 408, s2501_plain_checked⟩

def s2502_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2502_plain_checked : check 435 s2502_plain_contract = true := by decide +kernel
def s2502_plain : CertifiedContract :=
  ⟨2502, 2503, 0, (.inc 8), s2502_plain_contract, 435, s2502_plain_checked⟩

def s2503_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2503_plain_checked : check 118 s2503_plain_contract = true := by decide +kernel
def s2503_plain : CertifiedContract :=
  ⟨2503, 2500, 0, .none, s2503_plain_contract, 118, s2503_plain_checked⟩

def s2504_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s2504_zero_checked : check 410 s2504_zero_contract = true := by decide +kernel
def s2504_zero : CertifiedContract :=
  ⟨2504, 2510, 0, .none, s2504_zero_contract, 410, s2504_zero_checked⟩

def s2504_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2504_positive_checked : check 413 s2504_positive_contract = true := by decide +kernel
def s2504_positive : CertifiedContract :=
  ⟨2504, 2505, 1, (.dec 8), s2504_positive_contract, 413, s2504_positive_checked⟩

def s2505_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2505_plain_checked : check 408 s2505_plain_contract = true := by decide +kernel
def s2505_plain : CertifiedContract :=
  ⟨2505, 2506, 0, (.inc 5), s2505_plain_contract, 408, s2505_plain_checked⟩

def s2506_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s2506_zero_checked : check 428 s2506_zero_contract = true := by decide +kernel
def s2506_zero : CertifiedContract :=
  ⟨2506, 2509, 0, .none, s2506_zero_contract, 428, s2506_zero_checked⟩

def s2506_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2506_positive_checked : check 431 s2506_positive_contract = true := by decide +kernel
def s2506_positive : CertifiedContract :=
  ⟨2506, 2507, 1, (.dec 8), s2506_positive_contract, 431, s2506_positive_checked⟩

def s2507_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2507_plain_checked : check 426 s2507_plain_contract = true := by decide +kernel
def s2507_plain : CertifiedContract :=
  ⟨2507, 2508, 0, (.inc 2), s2507_plain_contract, 426, s2507_plain_checked⟩

def s2508_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2508_plain_checked : check 118 s2508_plain_contract = true := by decide +kernel
def s2508_plain : CertifiedContract :=
  ⟨2508, 2506, 0, .none, s2508_plain_contract, 118, s2508_plain_checked⟩

def s2509_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2509_plain_checked : check 121 s2509_plain_contract = true := by decide +kernel
def s2509_plain : CertifiedContract :=
  ⟨2509, 2500, 0, .none, s2509_plain_contract, 121, s2509_plain_checked⟩

def s2510_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, true, false] 0 .none⟩
theorem s2510_zero_checked : check 395 s2510_zero_contract = true := by decide +kernel
def s2510_zero : CertifiedContract :=
  ⟨2510, 2516, 0, .none, s2510_zero_contract, 395, s2510_zero_checked⟩

def s2510_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2510_positive_checked : check 395 s2510_positive_contract = true := by decide +kernel
def s2510_positive : CertifiedContract :=
  ⟨2510, 2511, 1, (.dec 5), s2510_positive_contract, 395, s2510_positive_checked⟩

def s2511_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2511_plain_checked : check 408 s2511_plain_contract = true := by decide +kernel
def s2511_plain : CertifiedContract :=
  ⟨2511, 2512, 0, (.inc 2), s2511_plain_contract, 408, s2511_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s2463_positive,
  s2464_plain,
  s2465_plain,
  s2466_zero,
  s2466_positive,
  s2467_plain,
  s2468_plain,
  s2469_zero,
  s2469_positive,
  s2470_plain,
  s2471_plain,
  s2472_plain,
  s2473_zero,
  s2473_positive,
  s2474_plain,
  s2475_zero,
  s2475_positive,
  s2476_plain,
  s2477_plain,
  s2478_plain,
  s2479_zero,
  s2479_positive,
  s2480_plain,
  s2481_plain,
  s2482_zero,
  s2482_positive,
  s2483_plain,
  s2484_plain,
  s2485_plain,
  s2486_zero,
  s2486_positive,
  s2487_plain,
  s2488_plain,
  s2489_zero,
  s2489_positive,
  s2490_plain,
  s2491_zero,
  s2491_positive,
  s2492_plain,
  s2493_zero,
  s2493_positive,
  s2494_plain,
  s2495_plain,
  s2496_plain,
  s2497_zero,
  s2497_positive,
  s2498_plain,
  s2499_plain,
  s2500_zero,
  s2500_positive,
  s2501_plain,
  s2502_plain,
  s2503_plain,
  s2504_zero,
  s2504_positive,
  s2505_plain,
  s2506_zero,
  s2506_positive,
  s2507_plain,
  s2508_plain,
  s2509_plain,
  s2510_zero,
  s2510_positive,
  s2511_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S050
