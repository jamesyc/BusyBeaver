module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S051
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s2512_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2512_plain_checked : check 411 s2512_plain_contract = true := by decide +kernel
def s2512_plain : CertifiedContract :=
  ⟨2512, 2513, 0, (.inc 2), s2512_plain_contract, 411, s2512_plain_checked⟩

def s2513_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2513_plain_checked : check 408 s2513_plain_contract = true := by decide +kernel
def s2513_plain : CertifiedContract :=
  ⟨2513, 2514, 0, (.inc 2), s2513_plain_contract, 408, s2513_plain_checked⟩

def s2514_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s2514_plain_checked : check 414 s2514_plain_contract = true := by decide +kernel
def s2514_plain : CertifiedContract :=
  ⟨2514, 2515, 0, (.inc 2), s2514_plain_contract, 414, s2514_plain_checked⟩

def s2515_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s2515_plain_checked : check 106 s2515_plain_contract = true := by decide +kernel
def s2515_plain : CertifiedContract :=
  ⟨2515, 2510, 0, .none, s2515_plain_contract, 106, s2515_plain_checked⟩

def s2516_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2516_plain_checked : check 363 s2516_plain_contract = true := by decide +kernel
def s2516_plain : CertifiedContract :=
  ⟨2516, 2517, 0, (.inc 2), s2516_plain_contract, 363, s2516_plain_checked⟩

def s2517_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, true] 0 (.inc 2)⟩
theorem s2517_plain_checked : check 372 s2517_plain_contract = true := by decide +kernel
def s2517_plain : CertifiedContract :=
  ⟨2517, 2518, 0, (.inc 2), s2517_plain_contract, 372, s2517_plain_checked⟩

def s2518_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, false, false] 0 (.inc 2)⟩
theorem s2518_plain_checked : check 345 s2518_plain_contract = true := by decide +kernel
def s2518_plain : CertifiedContract :=
  ⟨2518, 2519, 0, (.inc 2), s2518_plain_contract, 345, s2518_plain_checked⟩

def s2519_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, false, false] 0 .none⟩
theorem s2519_zero_checked : check 308 s2519_zero_contract = true := by decide +kernel
def s2519_zero : CertifiedContract :=
  ⟨2519, 2522, 0, .none, s2519_zero_contract, 308, s2519_zero_checked⟩

def s2519_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, false, true, false] 1 (.dec 2)⟩
theorem s2519_positive_checked : check 314 s2519_positive_contract = true := by decide +kernel
def s2519_positive : CertifiedContract :=
  ⟨2519, 2520, 1, (.dec 2), s2519_positive_contract, 314, s2519_positive_checked⟩

def s2520_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, false, true, true] 0 (.inc 8)⟩
theorem s2520_plain_checked : check 327 s2520_plain_contract = true := by decide +kernel
def s2520_plain : CertifiedContract :=
  ⟨2520, 2521, 0, (.inc 8), s2520_plain_contract, 327, s2520_plain_checked⟩

def s2521_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, false, false] 0 .none⟩
theorem s2521_plain_checked : check 82 s2521_plain_contract = true := by decide +kernel
def s2521_plain : CertifiedContract :=
  ⟨2521, 2519, 0, .none, s2521_plain_contract, 82, s2521_plain_checked⟩

def s2522_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s2522_zero_checked : check 329 s2522_zero_contract = true := by decide +kernel
def s2522_zero : CertifiedContract :=
  ⟨2522, 2525, 0, .none, s2522_zero_contract, 329, s2522_zero_checked⟩

def s2522_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2522_positive_checked : check 335 s2522_positive_contract = true := by decide +kernel
def s2522_positive : CertifiedContract :=
  ⟨2522, 2523, 1, (.dec 0), s2522_positive_contract, 335, s2522_positive_checked⟩

def s2523_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2523_plain_checked : check 327 s2523_plain_contract = true := by decide +kernel
def s2523_plain : CertifiedContract :=
  ⟨2523, 2524, 0, (.inc 2), s2523_plain_contract, 327, s2523_plain_checked⟩

def s2524_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, false, false] 0 .none⟩
theorem s2524_plain_checked : check 85 s2524_plain_contract = true := by decide +kernel
def s2524_plain : CertifiedContract :=
  ⟨2524, 2522, 0, .none, s2524_plain_contract, 85, s2524_plain_checked⟩

def s2525_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s2525_zero_checked : check 335 s2525_zero_contract = true := by decide +kernel
def s2525_zero : CertifiedContract :=
  ⟨2525, 2529, 0, .none, s2525_zero_contract, 335, s2525_zero_checked⟩

def s2525_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2525_positive_checked : check 341 s2525_positive_contract = true := by decide +kernel
def s2525_positive : CertifiedContract :=
  ⟨2525, 2526, 1, (.dec 2), s2525_positive_contract, 341, s2525_positive_checked⟩

def s2526_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2526_plain_checked : check 354 s2526_plain_contract = true := by decide +kernel
def s2526_plain : CertifiedContract :=
  ⟨2526, 2527, 0, (.inc 5), s2526_plain_contract, 354, s2526_plain_checked⟩

def s2527_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2527_plain_checked : check 381 s2527_plain_contract = true := by decide +kernel
def s2527_plain : CertifiedContract :=
  ⟨2527, 2528, 0, (.inc 8), s2527_plain_contract, 381, s2527_plain_checked⟩

def s2528_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s2528_plain_checked : check 100 s2528_plain_contract = true := by decide +kernel
def s2528_plain : CertifiedContract :=
  ⟨2528, 2525, 0, .none, s2528_plain_contract, 100, s2528_plain_checked⟩

def s2529_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s2529_zero_checked : check 356 s2529_zero_contract = true := by decide +kernel
def s2529_zero : CertifiedContract :=
  ⟨2529, 2535, 0, .none, s2529_zero_contract, 356, s2529_zero_checked⟩

def s2529_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2529_positive_checked : check 359 s2529_positive_contract = true := by decide +kernel
def s2529_positive : CertifiedContract :=
  ⟨2529, 2530, 1, (.dec 8), s2529_positive_contract, 359, s2529_positive_checked⟩

def s2530_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2530_plain_checked : check 354 s2530_plain_contract = true := by decide +kernel
def s2530_plain : CertifiedContract :=
  ⟨2530, 2531, 0, (.inc 5), s2530_plain_contract, 354, s2530_plain_checked⟩

def s2531_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s2531_zero_checked : check 374 s2531_zero_contract = true := by decide +kernel
def s2531_zero : CertifiedContract :=
  ⟨2531, 2534, 0, .none, s2531_zero_contract, 374, s2531_zero_checked⟩

def s2531_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2531_positive_checked : check 377 s2531_positive_contract = true := by decide +kernel
def s2531_positive : CertifiedContract :=
  ⟨2531, 2532, 1, (.dec 8), s2531_positive_contract, 377, s2531_positive_checked⟩

def s2532_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2532_plain_checked : check 372 s2532_plain_contract = true := by decide +kernel
def s2532_plain : CertifiedContract :=
  ⟨2532, 2533, 0, (.inc 2), s2532_plain_contract, 372, s2532_plain_checked⟩

def s2533_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2533_plain_checked : check 100 s2533_plain_contract = true := by decide +kernel
def s2533_plain : CertifiedContract :=
  ⟨2533, 2531, 0, .none, s2533_plain_contract, 100, s2533_plain_checked⟩

def s2534_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s2534_plain_checked : check 103 s2534_plain_contract = true := by decide +kernel
def s2534_plain : CertifiedContract :=
  ⟨2534, 2525, 0, .none, s2534_plain_contract, 103, s2534_plain_checked⟩

def s2535_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, true] 0 .none⟩
theorem s2535_zero_checked : check 344 s2535_zero_contract = true := by decide +kernel
def s2535_zero : CertifiedContract :=
  ⟨2535, 2538, 0, .none, s2535_zero_contract, 344, s2535_zero_checked⟩

def s2535_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2535_positive_checked : check 341 s2535_positive_contract = true := by decide +kernel
def s2535_positive : CertifiedContract :=
  ⟨2535, 2536, 1, (.dec 5), s2535_positive_contract, 341, s2535_positive_checked⟩

def s2536_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2536_plain_checked : check 354 s2536_plain_contract = true := by decide +kernel
def s2536_plain : CertifiedContract :=
  ⟨2536, 2537, 0, (.inc 0), s2536_plain_contract, 354, s2536_plain_checked⟩

def s2537_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s2537_plain_checked : check 91 s2537_plain_contract = true := by decide +kernel
def s2537_plain : CertifiedContract :=
  ⟨2537, 2535, 0, .none, s2537_plain_contract, 91, s2537_plain_checked⟩

def s2538_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, false] 0 (.inc 2)⟩
theorem s2538_plain_checked : check 294 s2538_plain_contract = true := by decide +kernel
def s2538_plain : CertifiedContract :=
  ⟨2538, 2539, 0, (.inc 2), s2538_plain_contract, 294, s2538_plain_checked⟩

def s2539_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, true, false] 0 .none⟩
theorem s2539_zero_checked : check 338 s2539_zero_contract = true := by decide +kernel
def s2539_zero : CertifiedContract :=
  ⟨2539, 2547, 0, .none, s2539_zero_contract, 338, s2539_zero_checked⟩

def s2539_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s2539_positive_checked : check 344 s2539_positive_contract = true := by decide +kernel
def s2539_positive : CertifiedContract :=
  ⟨2539, 2540, 1, (.dec 0), s2539_positive_contract, 344, s2539_positive_checked⟩

def s2540_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2540_plain_checked : check 354 s2540_plain_contract = true := by decide +kernel
def s2540_plain : CertifiedContract :=
  ⟨2540, 2541, 0, (.inc 5), s2540_plain_contract, 354, s2540_plain_checked⟩

def s2541_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2541_zero_checked : check 380 s2541_zero_contract = true := by decide +kernel
def s2541_zero : CertifiedContract :=
  ⟨2541, 2543, 0, .none, s2541_zero_contract, 380, s2541_zero_checked⟩

def s2541_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2541_positive_checked : check 386 s2541_positive_contract = true := by decide +kernel
def s2541_positive : CertifiedContract :=
  ⟨2541, 2542, 1, (.dec 8), s2541_positive_contract, 386, s2541_positive_checked⟩

def s2542_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s2542_plain_checked : check 103 s2542_plain_contract = true := by decide +kernel
def s2542_plain : CertifiedContract :=
  ⟨2542, 2546, 0, .none, s2542_plain_contract, 103, s2542_plain_checked⟩

def s2543_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s2543_zero_checked : check 392 s2543_zero_contract = true := by decide +kernel
def s2543_zero : CertifiedContract :=
  ⟨2543, 2546, 0, .none, s2543_zero_contract, 392, s2543_zero_checked⟩

def s2543_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2543_positive_checked : check 395 s2543_positive_contract = true := by decide +kernel
def s2543_positive : CertifiedContract :=
  ⟨2543, 2544, 1, (.dec 5), s2543_positive_contract, 395, s2543_positive_checked⟩

def s2544_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2544_plain_checked : check 399 s2544_plain_contract = true := by decide +kernel
def s2544_plain : CertifiedContract :=
  ⟨2544, 2545, 0, (.inc 8), s2544_plain_contract, 399, s2544_plain_checked⟩

def s2545_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2545_plain_checked : check 106 s2545_plain_contract = true := by decide +kernel
def s2545_plain : CertifiedContract :=
  ⟨2545, 2543, 0, .none, s2545_plain_contract, 106, s2545_plain_checked⟩

def s2546_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, false, false] 0 .none⟩
theorem s2546_plain_checked : check 97 s2546_plain_contract = true := by decide +kernel
def s2546_plain : CertifiedContract :=
  ⟨2546, 2539, 0, .none, s2546_plain_contract, 97, s2546_plain_checked⟩

def s2547_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s2547_zero_checked : check 338 s2547_zero_contract = true := by decide +kernel
def s2547_zero : CertifiedContract :=
  ⟨2547, 2550, 0, .none, s2547_zero_contract, 338, s2547_zero_checked⟩

def s2547_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s2547_positive_checked : check 341 s2547_positive_contract = true := by decide +kernel
def s2547_positive : CertifiedContract :=
  ⟨2547, 2548, 1, (.dec 5), s2547_positive_contract, 341, s2547_positive_checked⟩

def s2548_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s2548_plain_checked : check 354 s2548_plain_contract = true := by decide +kernel
def s2548_plain : CertifiedContract :=
  ⟨2548, 2549, 0, (.inc 0), s2548_plain_contract, 354, s2548_plain_checked⟩

def s2549_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false, true, false] 0 .none⟩
theorem s2549_plain_checked : check 91 s2549_plain_contract = true := by decide +kernel
def s2549_plain : CertifiedContract :=
  ⟨2549, 2547, 0, .none, s2549_plain_contract, 91, s2549_plain_checked⟩

def s2550_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, true, false] 0 .none⟩
theorem s2550_zero_checked : check 335 s2550_zero_contract = true := by decide +kernel
def s2550_zero : CertifiedContract :=
  ⟨2550, 2554, 0, .none, s2550_zero_contract, 335, s2550_zero_checked⟩

def s2550_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2550_positive_checked : check 341 s2550_positive_contract = true := by decide +kernel
def s2550_positive : CertifiedContract :=
  ⟨2550, 2551, 1, (.dec 2), s2550_positive_contract, 341, s2550_positive_checked⟩

def s2551_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2551_plain_checked : check 354 s2551_plain_contract = true := by decide +kernel
def s2551_plain : CertifiedContract :=
  ⟨2551, 2552, 0, (.inc 5), s2551_plain_contract, 354, s2551_plain_checked⟩

def s2552_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2552_plain_checked : check 381 s2552_plain_contract = true := by decide +kernel
def s2552_plain : CertifiedContract :=
  ⟨2552, 2553, 0, (.inc 8), s2552_plain_contract, 381, s2552_plain_checked⟩

def s2553_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s2553_plain_checked : check 100 s2553_plain_contract = true := by decide +kernel
def s2553_plain : CertifiedContract :=
  ⟨2553, 2550, 0, .none, s2553_plain_contract, 100, s2553_plain_checked⟩

def s2554_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false] 0 .none⟩
theorem s2554_zero_checked : check 356 s2554_zero_contract = true := by decide +kernel
def s2554_zero : CertifiedContract :=
  ⟨2554, 2560, 0, .none, s2554_zero_contract, 356, s2554_zero_checked⟩

def s2554_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2554_positive_checked : check 359 s2554_positive_contract = true := by decide +kernel
def s2554_positive : CertifiedContract :=
  ⟨2554, 2555, 1, (.dec 8), s2554_positive_contract, 359, s2554_positive_checked⟩

def s2555_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2555_plain_checked : check 354 s2555_plain_contract = true := by decide +kernel
def s2555_plain : CertifiedContract :=
  ⟨2555, 2556, 0, (.inc 5), s2555_plain_contract, 354, s2555_plain_checked⟩

def s2556_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, true, true, true] 0 .none⟩
theorem s2556_zero_checked : check 374 s2556_zero_contract = true := by decide +kernel
def s2556_zero : CertifiedContract :=
  ⟨2556, 2559, 0, .none, s2556_zero_contract, 374, s2556_zero_checked⟩

def s2556_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2556_positive_checked : check 377 s2556_positive_contract = true := by decide +kernel
def s2556_positive : CertifiedContract :=
  ⟨2556, 2557, 1, (.dec 8), s2556_positive_contract, 377, s2556_positive_checked⟩

def s2557_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2557_plain_checked : check 372 s2557_plain_contract = true := by decide +kernel
def s2557_plain : CertifiedContract :=
  ⟨2557, 2558, 0, (.inc 2), s2557_plain_contract, 372, s2557_plain_checked⟩

def s2558_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2558_plain_checked : check 100 s2558_plain_contract = true := by decide +kernel
def s2558_plain : CertifiedContract :=
  ⟨2558, 2556, 0, .none, s2558_plain_contract, 100, s2558_plain_checked⟩

def s2559_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s2559_plain_checked : check 103 s2559_plain_contract = true := by decide +kernel
def s2559_plain : CertifiedContract :=
  ⟨2559, 2550, 0, .none, s2559_plain_contract, 103, s2559_plain_checked⟩

def s2560_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s2560_zero_checked : check 341 s2560_zero_contract = true := by decide +kernel
def s2560_zero : CertifiedContract :=
  ⟨2560, 2566, 0, .none, s2560_zero_contract, 341, s2560_zero_checked⟩

def s2560_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2560_positive_checked : check 341 s2560_positive_contract = true := by decide +kernel
def s2560_positive : CertifiedContract :=
  ⟨2560, 2561, 1, (.dec 5), s2560_positive_contract, 341, s2560_positive_checked⟩

def s2561_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2561_plain_checked : check 354 s2561_plain_contract = true := by decide +kernel
def s2561_plain : CertifiedContract :=
  ⟨2561, 2562, 0, (.inc 2), s2561_plain_contract, 354, s2561_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s2512_plain,
  s2513_plain,
  s2514_plain,
  s2515_plain,
  s2516_plain,
  s2517_plain,
  s2518_plain,
  s2519_zero,
  s2519_positive,
  s2520_plain,
  s2521_plain,
  s2522_zero,
  s2522_positive,
  s2523_plain,
  s2524_plain,
  s2525_zero,
  s2525_positive,
  s2526_plain,
  s2527_plain,
  s2528_plain,
  s2529_zero,
  s2529_positive,
  s2530_plain,
  s2531_zero,
  s2531_positive,
  s2532_plain,
  s2533_plain,
  s2534_plain,
  s2535_zero,
  s2535_positive,
  s2536_plain,
  s2537_plain,
  s2538_plain,
  s2539_zero,
  s2539_positive,
  s2540_plain,
  s2541_zero,
  s2541_positive,
  s2542_plain,
  s2543_zero,
  s2543_positive,
  s2544_plain,
  s2545_plain,
  s2546_plain,
  s2547_zero,
  s2547_positive,
  s2548_plain,
  s2549_plain,
  s2550_zero,
  s2550_positive,
  s2551_plain,
  s2552_plain,
  s2553_plain,
  s2554_zero,
  s2554_positive,
  s2555_plain,
  s2556_zero,
  s2556_positive,
  s2557_plain,
  s2558_plain,
  s2559_plain,
  s2560_zero,
  s2560_positive,
  s2561_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S051
