module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S052
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s2562_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2562_plain_checked : check 358 s2562_plain_contract = true := by decide +kernel
def s2562_plain : CertifiedContract :=
  ⟨2562, 2563, 0, (.inc 2), s2562_plain_contract, 358, s2562_plain_checked⟩

def s2563_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2563_plain_checked : check 364 s2563_plain_contract = true := by decide +kernel
def s2563_plain : CertifiedContract :=
  ⟨2563, 2564, 0, (.inc 2), s2563_plain_contract, 364, s2563_plain_checked⟩

def s2564_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s2564_plain_checked : check 370 s2564_plain_contract = true := by decide +kernel
def s2564_plain : CertifiedContract :=
  ⟨2564, 2565, 0, (.inc 2), s2564_plain_contract, 370, s2564_plain_checked⟩

def s2565_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false] 0 .none⟩
theorem s2565_plain_checked : check 89 s2565_plain_contract = true := by decide +kernel
def s2565_plain : CertifiedContract :=
  ⟨2565, 2560, 0, .none, s2565_plain_contract, 89, s2565_plain_checked⟩

def s2566_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s2566_zero_checked : check 348 s2566_zero_contract = true := by decide +kernel
def s2566_zero : CertifiedContract :=
  ⟨2566, 2574, 0, .none, s2566_zero_contract, 348, s2566_zero_checked⟩

def s2566_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s2566_positive_checked : check 354 s2566_positive_contract = true := by decide +kernel
def s2566_positive : CertifiedContract :=
  ⟨2566, 2567, 1, (.dec 0), s2566_positive_contract, 354, s2566_positive_checked⟩

def s2567_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2567_plain_checked : check 364 s2567_plain_contract = true := by decide +kernel
def s2567_plain : CertifiedContract :=
  ⟨2567, 2568, 0, (.inc 5), s2567_plain_contract, 364, s2567_plain_checked⟩

def s2568_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2568_zero_checked : check 390 s2568_zero_contract = true := by decide +kernel
def s2568_zero : CertifiedContract :=
  ⟨2568, 2570, 0, .none, s2568_zero_contract, 390, s2568_zero_checked⟩

def s2568_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2568_positive_checked : check 396 s2568_positive_contract = true := by decide +kernel
def s2568_positive : CertifiedContract :=
  ⟨2568, 2569, 1, (.dec 8), s2568_positive_contract, 396, s2568_positive_checked⟩

def s2569_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s2569_plain_checked : check 107 s2569_plain_contract = true := by decide +kernel
def s2569_plain : CertifiedContract :=
  ⟨2569, 2573, 0, .none, s2569_plain_contract, 107, s2569_plain_checked⟩

def s2570_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s2570_zero_checked : check 402 s2570_zero_contract = true := by decide +kernel
def s2570_zero : CertifiedContract :=
  ⟨2570, 2573, 0, .none, s2570_zero_contract, 402, s2570_zero_checked⟩

def s2570_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2570_positive_checked : check 405 s2570_positive_contract = true := by decide +kernel
def s2570_positive : CertifiedContract :=
  ⟨2570, 2571, 1, (.dec 5), s2570_positive_contract, 405, s2570_positive_checked⟩

def s2571_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2571_plain_checked : check 409 s2571_plain_contract = true := by decide +kernel
def s2571_plain : CertifiedContract :=
  ⟨2571, 2572, 0, (.inc 8), s2571_plain_contract, 409, s2571_plain_checked⟩

def s2572_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2572_plain_checked : check 110 s2572_plain_contract = true := by decide +kernel
def s2572_plain : CertifiedContract :=
  ⟨2572, 2570, 0, .none, s2572_plain_contract, 110, s2572_plain_checked⟩

def s2573_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s2573_plain_checked : check 101 s2573_plain_contract = true := by decide +kernel
def s2573_plain : CertifiedContract :=
  ⟨2573, 2566, 0, .none, s2573_plain_contract, 101, s2573_plain_checked⟩

def s2574_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2574_zero_checked : check 348 s2574_zero_contract = true := by decide +kernel
def s2574_zero : CertifiedContract :=
  ⟨2574, 2577, 0, .none, s2574_zero_contract, 348, s2574_zero_checked⟩

def s2574_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s2574_positive_checked : check 351 s2574_positive_contract = true := by decide +kernel
def s2574_positive : CertifiedContract :=
  ⟨2574, 2575, 1, (.dec 5), s2574_positive_contract, 351, s2574_positive_checked⟩

def s2575_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s2575_plain_checked : check 364 s2575_plain_contract = true := by decide +kernel
def s2575_plain : CertifiedContract :=
  ⟨2575, 2576, 0, (.inc 0), s2575_plain_contract, 364, s2575_plain_checked⟩

def s2576_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s2576_plain_checked : check 95 s2576_plain_contract = true := by decide +kernel
def s2576_plain : CertifiedContract :=
  ⟨2576, 2574, 0, .none, s2576_plain_contract, 95, s2576_plain_checked⟩

def s2577_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s2577_zero_checked : check 345 s2577_zero_contract = true := by decide +kernel
def s2577_zero : CertifiedContract :=
  ⟨2577, 2581, 0, .none, s2577_zero_contract, 345, s2577_zero_checked⟩

def s2577_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2577_positive_checked : check 351 s2577_positive_contract = true := by decide +kernel
def s2577_positive : CertifiedContract :=
  ⟨2577, 2578, 1, (.dec 2), s2577_positive_contract, 351, s2577_positive_checked⟩

def s2578_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2578_plain_checked : check 364 s2578_plain_contract = true := by decide +kernel
def s2578_plain : CertifiedContract :=
  ⟨2578, 2579, 0, (.inc 5), s2578_plain_contract, 364, s2578_plain_checked⟩

def s2579_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2579_plain_checked : check 391 s2579_plain_contract = true := by decide +kernel
def s2579_plain : CertifiedContract :=
  ⟨2579, 2580, 0, (.inc 8), s2579_plain_contract, 391, s2579_plain_checked⟩

def s2580_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2580_plain_checked : check 104 s2580_plain_contract = true := by decide +kernel
def s2580_plain : CertifiedContract :=
  ⟨2580, 2577, 0, .none, s2580_plain_contract, 104, s2580_plain_checked⟩

def s2581_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s2581_zero_checked : check 366 s2581_zero_contract = true := by decide +kernel
def s2581_zero : CertifiedContract :=
  ⟨2581, 2587, 0, .none, s2581_zero_contract, 366, s2581_zero_checked⟩

def s2581_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2581_positive_checked : check 369 s2581_positive_contract = true := by decide +kernel
def s2581_positive : CertifiedContract :=
  ⟨2581, 2582, 1, (.dec 8), s2581_positive_contract, 369, s2581_positive_checked⟩

def s2582_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2582_plain_checked : check 364 s2582_plain_contract = true := by decide +kernel
def s2582_plain : CertifiedContract :=
  ⟨2582, 2583, 0, (.inc 5), s2582_plain_contract, 364, s2582_plain_checked⟩

def s2583_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s2583_zero_checked : check 384 s2583_zero_contract = true := by decide +kernel
def s2583_zero : CertifiedContract :=
  ⟨2583, 2586, 0, .none, s2583_zero_contract, 384, s2583_zero_checked⟩

def s2583_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2583_positive_checked : check 387 s2583_positive_contract = true := by decide +kernel
def s2583_positive : CertifiedContract :=
  ⟨2583, 2584, 1, (.dec 8), s2583_positive_contract, 387, s2583_positive_checked⟩

def s2584_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2584_plain_checked : check 382 s2584_plain_contract = true := by decide +kernel
def s2584_plain : CertifiedContract :=
  ⟨2584, 2585, 0, (.inc 2), s2584_plain_contract, 382, s2584_plain_checked⟩

def s2585_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2585_plain_checked : check 104 s2585_plain_contract = true := by decide +kernel
def s2585_plain : CertifiedContract :=
  ⟨2585, 2583, 0, .none, s2585_plain_contract, 104, s2585_plain_checked⟩

def s2586_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2586_plain_checked : check 107 s2586_plain_contract = true := by decide +kernel
def s2586_plain : CertifiedContract :=
  ⟨2586, 2577, 0, .none, s2586_plain_contract, 107, s2586_plain_checked⟩

def s2587_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, true, false] 0 .none⟩
theorem s2587_zero_checked : check 351 s2587_zero_contract = true := by decide +kernel
def s2587_zero : CertifiedContract :=
  ⟨2587, 2593, 0, .none, s2587_zero_contract, 351, s2587_zero_checked⟩

def s2587_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2587_positive_checked : check 351 s2587_positive_contract = true := by decide +kernel
def s2587_positive : CertifiedContract :=
  ⟨2587, 2588, 1, (.dec 5), s2587_positive_contract, 351, s2587_positive_checked⟩

def s2588_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2588_plain_checked : check 364 s2588_plain_contract = true := by decide +kernel
def s2588_plain : CertifiedContract :=
  ⟨2588, 2589, 0, (.inc 2), s2588_plain_contract, 364, s2588_plain_checked⟩

def s2589_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2589_plain_checked : check 367 s2589_plain_contract = true := by decide +kernel
def s2589_plain : CertifiedContract :=
  ⟨2589, 2590, 0, (.inc 2), s2589_plain_contract, 367, s2589_plain_checked⟩

def s2590_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2590_plain_checked : check 373 s2590_plain_contract = true := by decide +kernel
def s2590_plain : CertifiedContract :=
  ⟨2590, 2591, 0, (.inc 2), s2590_plain_contract, 373, s2590_plain_checked⟩

def s2591_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s2591_plain_checked : check 379 s2591_plain_contract = true := by decide +kernel
def s2591_plain : CertifiedContract :=
  ⟨2591, 2592, 0, (.inc 2), s2591_plain_contract, 379, s2591_plain_checked⟩

def s2592_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s2592_plain_checked : check 92 s2592_plain_contract = true := by decide +kernel
def s2592_plain : CertifiedContract :=
  ⟨2592, 2587, 0, .none, s2592_plain_contract, 92, s2592_plain_checked⟩

def s2593_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2593_plain_checked : check 319 s2593_plain_contract = true := by decide +kernel
def s2593_plain : CertifiedContract :=
  ⟨2593, 2594, 0, (.inc 2), s2593_plain_contract, 319, s2593_plain_checked⟩

def s2594_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, false, false] 0 (.inc 2)⟩
theorem s2594_plain_checked : check 328 s2594_plain_contract = true := by decide +kernel
def s2594_plain : CertifiedContract :=
  ⟨2594, 2595, 0, (.inc 2), s2594_plain_contract, 328, s2594_plain_checked⟩

def s2595_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s2595_zero_checked : check 327 s2595_zero_contract = true := by decide +kernel
def s2595_zero : CertifiedContract :=
  ⟨2595, 2598, 0, .none, s2595_zero_contract, 327, s2595_zero_checked⟩

def s2595_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, false, true, false] 1 (.dec 2)⟩
theorem s2595_positive_checked : check 333 s2595_positive_contract = true := by decide +kernel
def s2595_positive : CertifiedContract :=
  ⟨2595, 2596, 1, (.dec 2), s2595_positive_contract, 333, s2595_positive_checked⟩

def s2596_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, false, true, true] 0 (.inc 8)⟩
theorem s2596_plain_checked : check 346 s2596_plain_contract = true := by decide +kernel
def s2596_plain : CertifiedContract :=
  ⟨2596, 2597, 0, (.inc 8), s2596_plain_contract, 346, s2596_plain_checked⟩

def s2597_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, false, false] 0 .none⟩
theorem s2597_plain_checked : check 89 s2597_plain_contract = true := by decide +kernel
def s2597_plain : CertifiedContract :=
  ⟨2597, 2595, 0, .none, s2597_plain_contract, 89, s2597_plain_checked⟩

def s2598_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s2598_zero_checked : check 348 s2598_zero_contract = true := by decide +kernel
def s2598_zero : CertifiedContract :=
  ⟨2598, 2601, 0, .none, s2598_zero_contract, 348, s2598_zero_checked⟩

def s2598_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2598_positive_checked : check 354 s2598_positive_contract = true := by decide +kernel
def s2598_positive : CertifiedContract :=
  ⟨2598, 2599, 1, (.dec 0), s2598_positive_contract, 354, s2598_positive_checked⟩

def s2599_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2599_plain_checked : check 346 s2599_plain_contract = true := by decide +kernel
def s2599_plain : CertifiedContract :=
  ⟨2599, 2600, 0, (.inc 2), s2599_plain_contract, 346, s2599_plain_checked⟩

def s2600_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, false, false] 0 .none⟩
theorem s2600_plain_checked : check 92 s2600_plain_contract = true := by decide +kernel
def s2600_plain : CertifiedContract :=
  ⟨2600, 2598, 0, .none, s2600_plain_contract, 92, s2600_plain_checked⟩

def s2601_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s2601_zero_checked : check 354 s2601_zero_contract = true := by decide +kernel
def s2601_zero : CertifiedContract :=
  ⟨2601, 2605, 0, .none, s2601_zero_contract, 354, s2601_zero_checked⟩

def s2601_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2601_positive_checked : check 360 s2601_positive_contract = true := by decide +kernel
def s2601_positive : CertifiedContract :=
  ⟨2601, 2602, 1, (.dec 2), s2601_positive_contract, 360, s2601_positive_checked⟩

def s2602_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2602_plain_checked : check 373 s2602_plain_contract = true := by decide +kernel
def s2602_plain : CertifiedContract :=
  ⟨2602, 2603, 0, (.inc 5), s2602_plain_contract, 373, s2602_plain_checked⟩

def s2603_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2603_plain_checked : check 400 s2603_plain_contract = true := by decide +kernel
def s2603_plain : CertifiedContract :=
  ⟨2603, 2604, 0, (.inc 8), s2603_plain_contract, 400, s2603_plain_checked⟩

def s2604_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s2604_plain_checked : check 107 s2604_plain_contract = true := by decide +kernel
def s2604_plain : CertifiedContract :=
  ⟨2604, 2601, 0, .none, s2604_plain_contract, 107, s2604_plain_checked⟩

def s2605_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s2605_zero_checked : check 375 s2605_zero_contract = true := by decide +kernel
def s2605_zero : CertifiedContract :=
  ⟨2605, 2611, 0, .none, s2605_zero_contract, 375, s2605_zero_checked⟩

def s2605_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2605_positive_checked : check 378 s2605_positive_contract = true := by decide +kernel
def s2605_positive : CertifiedContract :=
  ⟨2605, 2606, 1, (.dec 8), s2605_positive_contract, 378, s2605_positive_checked⟩

def s2606_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2606_plain_checked : check 373 s2606_plain_contract = true := by decide +kernel
def s2606_plain : CertifiedContract :=
  ⟨2606, 2607, 0, (.inc 5), s2606_plain_contract, 373, s2606_plain_checked⟩

def s2607_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s2607_zero_checked : check 393 s2607_zero_contract = true := by decide +kernel
def s2607_zero : CertifiedContract :=
  ⟨2607, 2610, 0, .none, s2607_zero_contract, 393, s2607_zero_checked⟩

def s2607_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2607_positive_checked : check 396 s2607_positive_contract = true := by decide +kernel
def s2607_positive : CertifiedContract :=
  ⟨2607, 2608, 1, (.dec 8), s2607_positive_contract, 396, s2607_positive_checked⟩

def s2608_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2608_plain_checked : check 391 s2608_plain_contract = true := by decide +kernel
def s2608_plain : CertifiedContract :=
  ⟨2608, 2609, 0, (.inc 2), s2608_plain_contract, 391, s2608_plain_checked⟩

def s2609_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2609_plain_checked : check 107 s2609_plain_contract = true := by decide +kernel
def s2609_plain : CertifiedContract :=
  ⟨2609, 2607, 0, .none, s2609_plain_contract, 107, s2609_plain_checked⟩

def s2610_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s2610_plain_checked : check 110 s2610_plain_contract = true := by decide +kernel
def s2610_plain : CertifiedContract :=
  ⟨2610, 2601, 0, .none, s2610_plain_contract, 110, s2610_plain_checked⟩

def s2611_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, true] 0 .none⟩
theorem s2611_zero_checked : check 363 s2611_zero_contract = true := by decide +kernel
def s2611_zero : CertifiedContract :=
  ⟨2611, 2614, 0, .none, s2611_zero_contract, 363, s2611_zero_checked⟩

def s2611_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2611_positive_checked : check 360 s2611_positive_contract = true := by decide +kernel
def s2611_positive : CertifiedContract :=
  ⟨2611, 2612, 1, (.dec 5), s2611_positive_contract, 360, s2611_positive_checked⟩

end PA211.UserCandidate.RuntimeShards.S052
