module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S053
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s2612_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2612_plain_checked : check 372 s2612_plain_contract = true := by decide +kernel
def s2612_plain : CertifiedContract :=
  ⟨2612, 2613, 0, (.inc 0), s2612_plain_contract, 372, s2612_plain_checked⟩

def s2613_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s2613_plain_checked : check 97 s2613_plain_contract = true := by decide +kernel
def s2613_plain : CertifiedContract :=
  ⟨2613, 2611, 0, .none, s2613_plain_contract, 97, s2613_plain_checked⟩

def s2614_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, false] 0 (.inc 2)⟩
theorem s2614_plain_checked : check 312 s2614_plain_contract = true := by decide +kernel
def s2614_plain : CertifiedContract :=
  ⟨2614, 2615, 0, (.inc 2), s2614_plain_contract, 312, s2614_plain_checked⟩

def s2615_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, true, false] 0 .none⟩
theorem s2615_zero_checked : check 329 s2615_zero_contract = true := by decide +kernel
def s2615_zero : CertifiedContract :=
  ⟨2615, 2623, 0, .none, s2615_zero_contract, 329, s2615_zero_checked⟩

def s2615_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, false] 1 (.dec 0)⟩
theorem s2615_positive_checked : check 335 s2615_positive_contract = true := by decide +kernel
def s2615_positive : CertifiedContract :=
  ⟨2615, 2616, 1, (.dec 0), s2615_positive_contract, 335, s2615_positive_checked⟩

def s2616_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2616_plain_checked : check 345 s2616_plain_contract = true := by decide +kernel
def s2616_plain : CertifiedContract :=
  ⟨2616, 2617, 0, (.inc 5), s2616_plain_contract, 345, s2616_plain_checked⟩

def s2617_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s2617_zero_checked : check 371 s2617_zero_contract = true := by decide +kernel
def s2617_zero : CertifiedContract :=
  ⟨2617, 2619, 0, .none, s2617_zero_contract, 371, s2617_zero_checked⟩

def s2617_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2617_positive_checked : check 377 s2617_positive_contract = true := by decide +kernel
def s2617_positive : CertifiedContract :=
  ⟨2617, 2618, 1, (.dec 8), s2617_positive_contract, 377, s2617_positive_checked⟩

def s2618_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s2618_plain_checked : check 100 s2618_plain_contract = true := by decide +kernel
def s2618_plain : CertifiedContract :=
  ⟨2618, 2622, 0, .none, s2618_plain_contract, 100, s2618_plain_checked⟩

def s2619_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s2619_zero_checked : check 383 s2619_zero_contract = true := by decide +kernel
def s2619_zero : CertifiedContract :=
  ⟨2619, 2622, 0, .none, s2619_zero_contract, 383, s2619_zero_checked⟩

def s2619_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2619_positive_checked : check 386 s2619_positive_contract = true := by decide +kernel
def s2619_positive : CertifiedContract :=
  ⟨2619, 2620, 1, (.dec 5), s2619_positive_contract, 386, s2619_positive_checked⟩

def s2620_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2620_plain_checked : check 390 s2620_plain_contract = true := by decide +kernel
def s2620_plain : CertifiedContract :=
  ⟨2620, 2621, 0, (.inc 8), s2620_plain_contract, 390, s2620_plain_checked⟩

def s2621_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s2621_plain_checked : check 103 s2621_plain_contract = true := by decide +kernel
def s2621_plain : CertifiedContract :=
  ⟨2621, 2619, 0, .none, s2621_plain_contract, 103, s2621_plain_checked⟩

def s2622_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s2622_plain_checked : check 94 s2622_plain_contract = true := by decide +kernel
def s2622_plain : CertifiedContract :=
  ⟨2622, 2615, 0, .none, s2622_plain_contract, 94, s2622_plain_checked⟩

def s2623_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, false, false] 0 .none⟩
theorem s2623_zero_checked : check 329 s2623_zero_contract = true := by decide +kernel
def s2623_zero : CertifiedContract :=
  ⟨2623, 2626, 0, .none, s2623_zero_contract, 329, s2623_zero_checked⟩

def s2623_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2623_positive_checked : check 332 s2623_positive_contract = true := by decide +kernel
def s2623_positive : CertifiedContract :=
  ⟨2623, 2624, 1, (.dec 5), s2623_positive_contract, 332, s2623_positive_checked⟩

def s2624_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, true, true, true] 0 (.inc 0)⟩
theorem s2624_plain_checked : check 345 s2624_plain_contract = true := by decide +kernel
def s2624_plain : CertifiedContract :=
  ⟨2624, 2625, 0, (.inc 0), s2624_plain_contract, 345, s2624_plain_checked⟩

def s2625_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, true, false] 0 .none⟩
theorem s2625_plain_checked : check 88 s2625_plain_contract = true := by decide +kernel
def s2625_plain : CertifiedContract :=
  ⟨2625, 2623, 0, .none, s2625_plain_contract, 88, s2625_plain_checked⟩

def s2626_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, true, false] 0 .none⟩
theorem s2626_zero_checked : check 326 s2626_zero_contract = true := by decide +kernel
def s2626_zero : CertifiedContract :=
  ⟨2626, 2630, 0, .none, s2626_zero_contract, 326, s2626_zero_checked⟩

def s2626_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2626_positive_checked : check 332 s2626_positive_contract = true := by decide +kernel
def s2626_positive : CertifiedContract :=
  ⟨2626, 2627, 1, (.dec 2), s2626_positive_contract, 332, s2626_positive_checked⟩

def s2627_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2627_plain_checked : check 345 s2627_plain_contract = true := by decide +kernel
def s2627_plain : CertifiedContract :=
  ⟨2627, 2628, 0, (.inc 5), s2627_plain_contract, 345, s2627_plain_checked⟩

def s2628_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2628_plain_checked : check 372 s2628_plain_contract = true := by decide +kernel
def s2628_plain : CertifiedContract :=
  ⟨2628, 2629, 0, (.inc 8), s2628_plain_contract, 372, s2628_plain_checked⟩

def s2629_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, false, false] 0 .none⟩
theorem s2629_plain_checked : check 97 s2629_plain_contract = true := by decide +kernel
def s2629_plain : CertifiedContract :=
  ⟨2629, 2626, 0, .none, s2629_plain_contract, 97, s2629_plain_checked⟩

def s2630_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, true, false] 0 .none⟩
theorem s2630_zero_checked : check 347 s2630_zero_contract = true := by decide +kernel
def s2630_zero : CertifiedContract :=
  ⟨2630, 2636, 0, .none, s2630_zero_contract, 347, s2630_zero_checked⟩

def s2630_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2630_positive_checked : check 350 s2630_positive_contract = true := by decide +kernel
def s2630_positive : CertifiedContract :=
  ⟨2630, 2631, 1, (.dec 8), s2630_positive_contract, 350, s2630_positive_checked⟩

def s2631_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2631_plain_checked : check 345 s2631_plain_contract = true := by decide +kernel
def s2631_plain : CertifiedContract :=
  ⟨2631, 2632, 0, (.inc 5), s2631_plain_contract, 345, s2631_plain_checked⟩

def s2632_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, true, true, true] 0 .none⟩
theorem s2632_zero_checked : check 365 s2632_zero_contract = true := by decide +kernel
def s2632_zero : CertifiedContract :=
  ⟨2632, 2635, 0, .none, s2632_zero_contract, 365, s2632_zero_checked⟩

def s2632_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2632_positive_checked : check 368 s2632_positive_contract = true := by decide +kernel
def s2632_positive : CertifiedContract :=
  ⟨2632, 2633, 1, (.dec 8), s2632_positive_contract, 368, s2632_positive_checked⟩

def s2633_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2633_plain_checked : check 363 s2633_plain_contract = true := by decide +kernel
def s2633_plain : CertifiedContract :=
  ⟨2633, 2634, 0, (.inc 2), s2633_plain_contract, 363, s2633_plain_checked⟩

def s2634_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2634_plain_checked : check 97 s2634_plain_contract = true := by decide +kernel
def s2634_plain : CertifiedContract :=
  ⟨2634, 2632, 0, .none, s2634_plain_contract, 97, s2634_plain_checked⟩

def s2635_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, false, false, false] 0 .none⟩
theorem s2635_plain_checked : check 100 s2635_plain_contract = true := by decide +kernel
def s2635_plain : CertifiedContract :=
  ⟨2635, 2626, 0, .none, s2635_plain_contract, 100, s2635_plain_checked⟩

def s2636_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s2636_zero_checked : check 344 s2636_zero_contract = true := by decide +kernel
def s2636_zero : CertifiedContract :=
  ⟨2636, 2642, 0, .none, s2636_zero_contract, 344, s2636_zero_checked⟩

def s2636_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2636_positive_checked : check 332 s2636_positive_contract = true := by decide +kernel
def s2636_positive : CertifiedContract :=
  ⟨2636, 2637, 1, (.dec 5), s2636_positive_contract, 332, s2636_positive_checked⟩

def s2637_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2637_plain_checked : check 345 s2637_plain_contract = true := by decide +kernel
def s2637_plain : CertifiedContract :=
  ⟨2637, 2638, 0, (.inc 2), s2637_plain_contract, 345, s2637_plain_checked⟩

def s2638_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2638_plain_checked : check 348 s2638_plain_contract = true := by decide +kernel
def s2638_plain : CertifiedContract :=
  ⟨2638, 2639, 0, (.inc 2), s2638_plain_contract, 348, s2638_plain_checked⟩

def s2639_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2639_plain_checked : check 345 s2639_plain_contract = true := by decide +kernel
def s2639_plain : CertifiedContract :=
  ⟨2639, 2640, 0, (.inc 2), s2639_plain_contract, 345, s2639_plain_checked⟩

def s2640_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, true, true, true] 0 (.inc 2)⟩
theorem s2640_plain_checked : check 351 s2640_plain_contract = true := by decide +kernel
def s2640_plain : CertifiedContract :=
  ⟨2640, 2641, 0, (.inc 2), s2640_plain_contract, 351, s2640_plain_checked⟩

def s2641_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, true, true, true, true, true, true, false] 0 .none⟩
theorem s2641_plain_checked : check 85 s2641_plain_contract = true := by decide +kernel
def s2641_plain : CertifiedContract :=
  ⟨2641, 2636, 0, .none, s2641_plain_contract, 85, s2641_plain_checked⟩

def s2642_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s2642_zero_checked : check 308 s2642_zero_contract = true := by decide +kernel
def s2642_zero : CertifiedContract :=
  ⟨2642, 2645, 0, .none, s2642_zero_contract, 308, s2642_zero_checked⟩

def s2642_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s2642_positive_checked : check 314 s2642_positive_contract = true := by decide +kernel
def s2642_positive : CertifiedContract :=
  ⟨2642, 2643, 1, (.dec 2), s2642_positive_contract, 314, s2642_positive_checked⟩

def s2643_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s2643_plain_checked : check 327 s2643_plain_contract = true := by decide +kernel
def s2643_plain : CertifiedContract :=
  ⟨2643, 2644, 0, (.inc 8), s2643_plain_contract, 327, s2643_plain_checked⟩

def s2644_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s2644_plain_checked : check 82 s2644_plain_contract = true := by decide +kernel
def s2644_plain : CertifiedContract :=
  ⟨2644, 2642, 0, .none, s2644_plain_contract, 82, s2644_plain_checked⟩

def s2645_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2645_zero_checked : check 329 s2645_zero_contract = true := by decide +kernel
def s2645_zero : CertifiedContract :=
  ⟨2645, 2648, 0, .none, s2645_zero_contract, 329, s2645_zero_checked⟩

def s2645_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2645_positive_checked : check 335 s2645_positive_contract = true := by decide +kernel
def s2645_positive : CertifiedContract :=
  ⟨2645, 2646, 1, (.dec 0), s2645_positive_contract, 335, s2645_positive_checked⟩

def s2646_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2646_plain_checked : check 327 s2646_plain_contract = true := by decide +kernel
def s2646_plain : CertifiedContract :=
  ⟨2646, 2647, 0, (.inc 2), s2646_plain_contract, 327, s2646_plain_checked⟩

def s2647_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s2647_plain_checked : check 85 s2647_plain_contract = true := by decide +kernel
def s2647_plain : CertifiedContract :=
  ⟨2647, 2645, 0, .none, s2647_plain_contract, 85, s2647_plain_checked⟩

def s2648_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2648_zero_checked : check 335 s2648_zero_contract = true := by decide +kernel
def s2648_zero : CertifiedContract :=
  ⟨2648, 2652, 0, .none, s2648_zero_contract, 335, s2648_zero_checked⟩

def s2648_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2648_positive_checked : check 341 s2648_positive_contract = true := by decide +kernel
def s2648_positive : CertifiedContract :=
  ⟨2648, 2649, 1, (.dec 2), s2648_positive_contract, 341, s2648_positive_checked⟩

def s2649_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2649_plain_checked : check 354 s2649_plain_contract = true := by decide +kernel
def s2649_plain : CertifiedContract :=
  ⟨2649, 2650, 0, (.inc 5), s2649_plain_contract, 354, s2649_plain_checked⟩

def s2650_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2650_plain_checked : check 381 s2650_plain_contract = true := by decide +kernel
def s2650_plain : CertifiedContract :=
  ⟨2650, 2651, 0, (.inc 8), s2650_plain_contract, 381, s2650_plain_checked⟩

def s2651_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2651_plain_checked : check 100 s2651_plain_contract = true := by decide +kernel
def s2651_plain : CertifiedContract :=
  ⟨2651, 2648, 0, .none, s2651_plain_contract, 100, s2651_plain_checked⟩

def s2652_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s2652_zero_checked : check 356 s2652_zero_contract = true := by decide +kernel
def s2652_zero : CertifiedContract :=
  ⟨2652, 2658, 0, .none, s2652_zero_contract, 356, s2652_zero_checked⟩

def s2652_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2652_positive_checked : check 359 s2652_positive_contract = true := by decide +kernel
def s2652_positive : CertifiedContract :=
  ⟨2652, 2653, 1, (.dec 8), s2652_positive_contract, 359, s2652_positive_checked⟩

def s2653_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2653_plain_checked : check 354 s2653_plain_contract = true := by decide +kernel
def s2653_plain : CertifiedContract :=
  ⟨2653, 2654, 0, (.inc 5), s2653_plain_contract, 354, s2653_plain_checked⟩

def s2654_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s2654_zero_checked : check 374 s2654_zero_contract = true := by decide +kernel
def s2654_zero : CertifiedContract :=
  ⟨2654, 2657, 0, .none, s2654_zero_contract, 374, s2654_zero_checked⟩

def s2654_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2654_positive_checked : check 377 s2654_positive_contract = true := by decide +kernel
def s2654_positive : CertifiedContract :=
  ⟨2654, 2655, 1, (.dec 8), s2654_positive_contract, 377, s2654_positive_checked⟩

def s2655_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2655_plain_checked : check 372 s2655_plain_contract = true := by decide +kernel
def s2655_plain : CertifiedContract :=
  ⟨2655, 2656, 0, (.inc 2), s2655_plain_contract, 372, s2655_plain_checked⟩

def s2656_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2656_plain_checked : check 100 s2656_plain_contract = true := by decide +kernel
def s2656_plain : CertifiedContract :=
  ⟨2656, 2654, 0, .none, s2656_plain_contract, 100, s2656_plain_checked⟩

def s2657_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2657_plain_checked : check 103 s2657_plain_contract = true := by decide +kernel
def s2657_plain : CertifiedContract :=
  ⟨2657, 2648, 0, .none, s2657_plain_contract, 103, s2657_plain_checked⟩

def s2658_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s2658_zero_checked : check 344 s2658_zero_contract = true := by decide +kernel
def s2658_zero : CertifiedContract :=
  ⟨2658, 2661, 0, .none, s2658_zero_contract, 344, s2658_zero_checked⟩

def s2658_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2658_positive_checked : check 341 s2658_positive_contract = true := by decide +kernel
def s2658_positive : CertifiedContract :=
  ⟨2658, 2659, 1, (.dec 5), s2658_positive_contract, 341, s2658_positive_checked⟩

def s2659_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2659_plain_checked : check 354 s2659_plain_contract = true := by decide +kernel
def s2659_plain : CertifiedContract :=
  ⟨2659, 2660, 0, (.inc 0), s2659_plain_contract, 354, s2659_plain_checked⟩

def s2660_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s2660_plain_checked : check 91 s2660_plain_contract = true := by decide +kernel
def s2660_plain : CertifiedContract :=
  ⟨2660, 2658, 0, .none, s2660_plain_contract, 91, s2660_plain_checked⟩

def s2661_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s2661_zero_checked : check 308 s2661_zero_contract = true := by decide +kernel
def s2661_zero : CertifiedContract :=
  ⟨2661, 2665, 0, .none, s2661_zero_contract, 308, s2661_zero_checked⟩

def nonterminal : Array CertifiedContract := #[
  s2612_plain,
  s2613_plain,
  s2614_plain,
  s2615_zero,
  s2615_positive,
  s2616_plain,
  s2617_zero,
  s2617_positive,
  s2618_plain,
  s2619_zero,
  s2619_positive,
  s2620_plain,
  s2621_plain,
  s2622_plain,
  s2623_zero,
  s2623_positive,
  s2624_plain,
  s2625_plain,
  s2626_zero,
  s2626_positive,
  s2627_plain,
  s2628_plain,
  s2629_plain,
  s2630_zero,
  s2630_positive,
  s2631_plain,
  s2632_zero,
  s2632_positive,
  s2633_plain,
  s2634_plain,
  s2635_plain,
  s2636_zero,
  s2636_positive,
  s2637_plain,
  s2638_plain,
  s2639_plain,
  s2640_plain,
  s2641_plain,
  s2642_zero,
  s2642_positive,
  s2643_plain,
  s2644_plain,
  s2645_zero,
  s2645_positive,
  s2646_plain,
  s2647_plain,
  s2648_zero,
  s2648_positive,
  s2649_plain,
  s2650_plain,
  s2651_plain,
  s2652_zero,
  s2652_positive,
  s2653_plain,
  s2654_zero,
  s2654_positive,
  s2655_plain,
  s2656_plain,
  s2657_plain,
  s2658_zero,
  s2658_positive,
  s2659_plain,
  s2660_plain,
  s2661_zero
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S053
