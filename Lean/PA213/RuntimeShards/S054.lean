import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S054
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s2661_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, true, false] 1 (.dec 3)⟩
theorem s2661_positive_checked : check 314 s2661_positive_contract = true := by decide +kernel
def s2661_positive : CertifiedContract :=
  ⟨2661, 2662, 1, (.dec 3), s2661_positive_contract, 314, s2661_positive_checked⟩

def s2662_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2662_plain_checked : check 327 s2662_plain_contract = true := by decide +kernel
def s2662_plain : CertifiedContract :=
  ⟨2662, 2663, 0, (.inc 2), s2662_plain_contract, 327, s2662_plain_checked⟩

def s2663_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2663_plain_checked : check 354 s2663_plain_contract = true := by decide +kernel
def s2663_plain : CertifiedContract :=
  ⟨2663, 2664, 0, (.inc 8), s2663_plain_contract, 354, s2663_plain_checked⟩

def s2664_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s2664_plain_checked : check 91 s2664_plain_contract = true := by decide +kernel
def s2664_plain : CertifiedContract :=
  ⟨2664, 2661, 0, .none, s2664_plain_contract, 91, s2664_plain_checked⟩

def s2665_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s2665_zero_checked : check 314 s2665_zero_contract = true := by decide +kernel
def s2665_zero : CertifiedContract :=
  ⟨2665, 2668, 0, .none, s2665_zero_contract, 314, s2665_zero_checked⟩

def s2665_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s2665_positive_checked : check 314 s2665_positive_contract = true := by decide +kernel
def s2665_positive : CertifiedContract :=
  ⟨2665, 2666, 1, (.dec 8), s2665_positive_contract, 314, s2665_positive_checked⟩

def s2666_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, true, true, true] 0 (.inc 3)⟩
theorem s2666_plain_checked : check 330 s2666_plain_contract = true := by decide +kernel
def s2666_plain : CertifiedContract :=
  ⟨2666, 2667, 0, (.inc 3), s2666_plain_contract, 330, s2666_plain_checked⟩

def s2667_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s2667_plain_checked : check 82 s2667_plain_contract = true := by decide +kernel
def s2667_plain : CertifiedContract :=
  ⟨2667, 2665, 0, .none, s2667_plain_contract, 82, s2667_plain_checked⟩

def s2668_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s2668_zero_checked : check 308 s2668_zero_contract = true := by decide +kernel
def s2668_zero : CertifiedContract :=
  ⟨2668, 2671, 0, .none, s2668_zero_contract, 308, s2668_zero_checked⟩

def s2668_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2668_positive_checked : check 314 s2668_positive_contract = true := by decide +kernel
def s2668_positive : CertifiedContract :=
  ⟨2668, 2669, 1, (.dec 2), s2668_positive_contract, 314, s2668_positive_checked⟩

def s2669_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s2669_plain_checked : check 327 s2669_plain_contract = true := by decide +kernel
def s2669_plain : CertifiedContract :=
  ⟨2669, 2670, 0, (.inc 8), s2669_plain_contract, 327, s2669_plain_checked⟩

def s2670_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s2670_plain_checked : check 82 s2670_plain_contract = true := by decide +kernel
def s2670_plain : CertifiedContract :=
  ⟨2670, 2668, 0, .none, s2670_plain_contract, 82, s2670_plain_checked⟩

def s2671_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2671_zero_checked : check 329 s2671_zero_contract = true := by decide +kernel
def s2671_zero : CertifiedContract :=
  ⟨2671, 2674, 0, .none, s2671_zero_contract, 329, s2671_zero_checked⟩

def s2671_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2671_positive_checked : check 335 s2671_positive_contract = true := by decide +kernel
def s2671_positive : CertifiedContract :=
  ⟨2671, 2672, 1, (.dec 0), s2671_positive_contract, 335, s2671_positive_checked⟩

def s2672_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2672_plain_checked : check 327 s2672_plain_contract = true := by decide +kernel
def s2672_plain : CertifiedContract :=
  ⟨2672, 2673, 0, (.inc 2), s2672_plain_contract, 327, s2672_plain_checked⟩

def s2673_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s2673_plain_checked : check 85 s2673_plain_contract = true := by decide +kernel
def s2673_plain : CertifiedContract :=
  ⟨2673, 2671, 0, .none, s2673_plain_contract, 85, s2673_plain_checked⟩

def s2674_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2674_zero_checked : check 335 s2674_zero_contract = true := by decide +kernel
def s2674_zero : CertifiedContract :=
  ⟨2674, 2678, 0, .none, s2674_zero_contract, 335, s2674_zero_checked⟩

def s2674_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2674_positive_checked : check 341 s2674_positive_contract = true := by decide +kernel
def s2674_positive : CertifiedContract :=
  ⟨2674, 2675, 1, (.dec 2), s2674_positive_contract, 341, s2674_positive_checked⟩

def s2675_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2675_plain_checked : check 354 s2675_plain_contract = true := by decide +kernel
def s2675_plain : CertifiedContract :=
  ⟨2675, 2676, 0, (.inc 5), s2675_plain_contract, 354, s2675_plain_checked⟩

def s2676_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2676_plain_checked : check 381 s2676_plain_contract = true := by decide +kernel
def s2676_plain : CertifiedContract :=
  ⟨2676, 2677, 0, (.inc 8), s2676_plain_contract, 381, s2676_plain_checked⟩

def s2677_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2677_plain_checked : check 100 s2677_plain_contract = true := by decide +kernel
def s2677_plain : CertifiedContract :=
  ⟨2677, 2674, 0, .none, s2677_plain_contract, 100, s2677_plain_checked⟩

def s2678_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s2678_zero_checked : check 356 s2678_zero_contract = true := by decide +kernel
def s2678_zero : CertifiedContract :=
  ⟨2678, 2684, 0, .none, s2678_zero_contract, 356, s2678_zero_checked⟩

def s2678_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2678_positive_checked : check 359 s2678_positive_contract = true := by decide +kernel
def s2678_positive : CertifiedContract :=
  ⟨2678, 2679, 1, (.dec 8), s2678_positive_contract, 359, s2678_positive_checked⟩

def s2679_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2679_plain_checked : check 354 s2679_plain_contract = true := by decide +kernel
def s2679_plain : CertifiedContract :=
  ⟨2679, 2680, 0, (.inc 5), s2679_plain_contract, 354, s2679_plain_checked⟩

def s2680_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s2680_zero_checked : check 374 s2680_zero_contract = true := by decide +kernel
def s2680_zero : CertifiedContract :=
  ⟨2680, 2683, 0, .none, s2680_zero_contract, 374, s2680_zero_checked⟩

def s2680_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2680_positive_checked : check 377 s2680_positive_contract = true := by decide +kernel
def s2680_positive : CertifiedContract :=
  ⟨2680, 2681, 1, (.dec 8), s2680_positive_contract, 377, s2680_positive_checked⟩

def s2681_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2681_plain_checked : check 372 s2681_plain_contract = true := by decide +kernel
def s2681_plain : CertifiedContract :=
  ⟨2681, 2682, 0, (.inc 2), s2681_plain_contract, 372, s2681_plain_checked⟩

def s2682_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2682_plain_checked : check 100 s2682_plain_contract = true := by decide +kernel
def s2682_plain : CertifiedContract :=
  ⟨2682, 2680, 0, .none, s2682_plain_contract, 100, s2682_plain_checked⟩

def s2683_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2683_plain_checked : check 103 s2683_plain_contract = true := by decide +kernel
def s2683_plain : CertifiedContract :=
  ⟨2683, 2674, 0, .none, s2683_plain_contract, 103, s2683_plain_checked⟩

def s2684_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s2684_zero_checked : check 344 s2684_zero_contract = true := by decide +kernel
def s2684_zero : CertifiedContract :=
  ⟨2684, 2687, 0, .none, s2684_zero_contract, 344, s2684_zero_checked⟩

def s2684_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2684_positive_checked : check 341 s2684_positive_contract = true := by decide +kernel
def s2684_positive : CertifiedContract :=
  ⟨2684, 2685, 1, (.dec 5), s2684_positive_contract, 341, s2684_positive_checked⟩

def s2685_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2685_plain_checked : check 354 s2685_plain_contract = true := by decide +kernel
def s2685_plain : CertifiedContract :=
  ⟨2685, 2686, 0, (.inc 0), s2685_plain_contract, 354, s2685_plain_checked⟩

def s2686_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s2686_plain_checked : check 91 s2686_plain_contract = true := by decide +kernel
def s2686_plain : CertifiedContract :=
  ⟨2686, 2684, 0, .none, s2686_plain_contract, 91, s2686_plain_checked⟩

def s2687_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s2687_zero_checked : check 308 s2687_zero_contract = true := by decide +kernel
def s2687_zero : CertifiedContract :=
  ⟨2687, 2691, 0, .none, s2687_zero_contract, 308, s2687_zero_checked⟩

def s2687_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s2687_positive_checked : check 314 s2687_positive_contract = true := by decide +kernel
def s2687_positive : CertifiedContract :=
  ⟨2687, 2688, 1, (.dec 7), s2687_positive_contract, 314, s2687_positive_checked⟩

def s2688_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2688_plain_checked : check 318 s2688_plain_contract = true := by decide +kernel
def s2688_plain : CertifiedContract :=
  ⟨2688, 2689, 0, (.inc 2), s2688_plain_contract, 318, s2688_plain_checked⟩

def s2689_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2689_plain_checked : check 345 s2689_plain_contract = true := by decide +kernel
def s2689_plain : CertifiedContract :=
  ⟨2689, 2690, 0, (.inc 8), s2689_plain_contract, 345, s2689_plain_checked⟩

def s2690_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s2690_plain_checked : check 88 s2690_plain_contract = true := by decide +kernel
def s2690_plain : CertifiedContract :=
  ⟨2690, 2687, 0, .none, s2690_plain_contract, 88, s2690_plain_checked⟩

def s2691_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s2691_zero_checked : check 317 s2691_zero_contract = true := by decide +kernel
def s2691_zero : CertifiedContract :=
  ⟨2691, 2694, 0, .none, s2691_zero_contract, 317, s2691_zero_checked⟩

def s2691_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s2691_positive_checked : check 314 s2691_positive_contract = true := by decide +kernel
def s2691_positive : CertifiedContract :=
  ⟨2691, 2692, 1, (.dec 8), s2691_positive_contract, 314, s2691_positive_checked⟩

def s2692_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s2692_plain_checked : check 345 s2692_plain_contract = true := by decide +kernel
def s2692_plain : CertifiedContract :=
  ⟨2692, 2693, 0, (.inc 7), s2692_plain_contract, 345, s2692_plain_checked⟩

def s2693_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s2693_plain_checked : check 82 s2693_plain_contract = true := by decide +kernel
def s2693_plain : CertifiedContract :=
  ⟨2693, 2691, 0, .none, s2693_plain_contract, 82, s2693_plain_checked⟩

def s2694_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s2694_zero_checked : check 320 s2694_zero_contract = true := by decide +kernel
def s2694_zero : CertifiedContract :=
  ⟨2694, 2702, 0, .none, s2694_zero_contract, 320, s2694_zero_checked⟩

def s2694_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s2694_positive_checked : check 326 s2694_positive_contract = true := by decide +kernel
def s2694_positive : CertifiedContract :=
  ⟨2694, 2695, 1, (.dec 0), s2694_positive_contract, 326, s2694_positive_checked⟩

def s2695_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2695_plain_checked : check 336 s2695_plain_contract = true := by decide +kernel
def s2695_plain : CertifiedContract :=
  ⟨2695, 2696, 0, (.inc 5), s2695_plain_contract, 336, s2695_plain_checked⟩

def s2696_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2696_zero_checked : check 362 s2696_zero_contract = true := by decide +kernel
def s2696_zero : CertifiedContract :=
  ⟨2696, 2698, 0, .none, s2696_zero_contract, 362, s2696_zero_checked⟩

def s2696_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2696_positive_checked : check 368 s2696_positive_contract = true := by decide +kernel
def s2696_positive : CertifiedContract :=
  ⟨2696, 2697, 1, (.dec 8), s2696_positive_contract, 368, s2696_positive_checked⟩

def s2697_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s2697_plain_checked : check 97 s2697_plain_contract = true := by decide +kernel
def s2697_plain : CertifiedContract :=
  ⟨2697, 2701, 0, .none, s2697_plain_contract, 97, s2697_plain_checked⟩

def s2698_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s2698_zero_checked : check 374 s2698_zero_contract = true := by decide +kernel
def s2698_zero : CertifiedContract :=
  ⟨2698, 2701, 0, .none, s2698_zero_contract, 374, s2698_zero_checked⟩

def s2698_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2698_positive_checked : check 377 s2698_positive_contract = true := by decide +kernel
def s2698_positive : CertifiedContract :=
  ⟨2698, 2699, 1, (.dec 5), s2698_positive_contract, 377, s2698_positive_checked⟩

def s2699_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2699_plain_checked : check 381 s2699_plain_contract = true := by decide +kernel
def s2699_plain : CertifiedContract :=
  ⟨2699, 2700, 0, (.inc 8), s2699_plain_contract, 381, s2699_plain_checked⟩

def s2700_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2700_plain_checked : check 100 s2700_plain_contract = true := by decide +kernel
def s2700_plain : CertifiedContract :=
  ⟨2700, 2698, 0, .none, s2700_plain_contract, 100, s2700_plain_checked⟩

def s2701_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s2701_plain_checked : check 91 s2701_plain_contract = true := by decide +kernel
def s2701_plain : CertifiedContract :=
  ⟨2701, 2694, 0, .none, s2701_plain_contract, 91, s2701_plain_checked⟩

def s2702_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2702_zero_checked : check 320 s2702_zero_contract = true := by decide +kernel
def s2702_zero : CertifiedContract :=
  ⟨2702, 2705, 0, .none, s2702_zero_contract, 320, s2702_zero_checked⟩

def s2702_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s2702_positive_checked : check 323 s2702_positive_contract = true := by decide +kernel
def s2702_positive : CertifiedContract :=
  ⟨2702, 2703, 1, (.dec 5), s2702_positive_contract, 323, s2702_positive_checked⟩

def s2703_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s2703_plain_checked : check 336 s2703_plain_contract = true := by decide +kernel
def s2703_plain : CertifiedContract :=
  ⟨2703, 2704, 0, (.inc 0), s2703_plain_contract, 336, s2703_plain_checked⟩

def s2704_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s2704_plain_checked : check 85 s2704_plain_contract = true := by decide +kernel
def s2704_plain : CertifiedContract :=
  ⟨2704, 2702, 0, .none, s2704_plain_contract, 85, s2704_plain_checked⟩

def s2705_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s2705_zero_checked : check 317 s2705_zero_contract = true := by decide +kernel
def s2705_zero : CertifiedContract :=
  ⟨2705, 2709, 0, .none, s2705_zero_contract, 317, s2705_zero_checked⟩

def s2705_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2705_positive_checked : check 323 s2705_positive_contract = true := by decide +kernel
def s2705_positive : CertifiedContract :=
  ⟨2705, 2706, 1, (.dec 2), s2705_positive_contract, 323, s2705_positive_checked⟩

def s2706_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2706_plain_checked : check 336 s2706_plain_contract = true := by decide +kernel
def s2706_plain : CertifiedContract :=
  ⟨2706, 2707, 0, (.inc 5), s2706_plain_contract, 336, s2706_plain_checked⟩

def s2707_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2707_plain_checked : check 363 s2707_plain_contract = true := by decide +kernel
def s2707_plain : CertifiedContract :=
  ⟨2707, 2708, 0, (.inc 8), s2707_plain_contract, 363, s2707_plain_checked⟩

def s2708_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2708_plain_checked : check 94 s2708_plain_contract = true := by decide +kernel
def s2708_plain : CertifiedContract :=
  ⟨2708, 2705, 0, .none, s2708_plain_contract, 94, s2708_plain_checked⟩

def s2709_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s2709_zero_checked : check 338 s2709_zero_contract = true := by decide +kernel
def s2709_zero : CertifiedContract :=
  ⟨2709, 2715, 0, .none, s2709_zero_contract, 338, s2709_zero_checked⟩

def s2709_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2709_positive_checked : check 341 s2709_positive_contract = true := by decide +kernel
def s2709_positive : CertifiedContract :=
  ⟨2709, 2710, 1, (.dec 8), s2709_positive_contract, 341, s2709_positive_checked⟩

def nonterminal : Array CertifiedContract := #[
  s2661_positive,
  s2662_plain,
  s2663_plain,
  s2664_plain,
  s2665_zero,
  s2665_positive,
  s2666_plain,
  s2667_plain,
  s2668_zero,
  s2668_positive,
  s2669_plain,
  s2670_plain,
  s2671_zero,
  s2671_positive,
  s2672_plain,
  s2673_plain,
  s2674_zero,
  s2674_positive,
  s2675_plain,
  s2676_plain,
  s2677_plain,
  s2678_zero,
  s2678_positive,
  s2679_plain,
  s2680_zero,
  s2680_positive,
  s2681_plain,
  s2682_plain,
  s2683_plain,
  s2684_zero,
  s2684_positive,
  s2685_plain,
  s2686_plain,
  s2687_zero,
  s2687_positive,
  s2688_plain,
  s2689_plain,
  s2690_plain,
  s2691_zero,
  s2691_positive,
  s2692_plain,
  s2693_plain,
  s2694_zero,
  s2694_positive,
  s2695_plain,
  s2696_zero,
  s2696_positive,
  s2697_plain,
  s2698_zero,
  s2698_positive,
  s2699_plain,
  s2700_plain,
  s2701_plain,
  s2702_zero,
  s2702_positive,
  s2703_plain,
  s2704_plain,
  s2705_zero,
  s2705_positive,
  s2706_plain,
  s2707_plain,
  s2708_plain,
  s2709_zero,
  s2709_positive
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S054
