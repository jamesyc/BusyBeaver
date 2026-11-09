module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S054
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s2661_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, true, false] 1 (.dec 3)⟩
theorem s2661_positive_checked : check 315 s2661_positive_contract = true := by decide +kernel
def s2661_positive : CertifiedContract :=
  ⟨2661, 2662, 1, (.dec 3), s2661_positive_contract, 315, s2661_positive_checked⟩

def s2662_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2662_plain_checked : check 328 s2662_plain_contract = true := by decide +kernel
def s2662_plain : CertifiedContract :=
  ⟨2662, 2663, 0, (.inc 2), s2662_plain_contract, 328, s2662_plain_checked⟩

def s2663_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2663_plain_checked : check 355 s2663_plain_contract = true := by decide +kernel
def s2663_plain : CertifiedContract :=
  ⟨2663, 2664, 0, (.inc 8), s2663_plain_contract, 355, s2663_plain_checked⟩

def s2664_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s2664_plain_checked : check 92 s2664_plain_contract = true := by decide +kernel
def s2664_plain : CertifiedContract :=
  ⟨2664, 2661, 0, .none, s2664_plain_contract, 92, s2664_plain_checked⟩

def s2665_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s2665_zero_checked : check 315 s2665_zero_contract = true := by decide +kernel
def s2665_zero : CertifiedContract :=
  ⟨2665, 2668, 0, .none, s2665_zero_contract, 315, s2665_zero_checked⟩

def s2665_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s2665_positive_checked : check 315 s2665_positive_contract = true := by decide +kernel
def s2665_positive : CertifiedContract :=
  ⟨2665, 2666, 1, (.dec 8), s2665_positive_contract, 315, s2665_positive_checked⟩

def s2666_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, true, true, true] 0 (.inc 3)⟩
theorem s2666_plain_checked : check 331 s2666_plain_contract = true := by decide +kernel
def s2666_plain : CertifiedContract :=
  ⟨2666, 2667, 0, (.inc 3), s2666_plain_contract, 331, s2666_plain_checked⟩

def s2667_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s2667_plain_checked : check 83 s2667_plain_contract = true := by decide +kernel
def s2667_plain : CertifiedContract :=
  ⟨2667, 2665, 0, .none, s2667_plain_contract, 83, s2667_plain_checked⟩

def s2668_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s2668_zero_checked : check 309 s2668_zero_contract = true := by decide +kernel
def s2668_zero : CertifiedContract :=
  ⟨2668, 2671, 0, .none, s2668_zero_contract, 309, s2668_zero_checked⟩

def s2668_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2668_positive_checked : check 315 s2668_positive_contract = true := by decide +kernel
def s2668_positive : CertifiedContract :=
  ⟨2668, 2669, 1, (.dec 2), s2668_positive_contract, 315, s2668_positive_checked⟩

def s2669_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s2669_plain_checked : check 328 s2669_plain_contract = true := by decide +kernel
def s2669_plain : CertifiedContract :=
  ⟨2669, 2670, 0, (.inc 8), s2669_plain_contract, 328, s2669_plain_checked⟩

def s2670_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s2670_plain_checked : check 83 s2670_plain_contract = true := by decide +kernel
def s2670_plain : CertifiedContract :=
  ⟨2670, 2668, 0, .none, s2670_plain_contract, 83, s2670_plain_checked⟩

def s2671_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2671_zero_checked : check 330 s2671_zero_contract = true := by decide +kernel
def s2671_zero : CertifiedContract :=
  ⟨2671, 2674, 0, .none, s2671_zero_contract, 330, s2671_zero_checked⟩

def s2671_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2671_positive_checked : check 336 s2671_positive_contract = true := by decide +kernel
def s2671_positive : CertifiedContract :=
  ⟨2671, 2672, 1, (.dec 0), s2671_positive_contract, 336, s2671_positive_checked⟩

def s2672_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2672_plain_checked : check 328 s2672_plain_contract = true := by decide +kernel
def s2672_plain : CertifiedContract :=
  ⟨2672, 2673, 0, (.inc 2), s2672_plain_contract, 328, s2672_plain_checked⟩

def s2673_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s2673_plain_checked : check 86 s2673_plain_contract = true := by decide +kernel
def s2673_plain : CertifiedContract :=
  ⟨2673, 2671, 0, .none, s2673_plain_contract, 86, s2673_plain_checked⟩

def s2674_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2674_zero_checked : check 336 s2674_zero_contract = true := by decide +kernel
def s2674_zero : CertifiedContract :=
  ⟨2674, 2678, 0, .none, s2674_zero_contract, 336, s2674_zero_checked⟩

def s2674_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2674_positive_checked : check 342 s2674_positive_contract = true := by decide +kernel
def s2674_positive : CertifiedContract :=
  ⟨2674, 2675, 1, (.dec 2), s2674_positive_contract, 342, s2674_positive_checked⟩

def s2675_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2675_plain_checked : check 355 s2675_plain_contract = true := by decide +kernel
def s2675_plain : CertifiedContract :=
  ⟨2675, 2676, 0, (.inc 5), s2675_plain_contract, 355, s2675_plain_checked⟩

def s2676_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2676_plain_checked : check 382 s2676_plain_contract = true := by decide +kernel
def s2676_plain : CertifiedContract :=
  ⟨2676, 2677, 0, (.inc 8), s2676_plain_contract, 382, s2676_plain_checked⟩

def s2677_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2677_plain_checked : check 101 s2677_plain_contract = true := by decide +kernel
def s2677_plain : CertifiedContract :=
  ⟨2677, 2674, 0, .none, s2677_plain_contract, 101, s2677_plain_checked⟩

def s2678_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s2678_zero_checked : check 357 s2678_zero_contract = true := by decide +kernel
def s2678_zero : CertifiedContract :=
  ⟨2678, 2684, 0, .none, s2678_zero_contract, 357, s2678_zero_checked⟩

def s2678_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2678_positive_checked : check 360 s2678_positive_contract = true := by decide +kernel
def s2678_positive : CertifiedContract :=
  ⟨2678, 2679, 1, (.dec 8), s2678_positive_contract, 360, s2678_positive_checked⟩

def s2679_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2679_plain_checked : check 355 s2679_plain_contract = true := by decide +kernel
def s2679_plain : CertifiedContract :=
  ⟨2679, 2680, 0, (.inc 5), s2679_plain_contract, 355, s2679_plain_checked⟩

def s2680_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s2680_zero_checked : check 375 s2680_zero_contract = true := by decide +kernel
def s2680_zero : CertifiedContract :=
  ⟨2680, 2683, 0, .none, s2680_zero_contract, 375, s2680_zero_checked⟩

def s2680_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2680_positive_checked : check 378 s2680_positive_contract = true := by decide +kernel
def s2680_positive : CertifiedContract :=
  ⟨2680, 2681, 1, (.dec 8), s2680_positive_contract, 378, s2680_positive_checked⟩

def s2681_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2681_plain_checked : check 373 s2681_plain_contract = true := by decide +kernel
def s2681_plain : CertifiedContract :=
  ⟨2681, 2682, 0, (.inc 2), s2681_plain_contract, 373, s2681_plain_checked⟩

def s2682_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2682_plain_checked : check 101 s2682_plain_contract = true := by decide +kernel
def s2682_plain : CertifiedContract :=
  ⟨2682, 2680, 0, .none, s2682_plain_contract, 101, s2682_plain_checked⟩

def s2683_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2683_plain_checked : check 104 s2683_plain_contract = true := by decide +kernel
def s2683_plain : CertifiedContract :=
  ⟨2683, 2674, 0, .none, s2683_plain_contract, 104, s2683_plain_checked⟩

def s2684_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s2684_zero_checked : check 345 s2684_zero_contract = true := by decide +kernel
def s2684_zero : CertifiedContract :=
  ⟨2684, 2687, 0, .none, s2684_zero_contract, 345, s2684_zero_checked⟩

def s2684_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2684_positive_checked : check 342 s2684_positive_contract = true := by decide +kernel
def s2684_positive : CertifiedContract :=
  ⟨2684, 2685, 1, (.dec 5), s2684_positive_contract, 342, s2684_positive_checked⟩

def s2685_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2685_plain_checked : check 355 s2685_plain_contract = true := by decide +kernel
def s2685_plain : CertifiedContract :=
  ⟨2685, 2686, 0, (.inc 0), s2685_plain_contract, 355, s2685_plain_checked⟩

def s2686_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s2686_plain_checked : check 92 s2686_plain_contract = true := by decide +kernel
def s2686_plain : CertifiedContract :=
  ⟨2686, 2684, 0, .none, s2686_plain_contract, 92, s2686_plain_checked⟩

def s2687_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s2687_zero_checked : check 309 s2687_zero_contract = true := by decide +kernel
def s2687_zero : CertifiedContract :=
  ⟨2687, 2691, 0, .none, s2687_zero_contract, 309, s2687_zero_checked⟩

def s2687_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s2687_positive_checked : check 315 s2687_positive_contract = true := by decide +kernel
def s2687_positive : CertifiedContract :=
  ⟨2687, 2688, 1, (.dec 7), s2687_positive_contract, 315, s2687_positive_checked⟩

def s2688_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2688_plain_checked : check 319 s2688_plain_contract = true := by decide +kernel
def s2688_plain : CertifiedContract :=
  ⟨2688, 2689, 0, (.inc 2), s2688_plain_contract, 319, s2688_plain_checked⟩

def s2689_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2689_plain_checked : check 346 s2689_plain_contract = true := by decide +kernel
def s2689_plain : CertifiedContract :=
  ⟨2689, 2690, 0, (.inc 8), s2689_plain_contract, 346, s2689_plain_checked⟩

def s2690_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s2690_plain_checked : check 89 s2690_plain_contract = true := by decide +kernel
def s2690_plain : CertifiedContract :=
  ⟨2690, 2687, 0, .none, s2690_plain_contract, 89, s2690_plain_checked⟩

def s2691_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s2691_zero_checked : check 318 s2691_zero_contract = true := by decide +kernel
def s2691_zero : CertifiedContract :=
  ⟨2691, 2694, 0, .none, s2691_zero_contract, 318, s2691_zero_checked⟩

def s2691_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s2691_positive_checked : check 315 s2691_positive_contract = true := by decide +kernel
def s2691_positive : CertifiedContract :=
  ⟨2691, 2692, 1, (.dec 8), s2691_positive_contract, 315, s2691_positive_checked⟩

def s2692_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s2692_plain_checked : check 346 s2692_plain_contract = true := by decide +kernel
def s2692_plain : CertifiedContract :=
  ⟨2692, 2693, 0, (.inc 7), s2692_plain_contract, 346, s2692_plain_checked⟩

def s2693_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s2693_plain_checked : check 83 s2693_plain_contract = true := by decide +kernel
def s2693_plain : CertifiedContract :=
  ⟨2693, 2691, 0, .none, s2693_plain_contract, 83, s2693_plain_checked⟩

def s2694_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s2694_zero_checked : check 321 s2694_zero_contract = true := by decide +kernel
def s2694_zero : CertifiedContract :=
  ⟨2694, 2702, 0, .none, s2694_zero_contract, 321, s2694_zero_checked⟩

def s2694_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s2694_positive_checked : check 327 s2694_positive_contract = true := by decide +kernel
def s2694_positive : CertifiedContract :=
  ⟨2694, 2695, 1, (.dec 0), s2694_positive_contract, 327, s2694_positive_checked⟩

def s2695_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2695_plain_checked : check 337 s2695_plain_contract = true := by decide +kernel
def s2695_plain : CertifiedContract :=
  ⟨2695, 2696, 0, (.inc 5), s2695_plain_contract, 337, s2695_plain_checked⟩

def s2696_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2696_zero_checked : check 363 s2696_zero_contract = true := by decide +kernel
def s2696_zero : CertifiedContract :=
  ⟨2696, 2698, 0, .none, s2696_zero_contract, 363, s2696_zero_checked⟩

def s2696_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2696_positive_checked : check 369 s2696_positive_contract = true := by decide +kernel
def s2696_positive : CertifiedContract :=
  ⟨2696, 2697, 1, (.dec 8), s2696_positive_contract, 369, s2696_positive_checked⟩

def s2697_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s2697_plain_checked : check 98 s2697_plain_contract = true := by decide +kernel
def s2697_plain : CertifiedContract :=
  ⟨2697, 2701, 0, .none, s2697_plain_contract, 98, s2697_plain_checked⟩

def s2698_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s2698_zero_checked : check 375 s2698_zero_contract = true := by decide +kernel
def s2698_zero : CertifiedContract :=
  ⟨2698, 2701, 0, .none, s2698_zero_contract, 375, s2698_zero_checked⟩

def s2698_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2698_positive_checked : check 378 s2698_positive_contract = true := by decide +kernel
def s2698_positive : CertifiedContract :=
  ⟨2698, 2699, 1, (.dec 5), s2698_positive_contract, 378, s2698_positive_checked⟩

def s2699_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2699_plain_checked : check 382 s2699_plain_contract = true := by decide +kernel
def s2699_plain : CertifiedContract :=
  ⟨2699, 2700, 0, (.inc 8), s2699_plain_contract, 382, s2699_plain_checked⟩

def s2700_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2700_plain_checked : check 101 s2700_plain_contract = true := by decide +kernel
def s2700_plain : CertifiedContract :=
  ⟨2700, 2698, 0, .none, s2700_plain_contract, 101, s2700_plain_checked⟩

def s2701_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s2701_plain_checked : check 92 s2701_plain_contract = true := by decide +kernel
def s2701_plain : CertifiedContract :=
  ⟨2701, 2694, 0, .none, s2701_plain_contract, 92, s2701_plain_checked⟩

def s2702_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2702_zero_checked : check 321 s2702_zero_contract = true := by decide +kernel
def s2702_zero : CertifiedContract :=
  ⟨2702, 2705, 0, .none, s2702_zero_contract, 321, s2702_zero_checked⟩

def s2702_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s2702_positive_checked : check 324 s2702_positive_contract = true := by decide +kernel
def s2702_positive : CertifiedContract :=
  ⟨2702, 2703, 1, (.dec 5), s2702_positive_contract, 324, s2702_positive_checked⟩

def s2703_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s2703_plain_checked : check 337 s2703_plain_contract = true := by decide +kernel
def s2703_plain : CertifiedContract :=
  ⟨2703, 2704, 0, (.inc 0), s2703_plain_contract, 337, s2703_plain_checked⟩

def s2704_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s2704_plain_checked : check 86 s2704_plain_contract = true := by decide +kernel
def s2704_plain : CertifiedContract :=
  ⟨2704, 2702, 0, .none, s2704_plain_contract, 86, s2704_plain_checked⟩

def s2705_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s2705_zero_checked : check 318 s2705_zero_contract = true := by decide +kernel
def s2705_zero : CertifiedContract :=
  ⟨2705, 2709, 0, .none, s2705_zero_contract, 318, s2705_zero_checked⟩

def s2705_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2705_positive_checked : check 324 s2705_positive_contract = true := by decide +kernel
def s2705_positive : CertifiedContract :=
  ⟨2705, 2706, 1, (.dec 2), s2705_positive_contract, 324, s2705_positive_checked⟩

def s2706_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2706_plain_checked : check 337 s2706_plain_contract = true := by decide +kernel
def s2706_plain : CertifiedContract :=
  ⟨2706, 2707, 0, (.inc 5), s2706_plain_contract, 337, s2706_plain_checked⟩

def s2707_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2707_plain_checked : check 364 s2707_plain_contract = true := by decide +kernel
def s2707_plain : CertifiedContract :=
  ⟨2707, 2708, 0, (.inc 8), s2707_plain_contract, 364, s2707_plain_checked⟩

def s2708_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s2708_plain_checked : check 95 s2708_plain_contract = true := by decide +kernel
def s2708_plain : CertifiedContract :=
  ⟨2708, 2705, 0, .none, s2708_plain_contract, 95, s2708_plain_checked⟩

def s2709_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s2709_zero_checked : check 339 s2709_zero_contract = true := by decide +kernel
def s2709_zero : CertifiedContract :=
  ⟨2709, 2715, 0, .none, s2709_zero_contract, 339, s2709_zero_checked⟩

def s2709_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2709_positive_checked : check 342 s2709_positive_contract = true := by decide +kernel
def s2709_positive : CertifiedContract :=
  ⟨2709, 2710, 1, (.dec 8), s2709_positive_contract, 342, s2709_positive_checked⟩

end PA211.UserCandidate.RuntimeShards.S054
