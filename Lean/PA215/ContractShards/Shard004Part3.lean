import PA215.CertifiedContracts
import PA215.Census.C004
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard004Part3
open PA215.Contracts PA215.Census

def original566 : RawOriginal := C004.records[54]'(by decide)
theorem original_id566 : original566.index = 566 := by decide

def c566 : Contract := original566.toContract.get (by decide)
theorem binding566 : original566.toContract = some c566 := rfl

theorem checked566 : check 4000 c566 = true := by decide

def original567 : RawOriginal := C004.records[55]'(by decide)
theorem original_id567 : original567.index = 567 := by decide

def c567 : Contract := original567.toContract.get (by decide)
theorem binding567 : original567.toContract = some c567 := rfl

theorem checked567 : check 4000 c567 = true := by decide

def original568 : RawOriginal := C004.records[56]'(by decide)
theorem original_id568 : original568.index = 568 := by decide

def c568 : Contract := original568.toContract.get (by decide)
theorem binding568 : original568.toContract = some c568 := rfl

theorem checked568 : check 4000 c568 = true := by decide

def original569 : RawOriginal := C004.records[57]'(by decide)
theorem original_id569 : original569.index = 569 := by decide

def c569 : Contract := original569.toContract.get (by decide)
theorem binding569 : original569.toContract = some c569 := rfl

theorem checked569 : check 4000 c569 = true := by decide

def original570 : RawOriginal := C004.records[58]'(by decide)
theorem original_id570 : original570.index = 570 := by decide

def c570 : Contract := original570.toContract.get (by decide)
theorem binding570 : original570.toContract = some c570 := rfl

theorem checked570 : check 4000 c570 = true := by decide

def original571 : RawOriginal := C004.records[59]'(by decide)
theorem original_id571 : original571.index = 571 := by decide

def c571 : Contract := original571.toContract.get (by decide)
theorem binding571 : original571.toContract = some c571 := rfl

theorem checked571 : check 4000 c571 = true := by decide

def original572 : RawOriginal := C004.records[60]'(by decide)
theorem original_id572 : original572.index = 572 := by decide

def c572 : Contract := original572.toContract.get (by decide)
theorem binding572 : original572.toContract = some c572 := rfl

theorem checked572 : check 4000 c572 = true := by decide

def original573 : RawOriginal := C004.records[61]'(by decide)
theorem original_id573 : original573.index = 573 := by decide

def c573 : Contract := original573.toContract.get (by decide)
theorem binding573 : original573.toContract = some c573 := rfl

theorem checked573 : check 4000 c573 = true := by decide

def original574 : RawOriginal := C004.records[62]'(by decide)
theorem original_id574 : original574.index = 574 := by decide

def c574 : Contract := original574.toContract.get (by decide)
theorem binding574 : original574.toContract = some c574 := rfl

theorem checked574 : check 4000 c574 = true := by decide

def original575 : RawOriginal := C004.records[63]'(by decide)
theorem original_id575 : original575.index = 575 := by decide

def c575 : Contract := original575.toContract.get (by decide)
theorem binding575 : original575.toContract = some c575 := rfl

theorem checked575 : check 4000 c575 = true := by decide

def original576 : RawOriginal := C004.records[64]'(by decide)
theorem original_id576 : original576.index = 576 := by decide

def c576 : Contract := original576.toContract.get (by decide)
theorem binding576 : original576.toContract = some c576 := rfl

theorem checked576 : check 4000 c576 = true := by decide

def original577 : RawOriginal := C004.records[65]'(by decide)
theorem original_id577 : original577.index = 577 := by decide

def c577 : Contract := original577.toContract.get (by decide)
theorem binding577 : original577.toContract = some c577 := rfl

theorem checked577 : check 4000 c577 = true := by decide

def original578 : RawOriginal := C004.records[66]'(by decide)
theorem original_id578 : original578.index = 578 := by decide

def c578 : Contract := original578.toContract.get (by decide)
theorem binding578 : original578.toContract = some c578 := rfl

theorem checked578 : check 4000 c578 = true := by decide

def original579 : RawOriginal := C004.records[67]'(by decide)
theorem original_id579 : original579.index = 579 := by decide

def c579 : Contract := original579.toContract.get (by decide)
theorem binding579 : original579.toContract = some c579 := rfl

theorem checked579 : check 4000 c579 = true := by decide

def original580 : RawOriginal := C004.records[68]'(by decide)
theorem original_id580 : original580.index = 580 := by decide

def c580 : Contract := original580.toContract.get (by decide)
theorem binding580 : original580.toContract = some c580 := rfl

theorem checked580 : check 4000 c580 = true := by decide

def original581 : RawOriginal := C004.records[69]'(by decide)
theorem original_id581 : original581.index = 581 := by decide

def c581 : Contract := original581.toContract.get (by decide)
theorem binding581 : original581.toContract = some c581 := rfl

theorem checked581 : check 4000 c581 = true := by decide

def records : List Certified := [
  ⟨566, c566, 4000, checked566⟩,
  ⟨567, c567, 4000, checked567⟩,
  ⟨568, c568, 4000, checked568⟩,
  ⟨569, c569, 4000, checked569⟩,
  ⟨570, c570, 4000, checked570⟩,
  ⟨571, c571, 4000, checked571⟩,
  ⟨572, c572, 4000, checked572⟩,
  ⟨573, c573, 4000, checked573⟩,
  ⟨574, c574, 4000, checked574⟩,
  ⟨575, c575, 4000, checked575⟩,
  ⟨576, c576, 4000, checked576⟩,
  ⟨577, c577, 4000, checked577⟩,
  ⟨578, c578, 4000, checked578⟩,
  ⟨579, c579, 4000, checked579⟩,
  ⟨580, c580, 4000, checked580⟩,
  ⟨581, c581, 4000, checked581⟩]

end PA215.ContractShards.Shard004Part3
