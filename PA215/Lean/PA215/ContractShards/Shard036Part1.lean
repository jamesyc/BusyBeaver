import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C036
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard036Part1
open PA215.Contracts PA215.Census

def original4630 : RawOriginal := C036.records[22]'(by decide)
theorem original_id4630 : original4630.index = 4630 := by decide

def c4630 : Contract := original4630.toContract.get (by decide)
theorem binding4630 : original4630.toContract = some c4630 := rfl

theorem checked4630 : check 4000 c4630 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4631 : RawOriginal := C036.records[23]'(by decide)
theorem original_id4631 : original4631.index = 4631 := by decide

def c4631 : Contract := original4631.toContract.get (by decide)
theorem binding4631 : original4631.toContract = some c4631 := rfl

theorem checked4631 : check 4000 c4631 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4632 : RawOriginal := C036.records[24]'(by decide)
theorem original_id4632 : original4632.index = 4632 := by decide

def c4632 : Contract := original4632.toContract.get (by decide)
theorem binding4632 : original4632.toContract = some c4632 := rfl

theorem checked4632 : check 4000 c4632 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4633 : RawOriginal := C036.records[25]'(by decide)
theorem original_id4633 : original4633.index = 4633 := by decide

def c4633 : Contract := original4633.toContract.get (by decide)
theorem binding4633 : original4633.toContract = some c4633 := rfl

theorem checked4633 : check 4000 c4633 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4634 : RawOriginal := C036.records[26]'(by decide)
theorem original_id4634 : original4634.index = 4634 := by decide

def c4634 : Contract := original4634.toContract.get (by decide)
theorem binding4634 : original4634.toContract = some c4634 := rfl

theorem checked4634 : check 4000 c4634 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4635 : RawOriginal := C036.records[27]'(by decide)
theorem original_id4635 : original4635.index = 4635 := by decide

def c4635 : Contract := original4635.toContract.get (by decide)
theorem binding4635 : original4635.toContract = some c4635 := rfl

theorem checked4635 : check 4000 c4635 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4636 : RawOriginal := C036.records[28]'(by decide)
theorem original_id4636 : original4636.index = 4636 := by decide

def c4636 : Contract := original4636.toContract.get (by decide)
theorem binding4636 : original4636.toContract = some c4636 := rfl

theorem checked4636 : check 4000 c4636 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4637 : RawOriginal := C036.records[29]'(by decide)
theorem original_id4637 : original4637.index = 4637 := by decide

def c4637 : Contract := original4637.toContract.get (by decide)
theorem binding4637 : original4637.toContract = some c4637 := rfl

theorem checked4637 : check 4000 c4637 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4638 : RawOriginal := C036.records[30]'(by decide)
theorem original_id4638 : original4638.index = 4638 := by decide

def c4638 : Contract := original4638.toContract.get (by decide)
theorem binding4638 : original4638.toContract = some c4638 := rfl

theorem checked4638 : check 4000 c4638 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4639 : RawOriginal := C036.records[31]'(by decide)
theorem original_id4639 : original4639.index = 4639 := by decide

def c4639 : Contract := original4639.toContract.get (by decide)
theorem binding4639 : original4639.toContract = some c4639 := rfl

theorem checked4639 : check 4000 c4639 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4640 : RawOriginal := C036.records[32]'(by decide)
theorem original_id4640 : original4640.index = 4640 := by decide

def c4640 : Contract := original4640.toContract.get (by decide)
theorem binding4640 : original4640.toContract = some c4640 := rfl

theorem checked4640 : check 4000 c4640 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4641 : RawOriginal := C036.records[33]'(by decide)
theorem original_id4641 : original4641.index = 4641 := by decide

def c4641 : Contract := original4641.toContract.get (by decide)
theorem binding4641 : original4641.toContract = some c4641 := rfl

theorem checked4641 : check 4000 c4641 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4642 : RawOriginal := C036.records[34]'(by decide)
theorem original_id4642 : original4642.index = 4642 := by decide

def c4642 : Contract := original4642.toContract.get (by decide)
theorem binding4642 : original4642.toContract = some c4642 := rfl

theorem checked4642 : check 4000 c4642 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4643 : RawOriginal := C036.records[35]'(by decide)
theorem original_id4643 : original4643.index = 4643 := by decide

def c4643 : Contract := original4643.toContract.get (by decide)
theorem binding4643 : original4643.toContract = some c4643 := rfl

theorem checked4643 : check 4000 c4643 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4644 : RawOriginal := C036.records[36]'(by decide)
theorem original_id4644 : original4644.index = 4644 := by decide

def c4644 : Contract := original4644.toContract.get (by decide)
theorem binding4644 : original4644.toContract = some c4644 := rfl

theorem checked4644 : check 4000 c4644 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original4645 : RawOriginal := C036.records[37]'(by decide)
theorem original_id4645 : original4645.index = 4645 := by decide

def c4645 : Contract := original4645.toContract.get (by decide)
theorem binding4645 : original4645.toContract = some c4645 := rfl

theorem checked4645 : check 4000 c4645 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨4630, c4630, 4000, checked4630⟩,
  ⟨4631, c4631, 4000, checked4631⟩,
  ⟨4632, c4632, 4000, checked4632⟩,
  ⟨4633, c4633, 4000, checked4633⟩,
  ⟨4634, c4634, 4000, checked4634⟩,
  ⟨4635, c4635, 4000, checked4635⟩,
  ⟨4636, c4636, 4000, checked4636⟩,
  ⟨4637, c4637, 4000, checked4637⟩,
  ⟨4638, c4638, 4000, checked4638⟩,
  ⟨4639, c4639, 4000, checked4639⟩,
  ⟨4640, c4640, 4000, checked4640⟩,
  ⟨4641, c4641, 4000, checked4641⟩,
  ⟨4642, c4642, 4000, checked4642⟩,
  ⟨4643, c4643, 4000, checked4643⟩,
  ⟨4644, c4644, 4000, checked4644⟩,
  ⟨4645, c4645, 4000, checked4645⟩]

end PA215.ContractShards.Shard036Part1
