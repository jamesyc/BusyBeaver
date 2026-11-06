import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C021
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard021Part1
open PA215.Contracts PA215.Census

def original2710 : RawOriginal := C021.records[22]'(by decide)
theorem original_id2710 : original2710.index = 2710 := by decide

def c2710 : Contract := original2710.toContract.get (by decide)
theorem binding2710 : original2710.toContract = some c2710 := rfl

theorem checked2710 : check 4000 c2710 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2711 : RawOriginal := C021.records[23]'(by decide)
theorem original_id2711 : original2711.index = 2711 := by decide

def c2711 : Contract := original2711.toContract.get (by decide)
theorem binding2711 : original2711.toContract = some c2711 := rfl

theorem checked2711 : check 4000 c2711 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2712 : RawOriginal := C021.records[24]'(by decide)
theorem original_id2712 : original2712.index = 2712 := by decide

def c2712 : Contract := original2712.toContract.get (by decide)
theorem binding2712 : original2712.toContract = some c2712 := rfl

theorem checked2712 : check 4000 c2712 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2713 : RawOriginal := C021.records[25]'(by decide)
theorem original_id2713 : original2713.index = 2713 := by decide

def c2713 : Contract := original2713.toContract.get (by decide)
theorem binding2713 : original2713.toContract = some c2713 := rfl

theorem checked2713 : check 4000 c2713 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2714 : RawOriginal := C021.records[26]'(by decide)
theorem original_id2714 : original2714.index = 2714 := by decide

def c2714 : Contract := original2714.toContract.get (by decide)
theorem binding2714 : original2714.toContract = some c2714 := rfl

theorem checked2714 : check 4000 c2714 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2715 : RawOriginal := C021.records[27]'(by decide)
theorem original_id2715 : original2715.index = 2715 := by decide

def c2715 : Contract := original2715.toContract.get (by decide)
theorem binding2715 : original2715.toContract = some c2715 := rfl

theorem checked2715 : check 4000 c2715 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2716 : RawOriginal := C021.records[28]'(by decide)
theorem original_id2716 : original2716.index = 2716 := by decide

def c2716 : Contract := original2716.toContract.get (by decide)
theorem binding2716 : original2716.toContract = some c2716 := rfl

theorem checked2716 : check 4000 c2716 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2717 : RawOriginal := C021.records[29]'(by decide)
theorem original_id2717 : original2717.index = 2717 := by decide

def c2717 : Contract := original2717.toContract.get (by decide)
theorem binding2717 : original2717.toContract = some c2717 := rfl

theorem checked2717 : check 4000 c2717 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2718 : RawOriginal := C021.records[30]'(by decide)
theorem original_id2718 : original2718.index = 2718 := by decide

def c2718 : Contract := original2718.toContract.get (by decide)
theorem binding2718 : original2718.toContract = some c2718 := rfl

theorem checked2718 : check 4000 c2718 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2719 : RawOriginal := C021.records[31]'(by decide)
theorem original_id2719 : original2719.index = 2719 := by decide

def c2719 : Contract := original2719.toContract.get (by decide)
theorem binding2719 : original2719.toContract = some c2719 := rfl

theorem checked2719 : check 4000 c2719 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2720 : RawOriginal := C021.records[32]'(by decide)
theorem original_id2720 : original2720.index = 2720 := by decide

def c2720 : Contract := original2720.toContract.get (by decide)
theorem binding2720 : original2720.toContract = some c2720 := rfl

theorem checked2720 : check 4000 c2720 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2721 : RawOriginal := C021.records[33]'(by decide)
theorem original_id2721 : original2721.index = 2721 := by decide

def c2721 : Contract := original2721.toContract.get (by decide)
theorem binding2721 : original2721.toContract = some c2721 := rfl

theorem checked2721 : check 4000 c2721 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2722 : RawOriginal := C021.records[34]'(by decide)
theorem original_id2722 : original2722.index = 2722 := by decide

def c2722 : Contract := original2722.toContract.get (by decide)
theorem binding2722 : original2722.toContract = some c2722 := rfl

theorem checked2722 : check 4000 c2722 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2723 : RawOriginal := C021.records[35]'(by decide)
theorem original_id2723 : original2723.index = 2723 := by decide

def c2723 : Contract := original2723.toContract.get (by decide)
theorem binding2723 : original2723.toContract = some c2723 := rfl

theorem checked2723 : check 4000 c2723 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2724 : RawOriginal := C021.records[36]'(by decide)
theorem original_id2724 : original2724.index = 2724 := by decide

def c2724 : Contract := original2724.toContract.get (by decide)
theorem binding2724 : original2724.toContract = some c2724 := rfl

theorem checked2724 : check 4000 c2724 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2725 : RawOriginal := C021.records[37]'(by decide)
theorem original_id2725 : original2725.index = 2725 := by decide

def c2725 : Contract := original2725.toContract.get (by decide)
theorem binding2725 : original2725.toContract = some c2725 := rfl

theorem checked2725 : check 4000 c2725 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2710, c2710, 4000, checked2710⟩,
  ⟨2711, c2711, 4000, checked2711⟩,
  ⟨2712, c2712, 4000, checked2712⟩,
  ⟨2713, c2713, 4000, checked2713⟩,
  ⟨2714, c2714, 4000, checked2714⟩,
  ⟨2715, c2715, 4000, checked2715⟩,
  ⟨2716, c2716, 4000, checked2716⟩,
  ⟨2717, c2717, 4000, checked2717⟩,
  ⟨2718, c2718, 4000, checked2718⟩,
  ⟨2719, c2719, 4000, checked2719⟩,
  ⟨2720, c2720, 4000, checked2720⟩,
  ⟨2721, c2721, 4000, checked2721⟩,
  ⟨2722, c2722, 4000, checked2722⟩,
  ⟨2723, c2723, 4000, checked2723⟩,
  ⟨2724, c2724, 4000, checked2724⟩,
  ⟨2725, c2725, 4000, checked2725⟩]

end PA215.ContractShards.Shard021Part1
