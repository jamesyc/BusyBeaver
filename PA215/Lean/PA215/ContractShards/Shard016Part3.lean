import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C016
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard016Part3
open PA215.Contracts PA215.Census

def original2102 : RawOriginal := C016.records[54]'(by decide)
theorem original_id2102 : original2102.index = 2102 := by decide

def c2102 : Contract := original2102.toContract.get (by decide)
theorem binding2102 : original2102.toContract = some c2102 := rfl

theorem checked2102 : check 4000 c2102 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2103 : RawOriginal := C016.records[55]'(by decide)
theorem original_id2103 : original2103.index = 2103 := by decide

def c2103 : Contract := original2103.toContract.get (by decide)
theorem binding2103 : original2103.toContract = some c2103 := rfl

theorem checked2103 : check 4000 c2103 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2104 : RawOriginal := C016.records[56]'(by decide)
theorem original_id2104 : original2104.index = 2104 := by decide

def c2104 : Contract := original2104.toContract.get (by decide)
theorem binding2104 : original2104.toContract = some c2104 := rfl

theorem checked2104 : check 4000 c2104 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2105 : RawOriginal := C016.records[57]'(by decide)
theorem original_id2105 : original2105.index = 2105 := by decide

def c2105 : Contract := original2105.toContract.get (by decide)
theorem binding2105 : original2105.toContract = some c2105 := rfl

theorem checked2105 : check 4000 c2105 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2106 : RawOriginal := C016.records[58]'(by decide)
theorem original_id2106 : original2106.index = 2106 := by decide

def c2106 : Contract := original2106.toContract.get (by decide)
theorem binding2106 : original2106.toContract = some c2106 := rfl

theorem checked2106 : check 4000 c2106 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2107 : RawOriginal := C016.records[59]'(by decide)
theorem original_id2107 : original2107.index = 2107 := by decide

def c2107 : Contract := original2107.toContract.get (by decide)
theorem binding2107 : original2107.toContract = some c2107 := rfl

theorem checked2107 : check 4000 c2107 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2108 : RawOriginal := C016.records[60]'(by decide)
theorem original_id2108 : original2108.index = 2108 := by decide

def c2108 : Contract := original2108.toContract.get (by decide)
theorem binding2108 : original2108.toContract = some c2108 := rfl

theorem checked2108 : check 4000 c2108 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2109 : RawOriginal := C016.records[61]'(by decide)
theorem original_id2109 : original2109.index = 2109 := by decide

def c2109 : Contract := original2109.toContract.get (by decide)
theorem binding2109 : original2109.toContract = some c2109 := rfl

theorem checked2109 : check 4000 c2109 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2110 : RawOriginal := C016.records[62]'(by decide)
theorem original_id2110 : original2110.index = 2110 := by decide

def c2110 : Contract := original2110.toContract.get (by decide)
theorem binding2110 : original2110.toContract = some c2110 := rfl

theorem checked2110 : check 4000 c2110 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2111 : RawOriginal := C016.records[63]'(by decide)
theorem original_id2111 : original2111.index = 2111 := by decide

def c2111 : Contract := original2111.toContract.get (by decide)
theorem binding2111 : original2111.toContract = some c2111 := rfl

theorem checked2111 : check 4000 c2111 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2112 : RawOriginal := C016.records[64]'(by decide)
theorem original_id2112 : original2112.index = 2112 := by decide

def c2112 : Contract := original2112.toContract.get (by decide)
theorem binding2112 : original2112.toContract = some c2112 := rfl

theorem checked2112 : check 4000 c2112 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2113 : RawOriginal := C016.records[65]'(by decide)
theorem original_id2113 : original2113.index = 2113 := by decide

def c2113 : Contract := original2113.toContract.get (by decide)
theorem binding2113 : original2113.toContract = some c2113 := rfl

theorem checked2113 : check 4000 c2113 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2114 : RawOriginal := C016.records[66]'(by decide)
theorem original_id2114 : original2114.index = 2114 := by decide

def c2114 : Contract := original2114.toContract.get (by decide)
theorem binding2114 : original2114.toContract = some c2114 := rfl

theorem checked2114 : check 4000 c2114 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2115 : RawOriginal := C016.records[67]'(by decide)
theorem original_id2115 : original2115.index = 2115 := by decide

def c2115 : Contract := original2115.toContract.get (by decide)
theorem binding2115 : original2115.toContract = some c2115 := rfl

theorem checked2115 : check 4000 c2115 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2116 : RawOriginal := C016.records[68]'(by decide)
theorem original_id2116 : original2116.index = 2116 := by decide

def c2116 : Contract := original2116.toContract.get (by decide)
theorem binding2116 : original2116.toContract = some c2116 := rfl

theorem checked2116 : check 4000 c2116 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2117 : RawOriginal := C016.records[69]'(by decide)
theorem original_id2117 : original2117.index = 2117 := by decide

def c2117 : Contract := original2117.toContract.get (by decide)
theorem binding2117 : original2117.toContract = some c2117 := rfl

theorem checked2117 : check 4000 c2117 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2102, c2102, 4000, checked2102⟩,
  ⟨2103, c2103, 4000, checked2103⟩,
  ⟨2104, c2104, 4000, checked2104⟩,
  ⟨2105, c2105, 4000, checked2105⟩,
  ⟨2106, c2106, 4000, checked2106⟩,
  ⟨2107, c2107, 4000, checked2107⟩,
  ⟨2108, c2108, 4000, checked2108⟩,
  ⟨2109, c2109, 4000, checked2109⟩,
  ⟨2110, c2110, 4000, checked2110⟩,
  ⟨2111, c2111, 4000, checked2111⟩,
  ⟨2112, c2112, 4000, checked2112⟩,
  ⟨2113, c2113, 4000, checked2113⟩,
  ⟨2114, c2114, 4000, checked2114⟩,
  ⟨2115, c2115, 4000, checked2115⟩,
  ⟨2116, c2116, 4000, checked2116⟩,
  ⟨2117, c2117, 4000, checked2117⟩]

end PA215.ContractShards.Shard016Part3
