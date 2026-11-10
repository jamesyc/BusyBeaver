import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C016
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard016Part1
open PA215.Contracts PA215.Census

def original2070 : RawOriginal := C016.records[22]'(by decide)
theorem original_id2070 : original2070.index = 2070 := by decide

def c2070 : Contract := original2070.toContract.get (by decide)
theorem binding2070 : original2070.toContract = some c2070 := rfl

theorem checked2070 : check 4000 c2070 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2071 : RawOriginal := C016.records[23]'(by decide)
theorem original_id2071 : original2071.index = 2071 := by decide

def c2071 : Contract := original2071.toContract.get (by decide)
theorem binding2071 : original2071.toContract = some c2071 := rfl

theorem checked2071 : check 4000 c2071 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2072 : RawOriginal := C016.records[24]'(by decide)
theorem original_id2072 : original2072.index = 2072 := by decide

def c2072 : Contract := original2072.toContract.get (by decide)
theorem binding2072 : original2072.toContract = some c2072 := rfl

theorem checked2072 : check 4000 c2072 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2073 : RawOriginal := C016.records[25]'(by decide)
theorem original_id2073 : original2073.index = 2073 := by decide

def c2073 : Contract := original2073.toContract.get (by decide)
theorem binding2073 : original2073.toContract = some c2073 := rfl

theorem checked2073 : check 4000 c2073 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2074 : RawOriginal := C016.records[26]'(by decide)
theorem original_id2074 : original2074.index = 2074 := by decide

def c2074 : Contract := original2074.toContract.get (by decide)
theorem binding2074 : original2074.toContract = some c2074 := rfl

theorem checked2074 : check 4000 c2074 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2075 : RawOriginal := C016.records[27]'(by decide)
theorem original_id2075 : original2075.index = 2075 := by decide

def c2075 : Contract := original2075.toContract.get (by decide)
theorem binding2075 : original2075.toContract = some c2075 := rfl

theorem checked2075 : check 4000 c2075 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2076 : RawOriginal := C016.records[28]'(by decide)
theorem original_id2076 : original2076.index = 2076 := by decide

def c2076 : Contract := original2076.toContract.get (by decide)
theorem binding2076 : original2076.toContract = some c2076 := rfl

theorem checked2076 : check 4000 c2076 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2077 : RawOriginal := C016.records[29]'(by decide)
theorem original_id2077 : original2077.index = 2077 := by decide

def c2077 : Contract := original2077.toContract.get (by decide)
theorem binding2077 : original2077.toContract = some c2077 := rfl

theorem checked2077 : check 4000 c2077 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2078 : RawOriginal := C016.records[30]'(by decide)
theorem original_id2078 : original2078.index = 2078 := by decide

def c2078 : Contract := original2078.toContract.get (by decide)
theorem binding2078 : original2078.toContract = some c2078 := rfl

theorem checked2078 : check 4000 c2078 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2079 : RawOriginal := C016.records[31]'(by decide)
theorem original_id2079 : original2079.index = 2079 := by decide

def c2079 : Contract := original2079.toContract.get (by decide)
theorem binding2079 : original2079.toContract = some c2079 := rfl

theorem checked2079 : check 4000 c2079 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2080 : RawOriginal := C016.records[32]'(by decide)
theorem original_id2080 : original2080.index = 2080 := by decide

def c2080 : Contract := original2080.toContract.get (by decide)
theorem binding2080 : original2080.toContract = some c2080 := rfl

theorem checked2080 : check 4000 c2080 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2081 : RawOriginal := C016.records[33]'(by decide)
theorem original_id2081 : original2081.index = 2081 := by decide

def c2081 : Contract := original2081.toContract.get (by decide)
theorem binding2081 : original2081.toContract = some c2081 := rfl

theorem checked2081 : check 4000 c2081 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2082 : RawOriginal := C016.records[34]'(by decide)
theorem original_id2082 : original2082.index = 2082 := by decide

def c2082 : Contract := original2082.toContract.get (by decide)
theorem binding2082 : original2082.toContract = some c2082 := rfl

theorem checked2082 : check 4000 c2082 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2083 : RawOriginal := C016.records[35]'(by decide)
theorem original_id2083 : original2083.index = 2083 := by decide

def c2083 : Contract := original2083.toContract.get (by decide)
theorem binding2083 : original2083.toContract = some c2083 := rfl

theorem checked2083 : check 4000 c2083 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2084 : RawOriginal := C016.records[36]'(by decide)
theorem original_id2084 : original2084.index = 2084 := by decide

def c2084 : Contract := original2084.toContract.get (by decide)
theorem binding2084 : original2084.toContract = some c2084 := rfl

theorem checked2084 : check 4000 c2084 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2085 : RawOriginal := C016.records[37]'(by decide)
theorem original_id2085 : original2085.index = 2085 := by decide

def c2085 : Contract := original2085.toContract.get (by decide)
theorem binding2085 : original2085.toContract = some c2085 := rfl

theorem checked2085 : check 4000 c2085 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2070, c2070, 4000, checked2070⟩,
  ⟨2071, c2071, 4000, checked2071⟩,
  ⟨2072, c2072, 4000, checked2072⟩,
  ⟨2073, c2073, 4000, checked2073⟩,
  ⟨2074, c2074, 4000, checked2074⟩,
  ⟨2075, c2075, 4000, checked2075⟩,
  ⟨2076, c2076, 4000, checked2076⟩,
  ⟨2077, c2077, 4000, checked2077⟩,
  ⟨2078, c2078, 4000, checked2078⟩,
  ⟨2079, c2079, 4000, checked2079⟩,
  ⟨2080, c2080, 4000, checked2080⟩,
  ⟨2081, c2081, 4000, checked2081⟩,
  ⟨2082, c2082, 4000, checked2082⟩,
  ⟨2083, c2083, 4000, checked2083⟩,
  ⟨2084, c2084, 4000, checked2084⟩,
  ⟨2085, c2085, 4000, checked2085⟩]

end PA215.ContractShards.Shard016Part1
