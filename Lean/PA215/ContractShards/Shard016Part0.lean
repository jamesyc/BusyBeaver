import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C016
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard016Part0
open PA215.Contracts PA215.Census

def original2054 : RawOriginal := C016.records[6]'(by decide)
theorem original_id2054 : original2054.index = 2054 := by decide

def c2054 : Contract := original2054.toContract.get (by decide)
theorem binding2054 : original2054.toContract = some c2054 := rfl

theorem checked2054 : check 4000 c2054 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2055 : RawOriginal := C016.records[7]'(by decide)
theorem original_id2055 : original2055.index = 2055 := by decide

def c2055 : Contract := original2055.toContract.get (by decide)
theorem binding2055 : original2055.toContract = some c2055 := rfl

theorem checked2055 : check 4000 c2055 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2056 : RawOriginal := C016.records[8]'(by decide)
theorem original_id2056 : original2056.index = 2056 := by decide

def c2056 : Contract := original2056.toContract.get (by decide)
theorem binding2056 : original2056.toContract = some c2056 := rfl

theorem checked2056 : check 4000 c2056 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2057 : RawOriginal := C016.records[9]'(by decide)
theorem original_id2057 : original2057.index = 2057 := by decide

def c2057 : Contract := original2057.toContract.get (by decide)
theorem binding2057 : original2057.toContract = some c2057 := rfl

theorem checked2057 : check 4000 c2057 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2058 : RawOriginal := C016.records[10]'(by decide)
theorem original_id2058 : original2058.index = 2058 := by decide

def c2058 : Contract := original2058.toContract.get (by decide)
theorem binding2058 : original2058.toContract = some c2058 := rfl

theorem checked2058 : check 4000 c2058 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2059 : RawOriginal := C016.records[11]'(by decide)
theorem original_id2059 : original2059.index = 2059 := by decide

def c2059 : Contract := original2059.toContract.get (by decide)
theorem binding2059 : original2059.toContract = some c2059 := rfl

theorem checked2059 : check 4000 c2059 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2060 : RawOriginal := C016.records[12]'(by decide)
theorem original_id2060 : original2060.index = 2060 := by decide

def c2060 : Contract := original2060.toContract.get (by decide)
theorem binding2060 : original2060.toContract = some c2060 := rfl

theorem checked2060 : check 4000 c2060 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2061 : RawOriginal := C016.records[13]'(by decide)
theorem original_id2061 : original2061.index = 2061 := by decide

def c2061 : Contract := original2061.toContract.get (by decide)
theorem binding2061 : original2061.toContract = some c2061 := rfl

theorem checked2061 : check 4000 c2061 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2062 : RawOriginal := C016.records[14]'(by decide)
theorem original_id2062 : original2062.index = 2062 := by decide

def c2062 : Contract := original2062.toContract.get (by decide)
theorem binding2062 : original2062.toContract = some c2062 := rfl

theorem checked2062 : check 4000 c2062 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2063 : RawOriginal := C016.records[15]'(by decide)
theorem original_id2063 : original2063.index = 2063 := by decide

def c2063 : Contract := original2063.toContract.get (by decide)
theorem binding2063 : original2063.toContract = some c2063 := rfl

theorem checked2063 : check 4000 c2063 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2064 : RawOriginal := C016.records[16]'(by decide)
theorem original_id2064 : original2064.index = 2064 := by decide

def c2064 : Contract := original2064.toContract.get (by decide)
theorem binding2064 : original2064.toContract = some c2064 := rfl

theorem checked2064 : check 4000 c2064 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2065 : RawOriginal := C016.records[17]'(by decide)
theorem original_id2065 : original2065.index = 2065 := by decide

def c2065 : Contract := original2065.toContract.get (by decide)
theorem binding2065 : original2065.toContract = some c2065 := rfl

theorem checked2065 : check 4000 c2065 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2066 : RawOriginal := C016.records[18]'(by decide)
theorem original_id2066 : original2066.index = 2066 := by decide

def c2066 : Contract := original2066.toContract.get (by decide)
theorem binding2066 : original2066.toContract = some c2066 := rfl

theorem checked2066 : check 4000 c2066 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2067 : RawOriginal := C016.records[19]'(by decide)
theorem original_id2067 : original2067.index = 2067 := by decide

def c2067 : Contract := original2067.toContract.get (by decide)
theorem binding2067 : original2067.toContract = some c2067 := rfl

theorem checked2067 : check 4000 c2067 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2068 : RawOriginal := C016.records[20]'(by decide)
theorem original_id2068 : original2068.index = 2068 := by decide

def c2068 : Contract := original2068.toContract.get (by decide)
theorem binding2068 : original2068.toContract = some c2068 := rfl

theorem checked2068 : check 4000 c2068 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2069 : RawOriginal := C016.records[21]'(by decide)
theorem original_id2069 : original2069.index = 2069 := by decide

def c2069 : Contract := original2069.toContract.get (by decide)
theorem binding2069 : original2069.toContract = some c2069 := rfl

theorem checked2069 : check 4000 c2069 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2054, c2054, 4000, checked2054⟩,
  ⟨2055, c2055, 4000, checked2055⟩,
  ⟨2056, c2056, 4000, checked2056⟩,
  ⟨2057, c2057, 4000, checked2057⟩,
  ⟨2058, c2058, 4000, checked2058⟩,
  ⟨2059, c2059, 4000, checked2059⟩,
  ⟨2060, c2060, 4000, checked2060⟩,
  ⟨2061, c2061, 4000, checked2061⟩,
  ⟨2062, c2062, 4000, checked2062⟩,
  ⟨2063, c2063, 4000, checked2063⟩,
  ⟨2064, c2064, 4000, checked2064⟩,
  ⟨2065, c2065, 4000, checked2065⟩,
  ⟨2066, c2066, 4000, checked2066⟩,
  ⟨2067, c2067, 4000, checked2067⟩,
  ⟨2068, c2068, 4000, checked2068⟩,
  ⟨2069, c2069, 4000, checked2069⟩]

end PA215.ContractShards.Shard016Part0
