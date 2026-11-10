import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C016
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard016Part6
open PA215.Contracts PA215.Census

def original2150 : RawOriginal := C016.records[102]'(by decide)
theorem original_id2150 : original2150.index = 2150 := by decide

def c2150 : Contract := original2150.toContract.get (by decide)
theorem binding2150 : original2150.toContract = some c2150 := rfl

theorem checked2150 : check 4000 c2150 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2151 : RawOriginal := C016.records[103]'(by decide)
theorem original_id2151 : original2151.index = 2151 := by decide

def c2151 : Contract := original2151.toContract.get (by decide)
theorem binding2151 : original2151.toContract = some c2151 := rfl

theorem checked2151 : check 4000 c2151 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2152 : RawOriginal := C016.records[104]'(by decide)
theorem original_id2152 : original2152.index = 2152 := by decide

def c2152 : Contract := original2152.toContract.get (by decide)
theorem binding2152 : original2152.toContract = some c2152 := rfl

theorem checked2152 : check 4000 c2152 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2153 : RawOriginal := C016.records[105]'(by decide)
theorem original_id2153 : original2153.index = 2153 := by decide

def c2153 : Contract := original2153.toContract.get (by decide)
theorem binding2153 : original2153.toContract = some c2153 := rfl

theorem checked2153 : check 4000 c2153 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2154 : RawOriginal := C016.records[106]'(by decide)
theorem original_id2154 : original2154.index = 2154 := by decide

def c2154 : Contract := original2154.toContract.get (by decide)
theorem binding2154 : original2154.toContract = some c2154 := rfl

theorem checked2154 : check 4000 c2154 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2155 : RawOriginal := C016.records[107]'(by decide)
theorem original_id2155 : original2155.index = 2155 := by decide

def c2155 : Contract := original2155.toContract.get (by decide)
theorem binding2155 : original2155.toContract = some c2155 := rfl

theorem checked2155 : check 4000 c2155 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2156 : RawOriginal := C016.records[108]'(by decide)
theorem original_id2156 : original2156.index = 2156 := by decide

def c2156 : Contract := original2156.toContract.get (by decide)
theorem binding2156 : original2156.toContract = some c2156 := rfl

theorem checked2156 : check 4000 c2156 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2157 : RawOriginal := C016.records[109]'(by decide)
theorem original_id2157 : original2157.index = 2157 := by decide

def c2157 : Contract := original2157.toContract.get (by decide)
theorem binding2157 : original2157.toContract = some c2157 := rfl

theorem checked2157 : check 4000 c2157 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2158 : RawOriginal := C016.records[110]'(by decide)
theorem original_id2158 : original2158.index = 2158 := by decide

def c2158 : Contract := original2158.toContract.get (by decide)
theorem binding2158 : original2158.toContract = some c2158 := rfl

theorem checked2158 : check 4000 c2158 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2159 : RawOriginal := C016.records[111]'(by decide)
theorem original_id2159 : original2159.index = 2159 := by decide

def c2159 : Contract := original2159.toContract.get (by decide)
theorem binding2159 : original2159.toContract = some c2159 := rfl

theorem checked2159 : check 4000 c2159 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2160 : RawOriginal := C016.records[112]'(by decide)
theorem original_id2160 : original2160.index = 2160 := by decide

def c2160 : Contract := original2160.toContract.get (by decide)
theorem binding2160 : original2160.toContract = some c2160 := rfl

theorem checked2160 : check 4000 c2160 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2161 : RawOriginal := C016.records[113]'(by decide)
theorem original_id2161 : original2161.index = 2161 := by decide

def c2161 : Contract := original2161.toContract.get (by decide)
theorem binding2161 : original2161.toContract = some c2161 := rfl

theorem checked2161 : check 4000 c2161 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2162 : RawOriginal := C016.records[114]'(by decide)
theorem original_id2162 : original2162.index = 2162 := by decide

def c2162 : Contract := original2162.toContract.get (by decide)
theorem binding2162 : original2162.toContract = some c2162 := rfl

theorem checked2162 : check 4000 c2162 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2163 : RawOriginal := C016.records[115]'(by decide)
theorem original_id2163 : original2163.index = 2163 := by decide

def c2163 : Contract := original2163.toContract.get (by decide)
theorem binding2163 : original2163.toContract = some c2163 := rfl

theorem checked2163 : check 4000 c2163 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2164 : RawOriginal := C016.records[116]'(by decide)
theorem original_id2164 : original2164.index = 2164 := by decide

def c2164 : Contract := original2164.toContract.get (by decide)
theorem binding2164 : original2164.toContract = some c2164 := rfl

theorem checked2164 : check 4000 c2164 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2165 : RawOriginal := C016.records[117]'(by decide)
theorem original_id2165 : original2165.index = 2165 := by decide

def c2165 : Contract := original2165.toContract.get (by decide)
theorem binding2165 : original2165.toContract = some c2165 := rfl

theorem checked2165 : check 4000 c2165 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2150, c2150, 4000, checked2150⟩,
  ⟨2151, c2151, 4000, checked2151⟩,
  ⟨2152, c2152, 4000, checked2152⟩,
  ⟨2153, c2153, 4000, checked2153⟩,
  ⟨2154, c2154, 4000, checked2154⟩,
  ⟨2155, c2155, 4000, checked2155⟩,
  ⟨2156, c2156, 4000, checked2156⟩,
  ⟨2157, c2157, 4000, checked2157⟩,
  ⟨2158, c2158, 4000, checked2158⟩,
  ⟨2159, c2159, 4000, checked2159⟩,
  ⟨2160, c2160, 4000, checked2160⟩,
  ⟨2161, c2161, 4000, checked2161⟩,
  ⟨2162, c2162, 4000, checked2162⟩,
  ⟨2163, c2163, 4000, checked2163⟩,
  ⟨2164, c2164, 4000, checked2164⟩,
  ⟨2165, c2165, 4000, checked2165⟩]

end PA215.ContractShards.Shard016Part6
