import PA215.CertifiedContracts
import PA215.Census.C008
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard008Part5
open PA215.Contracts PA215.Census

def original1110 : RawOriginal := C008.records[86]'(by decide)
theorem original_id1110 : original1110.index = 1110 := by decide

def c1110 : Contract := original1110.toContract.get (by decide)
theorem binding1110 : original1110.toContract = some c1110 := rfl

theorem checked1110 : check 4000 c1110 = true := by decide

def original1111 : RawOriginal := C008.records[87]'(by decide)
theorem original_id1111 : original1111.index = 1111 := by decide

def c1111 : Contract := original1111.toContract.get (by decide)
theorem binding1111 : original1111.toContract = some c1111 := rfl

theorem checked1111 : check 4000 c1111 = true := by decide

def original1112 : RawOriginal := C008.records[88]'(by decide)
theorem original_id1112 : original1112.index = 1112 := by decide

def c1112 : Contract := original1112.toContract.get (by decide)
theorem binding1112 : original1112.toContract = some c1112 := rfl

theorem checked1112 : check 4000 c1112 = true := by decide

def original1113 : RawOriginal := C008.records[89]'(by decide)
theorem original_id1113 : original1113.index = 1113 := by decide

def c1113 : Contract := original1113.toContract.get (by decide)
theorem binding1113 : original1113.toContract = some c1113 := rfl

theorem checked1113 : check 4000 c1113 = true := by decide

def original1114 : RawOriginal := C008.records[90]'(by decide)
theorem original_id1114 : original1114.index = 1114 := by decide

def c1114 : Contract := original1114.toContract.get (by decide)
theorem binding1114 : original1114.toContract = some c1114 := rfl

theorem checked1114 : check 4000 c1114 = true := by decide

def original1115 : RawOriginal := C008.records[91]'(by decide)
theorem original_id1115 : original1115.index = 1115 := by decide

def c1115 : Contract := original1115.toContract.get (by decide)
theorem binding1115 : original1115.toContract = some c1115 := rfl

theorem checked1115 : check 4000 c1115 = true := by decide

def original1116 : RawOriginal := C008.records[92]'(by decide)
theorem original_id1116 : original1116.index = 1116 := by decide

def c1116 : Contract := original1116.toContract.get (by decide)
theorem binding1116 : original1116.toContract = some c1116 := rfl

theorem checked1116 : check 4000 c1116 = true := by decide

def original1117 : RawOriginal := C008.records[93]'(by decide)
theorem original_id1117 : original1117.index = 1117 := by decide

def c1117 : Contract := original1117.toContract.get (by decide)
theorem binding1117 : original1117.toContract = some c1117 := rfl

theorem checked1117 : check 4000 c1117 = true := by decide

def original1118 : RawOriginal := C008.records[94]'(by decide)
theorem original_id1118 : original1118.index = 1118 := by decide

def c1118 : Contract := original1118.toContract.get (by decide)
theorem binding1118 : original1118.toContract = some c1118 := rfl

theorem checked1118 : check 4000 c1118 = true := by decide

def original1119 : RawOriginal := C008.records[95]'(by decide)
theorem original_id1119 : original1119.index = 1119 := by decide

def c1119 : Contract := original1119.toContract.get (by decide)
theorem binding1119 : original1119.toContract = some c1119 := rfl

theorem checked1119 : check 4000 c1119 = true := by decide

def original1120 : RawOriginal := C008.records[96]'(by decide)
theorem original_id1120 : original1120.index = 1120 := by decide

def c1120 : Contract := original1120.toContract.get (by decide)
theorem binding1120 : original1120.toContract = some c1120 := rfl

theorem checked1120 : check 4000 c1120 = true := by decide

def original1121 : RawOriginal := C008.records[97]'(by decide)
theorem original_id1121 : original1121.index = 1121 := by decide

def c1121 : Contract := original1121.toContract.get (by decide)
theorem binding1121 : original1121.toContract = some c1121 := rfl

theorem checked1121 : check 4000 c1121 = true := by decide

def original1122 : RawOriginal := C008.records[98]'(by decide)
theorem original_id1122 : original1122.index = 1122 := by decide

def c1122 : Contract := original1122.toContract.get (by decide)
theorem binding1122 : original1122.toContract = some c1122 := rfl

theorem checked1122 : check 4000 c1122 = true := by decide

def original1123 : RawOriginal := C008.records[99]'(by decide)
theorem original_id1123 : original1123.index = 1123 := by decide

def c1123 : Contract := original1123.toContract.get (by decide)
theorem binding1123 : original1123.toContract = some c1123 := rfl

theorem checked1123 : check 4000 c1123 = true := by decide

def original1124 : RawOriginal := C008.records[100]'(by decide)
theorem original_id1124 : original1124.index = 1124 := by decide

def c1124 : Contract := original1124.toContract.get (by decide)
theorem binding1124 : original1124.toContract = some c1124 := rfl

theorem checked1124 : check 4000 c1124 = true := by decide

def original1125 : RawOriginal := C008.records[101]'(by decide)
theorem original_id1125 : original1125.index = 1125 := by decide

def c1125 : Contract := original1125.toContract.get (by decide)
theorem binding1125 : original1125.toContract = some c1125 := rfl

theorem checked1125 : check 4000 c1125 = true := by decide

def records : List Certified := [
  ⟨1110, c1110, 4000, checked1110⟩,
  ⟨1111, c1111, 4000, checked1111⟩,
  ⟨1112, c1112, 4000, checked1112⟩,
  ⟨1113, c1113, 4000, checked1113⟩,
  ⟨1114, c1114, 4000, checked1114⟩,
  ⟨1115, c1115, 4000, checked1115⟩,
  ⟨1116, c1116, 4000, checked1116⟩,
  ⟨1117, c1117, 4000, checked1117⟩,
  ⟨1118, c1118, 4000, checked1118⟩,
  ⟨1119, c1119, 4000, checked1119⟩,
  ⟨1120, c1120, 4000, checked1120⟩,
  ⟨1121, c1121, 4000, checked1121⟩,
  ⟨1122, c1122, 4000, checked1122⟩,
  ⟨1123, c1123, 4000, checked1123⟩,
  ⟨1124, c1124, 4000, checked1124⟩,
  ⟨1125, c1125, 4000, checked1125⟩]

end PA215.ContractShards.Shard008Part5
