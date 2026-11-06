import PA215.CertifiedContracts
import PA215.Census.C009
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard009Part4
open PA215.Contracts PA215.Census

def original1222 : RawOriginal := C009.records[70]'(by decide)
theorem original_id1222 : original1222.index = 1222 := by decide

def c1222 : Contract := original1222.toContract.get (by decide)
theorem binding1222 : original1222.toContract = some c1222 := rfl

theorem checked1222 : check 4000 c1222 = true := by decide

def original1223 : RawOriginal := C009.records[71]'(by decide)
theorem original_id1223 : original1223.index = 1223 := by decide

def c1223 : Contract := original1223.toContract.get (by decide)
theorem binding1223 : original1223.toContract = some c1223 := rfl

theorem checked1223 : check 4000 c1223 = true := by decide

def original1224 : RawOriginal := C009.records[72]'(by decide)
theorem original_id1224 : original1224.index = 1224 := by decide

def c1224 : Contract := original1224.toContract.get (by decide)
theorem binding1224 : original1224.toContract = some c1224 := rfl

theorem checked1224 : check 4000 c1224 = true := by decide

def original1225 : RawOriginal := C009.records[73]'(by decide)
theorem original_id1225 : original1225.index = 1225 := by decide

def c1225 : Contract := original1225.toContract.get (by decide)
theorem binding1225 : original1225.toContract = some c1225 := rfl

theorem checked1225 : check 4000 c1225 = true := by decide

def original1226 : RawOriginal := C009.records[74]'(by decide)
theorem original_id1226 : original1226.index = 1226 := by decide

def c1226 : Contract := original1226.toContract.get (by decide)
theorem binding1226 : original1226.toContract = some c1226 := rfl

theorem checked1226 : check 4000 c1226 = true := by decide

def original1227 : RawOriginal := C009.records[75]'(by decide)
theorem original_id1227 : original1227.index = 1227 := by decide

def c1227 : Contract := original1227.toContract.get (by decide)
theorem binding1227 : original1227.toContract = some c1227 := rfl

theorem checked1227 : check 4000 c1227 = true := by decide

def original1228 : RawOriginal := C009.records[76]'(by decide)
theorem original_id1228 : original1228.index = 1228 := by decide

def c1228 : Contract := original1228.toContract.get (by decide)
theorem binding1228 : original1228.toContract = some c1228 := rfl

theorem checked1228 : check 4000 c1228 = true := by decide

def original1229 : RawOriginal := C009.records[77]'(by decide)
theorem original_id1229 : original1229.index = 1229 := by decide

def c1229 : Contract := original1229.toContract.get (by decide)
theorem binding1229 : original1229.toContract = some c1229 := rfl

theorem checked1229 : check 4000 c1229 = true := by decide

def original1230 : RawOriginal := C009.records[78]'(by decide)
theorem original_id1230 : original1230.index = 1230 := by decide

def c1230 : Contract := original1230.toContract.get (by decide)
theorem binding1230 : original1230.toContract = some c1230 := rfl

theorem checked1230 : check 4000 c1230 = true := by decide

def original1231 : RawOriginal := C009.records[79]'(by decide)
theorem original_id1231 : original1231.index = 1231 := by decide

def c1231 : Contract := original1231.toContract.get (by decide)
theorem binding1231 : original1231.toContract = some c1231 := rfl

theorem checked1231 : check 4000 c1231 = true := by decide

def original1232 : RawOriginal := C009.records[80]'(by decide)
theorem original_id1232 : original1232.index = 1232 := by decide

def c1232 : Contract := original1232.toContract.get (by decide)
theorem binding1232 : original1232.toContract = some c1232 := rfl

theorem checked1232 : check 4000 c1232 = true := by decide

def original1233 : RawOriginal := C009.records[81]'(by decide)
theorem original_id1233 : original1233.index = 1233 := by decide

def c1233 : Contract := original1233.toContract.get (by decide)
theorem binding1233 : original1233.toContract = some c1233 := rfl

theorem checked1233 : check 4000 c1233 = true := by decide

def original1234 : RawOriginal := C009.records[82]'(by decide)
theorem original_id1234 : original1234.index = 1234 := by decide

def c1234 : Contract := original1234.toContract.get (by decide)
theorem binding1234 : original1234.toContract = some c1234 := rfl

theorem checked1234 : check 4000 c1234 = true := by decide

def original1235 : RawOriginal := C009.records[83]'(by decide)
theorem original_id1235 : original1235.index = 1235 := by decide

def c1235 : Contract := original1235.toContract.get (by decide)
theorem binding1235 : original1235.toContract = some c1235 := rfl

theorem checked1235 : check 4000 c1235 = true := by decide

def original1236 : RawOriginal := C009.records[84]'(by decide)
theorem original_id1236 : original1236.index = 1236 := by decide

def c1236 : Contract := original1236.toContract.get (by decide)
theorem binding1236 : original1236.toContract = some c1236 := rfl

theorem checked1236 : check 4000 c1236 = true := by decide

def original1237 : RawOriginal := C009.records[85]'(by decide)
theorem original_id1237 : original1237.index = 1237 := by decide

def c1237 : Contract := original1237.toContract.get (by decide)
theorem binding1237 : original1237.toContract = some c1237 := rfl

theorem checked1237 : check 4000 c1237 = true := by decide

def records : List Certified := [
  ⟨1222, c1222, 4000, checked1222⟩,
  ⟨1223, c1223, 4000, checked1223⟩,
  ⟨1224, c1224, 4000, checked1224⟩,
  ⟨1225, c1225, 4000, checked1225⟩,
  ⟨1226, c1226, 4000, checked1226⟩,
  ⟨1227, c1227, 4000, checked1227⟩,
  ⟨1228, c1228, 4000, checked1228⟩,
  ⟨1229, c1229, 4000, checked1229⟩,
  ⟨1230, c1230, 4000, checked1230⟩,
  ⟨1231, c1231, 4000, checked1231⟩,
  ⟨1232, c1232, 4000, checked1232⟩,
  ⟨1233, c1233, 4000, checked1233⟩,
  ⟨1234, c1234, 4000, checked1234⟩,
  ⟨1235, c1235, 4000, checked1235⟩,
  ⟨1236, c1236, 4000, checked1236⟩,
  ⟨1237, c1237, 4000, checked1237⟩]

end PA215.ContractShards.Shard009Part4
