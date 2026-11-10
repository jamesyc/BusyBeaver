import PA215.CertifiedContracts
import PA215.Census.C010
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard010Part1
open PA215.Contracts PA215.Census

def original1302 : RawOriginal := C010.records[22]'(by decide)
theorem original_id1302 : original1302.index = 1302 := by decide

def c1302 : Contract := original1302.toContract.get (by decide)
theorem binding1302 : original1302.toContract = some c1302 := rfl

theorem checked1302 : check 4000 c1302 = true := by decide

def original1303 : RawOriginal := C010.records[23]'(by decide)
theorem original_id1303 : original1303.index = 1303 := by decide

def c1303 : Contract := original1303.toContract.get (by decide)
theorem binding1303 : original1303.toContract = some c1303 := rfl

theorem checked1303 : check 4000 c1303 = true := by decide

def original1304 : RawOriginal := C010.records[24]'(by decide)
theorem original_id1304 : original1304.index = 1304 := by decide

def c1304 : Contract := original1304.toContract.get (by decide)
theorem binding1304 : original1304.toContract = some c1304 := rfl

theorem checked1304 : check 4000 c1304 = true := by decide

def original1305 : RawOriginal := C010.records[25]'(by decide)
theorem original_id1305 : original1305.index = 1305 := by decide

def c1305 : Contract := original1305.toContract.get (by decide)
theorem binding1305 : original1305.toContract = some c1305 := rfl

theorem checked1305 : check 4000 c1305 = true := by decide

def original1306 : RawOriginal := C010.records[26]'(by decide)
theorem original_id1306 : original1306.index = 1306 := by decide

def c1306 : Contract := original1306.toContract.get (by decide)
theorem binding1306 : original1306.toContract = some c1306 := rfl

theorem checked1306 : check 4000 c1306 = true := by decide

def original1307 : RawOriginal := C010.records[27]'(by decide)
theorem original_id1307 : original1307.index = 1307 := by decide

def c1307 : Contract := original1307.toContract.get (by decide)
theorem binding1307 : original1307.toContract = some c1307 := rfl

theorem checked1307 : check 4000 c1307 = true := by decide

def original1308 : RawOriginal := C010.records[28]'(by decide)
theorem original_id1308 : original1308.index = 1308 := by decide

def c1308 : Contract := original1308.toContract.get (by decide)
theorem binding1308 : original1308.toContract = some c1308 := rfl

theorem checked1308 : check 4000 c1308 = true := by decide

def original1309 : RawOriginal := C010.records[29]'(by decide)
theorem original_id1309 : original1309.index = 1309 := by decide

def c1309 : Contract := original1309.toContract.get (by decide)
theorem binding1309 : original1309.toContract = some c1309 := rfl

theorem checked1309 : check 4000 c1309 = true := by decide

def original1310 : RawOriginal := C010.records[30]'(by decide)
theorem original_id1310 : original1310.index = 1310 := by decide

def c1310 : Contract := original1310.toContract.get (by decide)
theorem binding1310 : original1310.toContract = some c1310 := rfl

theorem checked1310 : check 4000 c1310 = true := by decide

def original1311 : RawOriginal := C010.records[31]'(by decide)
theorem original_id1311 : original1311.index = 1311 := by decide

def c1311 : Contract := original1311.toContract.get (by decide)
theorem binding1311 : original1311.toContract = some c1311 := rfl

theorem checked1311 : check 4000 c1311 = true := by decide

def original1312 : RawOriginal := C010.records[32]'(by decide)
theorem original_id1312 : original1312.index = 1312 := by decide

def c1312 : Contract := original1312.toContract.get (by decide)
theorem binding1312 : original1312.toContract = some c1312 := rfl

theorem checked1312 : check 4000 c1312 = true := by decide

def original1313 : RawOriginal := C010.records[33]'(by decide)
theorem original_id1313 : original1313.index = 1313 := by decide

def c1313 : Contract := original1313.toContract.get (by decide)
theorem binding1313 : original1313.toContract = some c1313 := rfl

theorem checked1313 : check 4000 c1313 = true := by decide

def original1314 : RawOriginal := C010.records[34]'(by decide)
theorem original_id1314 : original1314.index = 1314 := by decide

def c1314 : Contract := original1314.toContract.get (by decide)
theorem binding1314 : original1314.toContract = some c1314 := rfl

theorem checked1314 : check 4000 c1314 = true := by decide

def original1315 : RawOriginal := C010.records[35]'(by decide)
theorem original_id1315 : original1315.index = 1315 := by decide

def c1315 : Contract := original1315.toContract.get (by decide)
theorem binding1315 : original1315.toContract = some c1315 := rfl

theorem checked1315 : check 4000 c1315 = true := by decide

def original1316 : RawOriginal := C010.records[36]'(by decide)
theorem original_id1316 : original1316.index = 1316 := by decide

def c1316 : Contract := original1316.toContract.get (by decide)
theorem binding1316 : original1316.toContract = some c1316 := rfl

theorem checked1316 : check 4000 c1316 = true := by decide

def original1317 : RawOriginal := C010.records[37]'(by decide)
theorem original_id1317 : original1317.index = 1317 := by decide

def c1317 : Contract := original1317.toContract.get (by decide)
theorem binding1317 : original1317.toContract = some c1317 := rfl

theorem checked1317 : check 4000 c1317 = true := by decide

def records : List Certified := [
  ⟨1302, c1302, 4000, checked1302⟩,
  ⟨1303, c1303, 4000, checked1303⟩,
  ⟨1304, c1304, 4000, checked1304⟩,
  ⟨1305, c1305, 4000, checked1305⟩,
  ⟨1306, c1306, 4000, checked1306⟩,
  ⟨1307, c1307, 4000, checked1307⟩,
  ⟨1308, c1308, 4000, checked1308⟩,
  ⟨1309, c1309, 4000, checked1309⟩,
  ⟨1310, c1310, 4000, checked1310⟩,
  ⟨1311, c1311, 4000, checked1311⟩,
  ⟨1312, c1312, 4000, checked1312⟩,
  ⟨1313, c1313, 4000, checked1313⟩,
  ⟨1314, c1314, 4000, checked1314⟩,
  ⟨1315, c1315, 4000, checked1315⟩,
  ⟨1316, c1316, 4000, checked1316⟩,
  ⟨1317, c1317, 4000, checked1317⟩]

end PA215.ContractShards.Shard010Part1
