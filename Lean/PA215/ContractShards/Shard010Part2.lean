import PA215.CertifiedContracts
import PA215.Census.C010
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard010Part2
open PA215.Contracts PA215.Census

def original1318 : RawOriginal := C010.records[38]'(by decide)
theorem original_id1318 : original1318.index = 1318 := by decide

def c1318 : Contract := original1318.toContract.get (by decide)
theorem binding1318 : original1318.toContract = some c1318 := rfl

theorem checked1318 : check 4000 c1318 = true := by decide

def original1319 : RawOriginal := C010.records[39]'(by decide)
theorem original_id1319 : original1319.index = 1319 := by decide

def c1319 : Contract := original1319.toContract.get (by decide)
theorem binding1319 : original1319.toContract = some c1319 := rfl

theorem checked1319 : check 4000 c1319 = true := by decide

def original1320 : RawOriginal := C010.records[40]'(by decide)
theorem original_id1320 : original1320.index = 1320 := by decide

def c1320 : Contract := original1320.toContract.get (by decide)
theorem binding1320 : original1320.toContract = some c1320 := rfl

theorem checked1320 : check 4000 c1320 = true := by decide

def original1321 : RawOriginal := C010.records[41]'(by decide)
theorem original_id1321 : original1321.index = 1321 := by decide

def c1321 : Contract := original1321.toContract.get (by decide)
theorem binding1321 : original1321.toContract = some c1321 := rfl

theorem checked1321 : check 4000 c1321 = true := by decide

def original1322 : RawOriginal := C010.records[42]'(by decide)
theorem original_id1322 : original1322.index = 1322 := by decide

def c1322 : Contract := original1322.toContract.get (by decide)
theorem binding1322 : original1322.toContract = some c1322 := rfl

theorem checked1322 : check 4000 c1322 = true := by decide

def original1323 : RawOriginal := C010.records[43]'(by decide)
theorem original_id1323 : original1323.index = 1323 := by decide

def c1323 : Contract := original1323.toContract.get (by decide)
theorem binding1323 : original1323.toContract = some c1323 := rfl

theorem checked1323 : check 4000 c1323 = true := by decide

def original1324 : RawOriginal := C010.records[44]'(by decide)
theorem original_id1324 : original1324.index = 1324 := by decide

def c1324 : Contract := original1324.toContract.get (by decide)
theorem binding1324 : original1324.toContract = some c1324 := rfl

theorem checked1324 : check 4000 c1324 = true := by decide

def original1325 : RawOriginal := C010.records[45]'(by decide)
theorem original_id1325 : original1325.index = 1325 := by decide

def c1325 : Contract := original1325.toContract.get (by decide)
theorem binding1325 : original1325.toContract = some c1325 := rfl

theorem checked1325 : check 4000 c1325 = true := by decide

def original1326 : RawOriginal := C010.records[46]'(by decide)
theorem original_id1326 : original1326.index = 1326 := by decide

def c1326 : Contract := original1326.toContract.get (by decide)
theorem binding1326 : original1326.toContract = some c1326 := rfl

theorem checked1326 : check 4000 c1326 = true := by decide

def original1327 : RawOriginal := C010.records[47]'(by decide)
theorem original_id1327 : original1327.index = 1327 := by decide

def c1327 : Contract := original1327.toContract.get (by decide)
theorem binding1327 : original1327.toContract = some c1327 := rfl

theorem checked1327 : check 4000 c1327 = true := by decide

def original1328 : RawOriginal := C010.records[48]'(by decide)
theorem original_id1328 : original1328.index = 1328 := by decide

def c1328 : Contract := original1328.toContract.get (by decide)
theorem binding1328 : original1328.toContract = some c1328 := rfl

theorem checked1328 : check 4000 c1328 = true := by decide

def original1329 : RawOriginal := C010.records[49]'(by decide)
theorem original_id1329 : original1329.index = 1329 := by decide

def c1329 : Contract := original1329.toContract.get (by decide)
theorem binding1329 : original1329.toContract = some c1329 := rfl

theorem checked1329 : check 4000 c1329 = true := by decide

def original1330 : RawOriginal := C010.records[50]'(by decide)
theorem original_id1330 : original1330.index = 1330 := by decide

def c1330 : Contract := original1330.toContract.get (by decide)
theorem binding1330 : original1330.toContract = some c1330 := rfl

theorem checked1330 : check 4000 c1330 = true := by decide

def original1331 : RawOriginal := C010.records[51]'(by decide)
theorem original_id1331 : original1331.index = 1331 := by decide

def c1331 : Contract := original1331.toContract.get (by decide)
theorem binding1331 : original1331.toContract = some c1331 := rfl

theorem checked1331 : check 4000 c1331 = true := by decide

def original1332 : RawOriginal := C010.records[52]'(by decide)
theorem original_id1332 : original1332.index = 1332 := by decide

def c1332 : Contract := original1332.toContract.get (by decide)
theorem binding1332 : original1332.toContract = some c1332 := rfl

theorem checked1332 : check 4000 c1332 = true := by decide

def original1333 : RawOriginal := C010.records[53]'(by decide)
theorem original_id1333 : original1333.index = 1333 := by decide

def c1333 : Contract := original1333.toContract.get (by decide)
theorem binding1333 : original1333.toContract = some c1333 := rfl

theorem checked1333 : check 4000 c1333 = true := by decide

def records : List Certified := [
  ⟨1318, c1318, 4000, checked1318⟩,
  ⟨1319, c1319, 4000, checked1319⟩,
  ⟨1320, c1320, 4000, checked1320⟩,
  ⟨1321, c1321, 4000, checked1321⟩,
  ⟨1322, c1322, 4000, checked1322⟩,
  ⟨1323, c1323, 4000, checked1323⟩,
  ⟨1324, c1324, 4000, checked1324⟩,
  ⟨1325, c1325, 4000, checked1325⟩,
  ⟨1326, c1326, 4000, checked1326⟩,
  ⟨1327, c1327, 4000, checked1327⟩,
  ⟨1328, c1328, 4000, checked1328⟩,
  ⟨1329, c1329, 4000, checked1329⟩,
  ⟨1330, c1330, 4000, checked1330⟩,
  ⟨1331, c1331, 4000, checked1331⟩,
  ⟨1332, c1332, 4000, checked1332⟩,
  ⟨1333, c1333, 4000, checked1333⟩]

end PA215.ContractShards.Shard010Part2
