import PA215.CertifiedContracts
import PA215.Census.C010
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard010Part3
open PA215.Contracts PA215.Census

def original1334 : RawOriginal := C010.records[54]'(by decide)
theorem original_id1334 : original1334.index = 1334 := by decide

def c1334 : Contract := original1334.toContract.get (by decide)
theorem binding1334 : original1334.toContract = some c1334 := rfl

theorem checked1334 : check 4000 c1334 = true := by decide

def original1335 : RawOriginal := C010.records[55]'(by decide)
theorem original_id1335 : original1335.index = 1335 := by decide

def c1335 : Contract := original1335.toContract.get (by decide)
theorem binding1335 : original1335.toContract = some c1335 := rfl

theorem checked1335 : check 4000 c1335 = true := by decide

def original1336 : RawOriginal := C010.records[56]'(by decide)
theorem original_id1336 : original1336.index = 1336 := by decide

def c1336 : Contract := original1336.toContract.get (by decide)
theorem binding1336 : original1336.toContract = some c1336 := rfl

theorem checked1336 : check 4000 c1336 = true := by decide

def original1337 : RawOriginal := C010.records[57]'(by decide)
theorem original_id1337 : original1337.index = 1337 := by decide

def c1337 : Contract := original1337.toContract.get (by decide)
theorem binding1337 : original1337.toContract = some c1337 := rfl

theorem checked1337 : check 4000 c1337 = true := by decide

def original1338 : RawOriginal := C010.records[58]'(by decide)
theorem original_id1338 : original1338.index = 1338 := by decide

def c1338 : Contract := original1338.toContract.get (by decide)
theorem binding1338 : original1338.toContract = some c1338 := rfl

theorem checked1338 : check 4000 c1338 = true := by decide

def original1339 : RawOriginal := C010.records[59]'(by decide)
theorem original_id1339 : original1339.index = 1339 := by decide

def c1339 : Contract := original1339.toContract.get (by decide)
theorem binding1339 : original1339.toContract = some c1339 := rfl

theorem checked1339 : check 4000 c1339 = true := by decide

def original1340 : RawOriginal := C010.records[60]'(by decide)
theorem original_id1340 : original1340.index = 1340 := by decide

def c1340 : Contract := original1340.toContract.get (by decide)
theorem binding1340 : original1340.toContract = some c1340 := rfl

theorem checked1340 : check 4000 c1340 = true := by decide

def original1341 : RawOriginal := C010.records[61]'(by decide)
theorem original_id1341 : original1341.index = 1341 := by decide

def c1341 : Contract := original1341.toContract.get (by decide)
theorem binding1341 : original1341.toContract = some c1341 := rfl

theorem checked1341 : check 4000 c1341 = true := by decide

def original1342 : RawOriginal := C010.records[62]'(by decide)
theorem original_id1342 : original1342.index = 1342 := by decide

def c1342 : Contract := original1342.toContract.get (by decide)
theorem binding1342 : original1342.toContract = some c1342 := rfl

theorem checked1342 : check 4000 c1342 = true := by decide

def original1343 : RawOriginal := C010.records[63]'(by decide)
theorem original_id1343 : original1343.index = 1343 := by decide

def c1343 : Contract := original1343.toContract.get (by decide)
theorem binding1343 : original1343.toContract = some c1343 := rfl

theorem checked1343 : check 4000 c1343 = true := by decide

def original1344 : RawOriginal := C010.records[64]'(by decide)
theorem original_id1344 : original1344.index = 1344 := by decide

def c1344 : Contract := original1344.toContract.get (by decide)
theorem binding1344 : original1344.toContract = some c1344 := rfl

theorem checked1344 : check 4000 c1344 = true := by decide

def original1345 : RawOriginal := C010.records[65]'(by decide)
theorem original_id1345 : original1345.index = 1345 := by decide

def c1345 : Contract := original1345.toContract.get (by decide)
theorem binding1345 : original1345.toContract = some c1345 := rfl

theorem checked1345 : check 4000 c1345 = true := by decide

def original1346 : RawOriginal := C010.records[66]'(by decide)
theorem original_id1346 : original1346.index = 1346 := by decide

def c1346 : Contract := original1346.toContract.get (by decide)
theorem binding1346 : original1346.toContract = some c1346 := rfl

theorem checked1346 : check 4000 c1346 = true := by decide

def original1347 : RawOriginal := C010.records[67]'(by decide)
theorem original_id1347 : original1347.index = 1347 := by decide

def c1347 : Contract := original1347.toContract.get (by decide)
theorem binding1347 : original1347.toContract = some c1347 := rfl

theorem checked1347 : check 4000 c1347 = true := by decide

def original1348 : RawOriginal := C010.records[68]'(by decide)
theorem original_id1348 : original1348.index = 1348 := by decide

def c1348 : Contract := original1348.toContract.get (by decide)
theorem binding1348 : original1348.toContract = some c1348 := rfl

theorem checked1348 : check 4000 c1348 = true := by decide

def original1349 : RawOriginal := C010.records[69]'(by decide)
theorem original_id1349 : original1349.index = 1349 := by decide

def c1349 : Contract := original1349.toContract.get (by decide)
theorem binding1349 : original1349.toContract = some c1349 := rfl

theorem checked1349 : check 4000 c1349 = true := by decide

def records : List Certified := [
  ⟨1334, c1334, 4000, checked1334⟩,
  ⟨1335, c1335, 4000, checked1335⟩,
  ⟨1336, c1336, 4000, checked1336⟩,
  ⟨1337, c1337, 4000, checked1337⟩,
  ⟨1338, c1338, 4000, checked1338⟩,
  ⟨1339, c1339, 4000, checked1339⟩,
  ⟨1340, c1340, 4000, checked1340⟩,
  ⟨1341, c1341, 4000, checked1341⟩,
  ⟨1342, c1342, 4000, checked1342⟩,
  ⟨1343, c1343, 4000, checked1343⟩,
  ⟨1344, c1344, 4000, checked1344⟩,
  ⟨1345, c1345, 4000, checked1345⟩,
  ⟨1346, c1346, 4000, checked1346⟩,
  ⟨1347, c1347, 4000, checked1347⟩,
  ⟨1348, c1348, 4000, checked1348⟩,
  ⟨1349, c1349, 4000, checked1349⟩]

end PA215.ContractShards.Shard010Part3
