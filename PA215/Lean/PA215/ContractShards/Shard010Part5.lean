import PA215.CertifiedContracts
import PA215.Census.C010
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard010Part5
open PA215.Contracts PA215.Census

def original1366 : RawOriginal := C010.records[86]'(by decide)
theorem original_id1366 : original1366.index = 1366 := by decide

def c1366 : Contract := original1366.toContract.get (by decide)
theorem binding1366 : original1366.toContract = some c1366 := rfl

theorem checked1366 : check 4000 c1366 = true := by decide

def original1367 : RawOriginal := C010.records[87]'(by decide)
theorem original_id1367 : original1367.index = 1367 := by decide

def c1367 : Contract := original1367.toContract.get (by decide)
theorem binding1367 : original1367.toContract = some c1367 := rfl

theorem checked1367 : check 4000 c1367 = true := by decide

def original1368 : RawOriginal := C010.records[88]'(by decide)
theorem original_id1368 : original1368.index = 1368 := by decide

def c1368 : Contract := original1368.toContract.get (by decide)
theorem binding1368 : original1368.toContract = some c1368 := rfl

theorem checked1368 : check 4000 c1368 = true := by decide

def original1369 : RawOriginal := C010.records[89]'(by decide)
theorem original_id1369 : original1369.index = 1369 := by decide

def c1369 : Contract := original1369.toContract.get (by decide)
theorem binding1369 : original1369.toContract = some c1369 := rfl

theorem checked1369 : check 4000 c1369 = true := by decide

def original1370 : RawOriginal := C010.records[90]'(by decide)
theorem original_id1370 : original1370.index = 1370 := by decide

def c1370 : Contract := original1370.toContract.get (by decide)
theorem binding1370 : original1370.toContract = some c1370 := rfl

theorem checked1370 : check 4000 c1370 = true := by decide

def original1371 : RawOriginal := C010.records[91]'(by decide)
theorem original_id1371 : original1371.index = 1371 := by decide

def c1371 : Contract := original1371.toContract.get (by decide)
theorem binding1371 : original1371.toContract = some c1371 := rfl

theorem checked1371 : check 4000 c1371 = true := by decide

def original1372 : RawOriginal := C010.records[92]'(by decide)
theorem original_id1372 : original1372.index = 1372 := by decide

def c1372 : Contract := original1372.toContract.get (by decide)
theorem binding1372 : original1372.toContract = some c1372 := rfl

theorem checked1372 : check 4000 c1372 = true := by decide

def original1373 : RawOriginal := C010.records[93]'(by decide)
theorem original_id1373 : original1373.index = 1373 := by decide

def c1373 : Contract := original1373.toContract.get (by decide)
theorem binding1373 : original1373.toContract = some c1373 := rfl

theorem checked1373 : check 4000 c1373 = true := by decide

def original1374 : RawOriginal := C010.records[94]'(by decide)
theorem original_id1374 : original1374.index = 1374 := by decide

def c1374 : Contract := original1374.toContract.get (by decide)
theorem binding1374 : original1374.toContract = some c1374 := rfl

theorem checked1374 : check 4000 c1374 = true := by decide

def original1375 : RawOriginal := C010.records[95]'(by decide)
theorem original_id1375 : original1375.index = 1375 := by decide

def c1375 : Contract := original1375.toContract.get (by decide)
theorem binding1375 : original1375.toContract = some c1375 := rfl

theorem checked1375 : check 4000 c1375 = true := by decide

def original1376 : RawOriginal := C010.records[96]'(by decide)
theorem original_id1376 : original1376.index = 1376 := by decide

def c1376 : Contract := original1376.toContract.get (by decide)
theorem binding1376 : original1376.toContract = some c1376 := rfl

theorem checked1376 : check 4000 c1376 = true := by decide

def original1377 : RawOriginal := C010.records[97]'(by decide)
theorem original_id1377 : original1377.index = 1377 := by decide

def c1377 : Contract := original1377.toContract.get (by decide)
theorem binding1377 : original1377.toContract = some c1377 := rfl

theorem checked1377 : check 4000 c1377 = true := by decide

def original1378 : RawOriginal := C010.records[98]'(by decide)
theorem original_id1378 : original1378.index = 1378 := by decide

def c1378 : Contract := original1378.toContract.get (by decide)
theorem binding1378 : original1378.toContract = some c1378 := rfl

theorem checked1378 : check 4000 c1378 = true := by decide

def original1379 : RawOriginal := C010.records[99]'(by decide)
theorem original_id1379 : original1379.index = 1379 := by decide

def c1379 : Contract := original1379.toContract.get (by decide)
theorem binding1379 : original1379.toContract = some c1379 := rfl

theorem checked1379 : check 4000 c1379 = true := by decide

def original1380 : RawOriginal := C010.records[100]'(by decide)
theorem original_id1380 : original1380.index = 1380 := by decide

def c1380 : Contract := original1380.toContract.get (by decide)
theorem binding1380 : original1380.toContract = some c1380 := rfl

theorem checked1380 : check 4000 c1380 = true := by decide

def original1381 : RawOriginal := C010.records[101]'(by decide)
theorem original_id1381 : original1381.index = 1381 := by decide

def c1381 : Contract := original1381.toContract.get (by decide)
theorem binding1381 : original1381.toContract = some c1381 := rfl

theorem checked1381 : check 4000 c1381 = true := by decide

def records : List Certified := [
  ⟨1366, c1366, 4000, checked1366⟩,
  ⟨1367, c1367, 4000, checked1367⟩,
  ⟨1368, c1368, 4000, checked1368⟩,
  ⟨1369, c1369, 4000, checked1369⟩,
  ⟨1370, c1370, 4000, checked1370⟩,
  ⟨1371, c1371, 4000, checked1371⟩,
  ⟨1372, c1372, 4000, checked1372⟩,
  ⟨1373, c1373, 4000, checked1373⟩,
  ⟨1374, c1374, 4000, checked1374⟩,
  ⟨1375, c1375, 4000, checked1375⟩,
  ⟨1376, c1376, 4000, checked1376⟩,
  ⟨1377, c1377, 4000, checked1377⟩,
  ⟨1378, c1378, 4000, checked1378⟩,
  ⟨1379, c1379, 4000, checked1379⟩,
  ⟨1380, c1380, 4000, checked1380⟩,
  ⟨1381, c1381, 4000, checked1381⟩]

end PA215.ContractShards.Shard010Part5
