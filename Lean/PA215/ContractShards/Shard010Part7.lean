import PA215.CertifiedContracts
import PA215.Census.C010
import PA215.Census.C011
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard010Part7
open PA215.Contracts PA215.Census

def original1398 : RawOriginal := C010.records[118]'(by decide)
theorem original_id1398 : original1398.index = 1398 := by decide

def c1398 : Contract := original1398.toContract.get (by decide)
theorem binding1398 : original1398.toContract = some c1398 := rfl

theorem checked1398 : check 4000 c1398 = true := by decide

def original1399 : RawOriginal := C010.records[119]'(by decide)
theorem original_id1399 : original1399.index = 1399 := by decide

def c1399 : Contract := original1399.toContract.get (by decide)
theorem binding1399 : original1399.toContract = some c1399 := rfl

theorem checked1399 : check 4000 c1399 = true := by decide

def original1400 : RawOriginal := C010.records[120]'(by decide)
theorem original_id1400 : original1400.index = 1400 := by decide

def c1400 : Contract := original1400.toContract.get (by decide)
theorem binding1400 : original1400.toContract = some c1400 := rfl

theorem checked1400 : check 4000 c1400 = true := by decide

def original1401 : RawOriginal := C010.records[121]'(by decide)
theorem original_id1401 : original1401.index = 1401 := by decide

def c1401 : Contract := original1401.toContract.get (by decide)
theorem binding1401 : original1401.toContract = some c1401 := rfl

theorem checked1401 : check 4000 c1401 = true := by decide

def original1402 : RawOriginal := C010.records[122]'(by decide)
theorem original_id1402 : original1402.index = 1402 := by decide

def c1402 : Contract := original1402.toContract.get (by decide)
theorem binding1402 : original1402.toContract = some c1402 := rfl

theorem checked1402 : check 4000 c1402 = true := by decide

def original1403 : RawOriginal := C010.records[123]'(by decide)
theorem original_id1403 : original1403.index = 1403 := by decide

def c1403 : Contract := original1403.toContract.get (by decide)
theorem binding1403 : original1403.toContract = some c1403 := rfl

theorem checked1403 : check 4000 c1403 = true := by decide

def original1404 : RawOriginal := C010.records[124]'(by decide)
theorem original_id1404 : original1404.index = 1404 := by decide

def c1404 : Contract := original1404.toContract.get (by decide)
theorem binding1404 : original1404.toContract = some c1404 := rfl

theorem checked1404 : check 4000 c1404 = true := by decide

def original1405 : RawOriginal := C010.records[125]'(by decide)
theorem original_id1405 : original1405.index = 1405 := by decide

def c1405 : Contract := original1405.toContract.get (by decide)
theorem binding1405 : original1405.toContract = some c1405 := rfl

theorem checked1405 : check 4000 c1405 = true := by decide

def original1406 : RawOriginal := C010.records[126]'(by decide)
theorem original_id1406 : original1406.index = 1406 := by decide

def c1406 : Contract := original1406.toContract.get (by decide)
theorem binding1406 : original1406.toContract = some c1406 := rfl

theorem checked1406 : check 4000 c1406 = true := by decide

def original1407 : RawOriginal := C010.records[127]'(by decide)
theorem original_id1407 : original1407.index = 1407 := by decide

def c1407 : Contract := original1407.toContract.get (by decide)
theorem binding1407 : original1407.toContract = some c1407 := rfl

theorem checked1407 : check 4000 c1407 = true := by decide

def original1408 : RawOriginal := C011.records[0]'(by decide)
theorem original_id1408 : original1408.index = 1408 := by decide

def c1408 : Contract := original1408.toContract.get (by decide)
theorem binding1408 : original1408.toContract = some c1408 := rfl

theorem checked1408 : check 4000 c1408 = true := by decide

def original1409 : RawOriginal := C011.records[1]'(by decide)
theorem original_id1409 : original1409.index = 1409 := by decide

def c1409 : Contract := original1409.toContract.get (by decide)
theorem binding1409 : original1409.toContract = some c1409 := rfl

theorem checked1409 : check 4000 c1409 = true := by decide

def original1410 : RawOriginal := C011.records[2]'(by decide)
theorem original_id1410 : original1410.index = 1410 := by decide

def c1410 : Contract := original1410.toContract.get (by decide)
theorem binding1410 : original1410.toContract = some c1410 := rfl

theorem checked1410 : check 4000 c1410 = true := by decide

def original1411 : RawOriginal := C011.records[3]'(by decide)
theorem original_id1411 : original1411.index = 1411 := by decide

def c1411 : Contract := original1411.toContract.get (by decide)
theorem binding1411 : original1411.toContract = some c1411 := rfl

theorem checked1411 : check 4000 c1411 = true := by decide

def original1412 : RawOriginal := C011.records[4]'(by decide)
theorem original_id1412 : original1412.index = 1412 := by decide

def c1412 : Contract := original1412.toContract.get (by decide)
theorem binding1412 : original1412.toContract = some c1412 := rfl

theorem checked1412 : check 4000 c1412 = true := by decide

def original1413 : RawOriginal := C011.records[5]'(by decide)
theorem original_id1413 : original1413.index = 1413 := by decide

def c1413 : Contract := original1413.toContract.get (by decide)
theorem binding1413 : original1413.toContract = some c1413 := rfl

theorem checked1413 : check 4000 c1413 = true := by decide

def records : List Certified := [
  ⟨1398, c1398, 4000, checked1398⟩,
  ⟨1399, c1399, 4000, checked1399⟩,
  ⟨1400, c1400, 4000, checked1400⟩,
  ⟨1401, c1401, 4000, checked1401⟩,
  ⟨1402, c1402, 4000, checked1402⟩,
  ⟨1403, c1403, 4000, checked1403⟩,
  ⟨1404, c1404, 4000, checked1404⟩,
  ⟨1405, c1405, 4000, checked1405⟩,
  ⟨1406, c1406, 4000, checked1406⟩,
  ⟨1407, c1407, 4000, checked1407⟩,
  ⟨1408, c1408, 4000, checked1408⟩,
  ⟨1409, c1409, 4000, checked1409⟩,
  ⟨1410, c1410, 4000, checked1410⟩,
  ⟨1411, c1411, 4000, checked1411⟩,
  ⟨1412, c1412, 4000, checked1412⟩,
  ⟨1413, c1413, 4000, checked1413⟩]

end PA215.ContractShards.Shard010Part7
