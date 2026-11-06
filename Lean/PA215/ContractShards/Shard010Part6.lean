import PA215.CertifiedContracts
import PA215.Census.C010
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard010Part6
open PA215.Contracts PA215.Census

def original1382 : RawOriginal := C010.records[102]'(by decide)
theorem original_id1382 : original1382.index = 1382 := by decide

def c1382 : Contract := original1382.toContract.get (by decide)
theorem binding1382 : original1382.toContract = some c1382 := rfl

theorem checked1382 : check 4000 c1382 = true := by decide

def original1383 : RawOriginal := C010.records[103]'(by decide)
theorem original_id1383 : original1383.index = 1383 := by decide

def c1383 : Contract := original1383.toContract.get (by decide)
theorem binding1383 : original1383.toContract = some c1383 := rfl

theorem checked1383 : check 4000 c1383 = true := by decide

def original1384 : RawOriginal := C010.records[104]'(by decide)
theorem original_id1384 : original1384.index = 1384 := by decide

def c1384 : Contract := original1384.toContract.get (by decide)
theorem binding1384 : original1384.toContract = some c1384 := rfl

theorem checked1384 : check 4000 c1384 = true := by decide

def original1385 : RawOriginal := C010.records[105]'(by decide)
theorem original_id1385 : original1385.index = 1385 := by decide

def c1385 : Contract := original1385.toContract.get (by decide)
theorem binding1385 : original1385.toContract = some c1385 := rfl

theorem checked1385 : check 4000 c1385 = true := by decide

def original1386 : RawOriginal := C010.records[106]'(by decide)
theorem original_id1386 : original1386.index = 1386 := by decide

def c1386 : Contract := original1386.toContract.get (by decide)
theorem binding1386 : original1386.toContract = some c1386 := rfl

theorem checked1386 : check 4000 c1386 = true := by decide

def original1387 : RawOriginal := C010.records[107]'(by decide)
theorem original_id1387 : original1387.index = 1387 := by decide

def c1387 : Contract := original1387.toContract.get (by decide)
theorem binding1387 : original1387.toContract = some c1387 := rfl

theorem checked1387 : check 4000 c1387 = true := by decide

def original1388 : RawOriginal := C010.records[108]'(by decide)
theorem original_id1388 : original1388.index = 1388 := by decide

def c1388 : Contract := original1388.toContract.get (by decide)
theorem binding1388 : original1388.toContract = some c1388 := rfl

theorem checked1388 : check 4000 c1388 = true := by decide

def original1389 : RawOriginal := C010.records[109]'(by decide)
theorem original_id1389 : original1389.index = 1389 := by decide

def c1389 : Contract := original1389.toContract.get (by decide)
theorem binding1389 : original1389.toContract = some c1389 := rfl

theorem checked1389 : check 4000 c1389 = true := by decide

def original1390 : RawOriginal := C010.records[110]'(by decide)
theorem original_id1390 : original1390.index = 1390 := by decide

def c1390 : Contract := original1390.toContract.get (by decide)
theorem binding1390 : original1390.toContract = some c1390 := rfl

theorem checked1390 : check 4000 c1390 = true := by decide

def original1391 : RawOriginal := C010.records[111]'(by decide)
theorem original_id1391 : original1391.index = 1391 := by decide

def c1391 : Contract := original1391.toContract.get (by decide)
theorem binding1391 : original1391.toContract = some c1391 := rfl

theorem checked1391 : check 4000 c1391 = true := by decide

def original1392 : RawOriginal := C010.records[112]'(by decide)
theorem original_id1392 : original1392.index = 1392 := by decide

def c1392 : Contract := original1392.toContract.get (by decide)
theorem binding1392 : original1392.toContract = some c1392 := rfl

theorem checked1392 : check 4000 c1392 = true := by decide

def original1393 : RawOriginal := C010.records[113]'(by decide)
theorem original_id1393 : original1393.index = 1393 := by decide

def c1393 : Contract := original1393.toContract.get (by decide)
theorem binding1393 : original1393.toContract = some c1393 := rfl

theorem checked1393 : check 4000 c1393 = true := by decide

def original1394 : RawOriginal := C010.records[114]'(by decide)
theorem original_id1394 : original1394.index = 1394 := by decide

def c1394 : Contract := original1394.toContract.get (by decide)
theorem binding1394 : original1394.toContract = some c1394 := rfl

theorem checked1394 : check 4000 c1394 = true := by decide

def original1395 : RawOriginal := C010.records[115]'(by decide)
theorem original_id1395 : original1395.index = 1395 := by decide

def c1395 : Contract := original1395.toContract.get (by decide)
theorem binding1395 : original1395.toContract = some c1395 := rfl

theorem checked1395 : check 4000 c1395 = true := by decide

def original1396 : RawOriginal := C010.records[116]'(by decide)
theorem original_id1396 : original1396.index = 1396 := by decide

def c1396 : Contract := original1396.toContract.get (by decide)
theorem binding1396 : original1396.toContract = some c1396 := rfl

theorem checked1396 : check 4000 c1396 = true := by decide

def original1397 : RawOriginal := C010.records[117]'(by decide)
theorem original_id1397 : original1397.index = 1397 := by decide

def c1397 : Contract := original1397.toContract.get (by decide)
theorem binding1397 : original1397.toContract = some c1397 := rfl

theorem checked1397 : check 4000 c1397 = true := by decide

def records : List Certified := [
  ⟨1382, c1382, 4000, checked1382⟩,
  ⟨1383, c1383, 4000, checked1383⟩,
  ⟨1384, c1384, 4000, checked1384⟩,
  ⟨1385, c1385, 4000, checked1385⟩,
  ⟨1386, c1386, 4000, checked1386⟩,
  ⟨1387, c1387, 4000, checked1387⟩,
  ⟨1388, c1388, 4000, checked1388⟩,
  ⟨1389, c1389, 4000, checked1389⟩,
  ⟨1390, c1390, 4000, checked1390⟩,
  ⟨1391, c1391, 4000, checked1391⟩,
  ⟨1392, c1392, 4000, checked1392⟩,
  ⟨1393, c1393, 4000, checked1393⟩,
  ⟨1394, c1394, 4000, checked1394⟩,
  ⟨1395, c1395, 4000, checked1395⟩,
  ⟨1396, c1396, 4000, checked1396⟩,
  ⟨1397, c1397, 4000, checked1397⟩]

end PA215.ContractShards.Shard010Part6
