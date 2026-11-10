import PA215.CertifiedContracts
import PA215.Census.C002
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard002Part5
open PA215.Contracts PA215.Census

def original342 : RawOriginal := C002.records[86]'(by decide)
theorem original_id342 : original342.index = 342 := by decide

def c342 : Contract := original342.toContract.get (by decide)
theorem binding342 : original342.toContract = some c342 := rfl

theorem checked342 : check 4000 c342 = true := by decide

def original343 : RawOriginal := C002.records[87]'(by decide)
theorem original_id343 : original343.index = 343 := by decide

def c343 : Contract := original343.toContract.get (by decide)
theorem binding343 : original343.toContract = some c343 := rfl

theorem checked343 : check 4000 c343 = true := by decide

def original344 : RawOriginal := C002.records[88]'(by decide)
theorem original_id344 : original344.index = 344 := by decide

def c344 : Contract := original344.toContract.get (by decide)
theorem binding344 : original344.toContract = some c344 := rfl

theorem checked344 : check 4000 c344 = true := by decide

def original345 : RawOriginal := C002.records[89]'(by decide)
theorem original_id345 : original345.index = 345 := by decide

def c345 : Contract := original345.toContract.get (by decide)
theorem binding345 : original345.toContract = some c345 := rfl

theorem checked345 : check 4000 c345 = true := by decide

def original346 : RawOriginal := C002.records[90]'(by decide)
theorem original_id346 : original346.index = 346 := by decide

def c346 : Contract := original346.toContract.get (by decide)
theorem binding346 : original346.toContract = some c346 := rfl

theorem checked346 : check 4000 c346 = true := by decide

def original347 : RawOriginal := C002.records[91]'(by decide)
theorem original_id347 : original347.index = 347 := by decide

def c347 : Contract := original347.toContract.get (by decide)
theorem binding347 : original347.toContract = some c347 := rfl

theorem checked347 : check 4000 c347 = true := by decide

def original348 : RawOriginal := C002.records[92]'(by decide)
theorem original_id348 : original348.index = 348 := by decide

def c348 : Contract := original348.toContract.get (by decide)
theorem binding348 : original348.toContract = some c348 := rfl

theorem checked348 : check 4000 c348 = true := by decide

def original349 : RawOriginal := C002.records[93]'(by decide)
theorem original_id349 : original349.index = 349 := by decide

def c349 : Contract := original349.toContract.get (by decide)
theorem binding349 : original349.toContract = some c349 := rfl

theorem checked349 : check 4000 c349 = true := by decide

def original350 : RawOriginal := C002.records[94]'(by decide)
theorem original_id350 : original350.index = 350 := by decide

def c350 : Contract := original350.toContract.get (by decide)
theorem binding350 : original350.toContract = some c350 := rfl

theorem checked350 : check 4000 c350 = true := by decide

def original351 : RawOriginal := C002.records[95]'(by decide)
theorem original_id351 : original351.index = 351 := by decide

def c351 : Contract := original351.toContract.get (by decide)
theorem binding351 : original351.toContract = some c351 := rfl

theorem checked351 : check 4000 c351 = true := by decide

def original352 : RawOriginal := C002.records[96]'(by decide)
theorem original_id352 : original352.index = 352 := by decide

def c352 : Contract := original352.toContract.get (by decide)
theorem binding352 : original352.toContract = some c352 := rfl

theorem checked352 : check 4000 c352 = true := by decide

def original353 : RawOriginal := C002.records[97]'(by decide)
theorem original_id353 : original353.index = 353 := by decide

def c353 : Contract := original353.toContract.get (by decide)
theorem binding353 : original353.toContract = some c353 := rfl

theorem checked353 : check 4000 c353 = true := by decide

def original354 : RawOriginal := C002.records[98]'(by decide)
theorem original_id354 : original354.index = 354 := by decide

def c354 : Contract := original354.toContract.get (by decide)
theorem binding354 : original354.toContract = some c354 := rfl

theorem checked354 : check 4000 c354 = true := by decide

def original355 : RawOriginal := C002.records[99]'(by decide)
theorem original_id355 : original355.index = 355 := by decide

def c355 : Contract := original355.toContract.get (by decide)
theorem binding355 : original355.toContract = some c355 := rfl

theorem checked355 : check 4000 c355 = true := by decide

def original356 : RawOriginal := C002.records[100]'(by decide)
theorem original_id356 : original356.index = 356 := by decide

def c356 : Contract := original356.toContract.get (by decide)
theorem binding356 : original356.toContract = some c356 := rfl

theorem checked356 : check 4000 c356 = true := by decide

def original357 : RawOriginal := C002.records[101]'(by decide)
theorem original_id357 : original357.index = 357 := by decide

def c357 : Contract := original357.toContract.get (by decide)
theorem binding357 : original357.toContract = some c357 := rfl

theorem checked357 : check 4000 c357 = true := by decide

def records : List Certified := [
  ⟨342, c342, 4000, checked342⟩,
  ⟨343, c343, 4000, checked343⟩,
  ⟨344, c344, 4000, checked344⟩,
  ⟨345, c345, 4000, checked345⟩,
  ⟨346, c346, 4000, checked346⟩,
  ⟨347, c347, 4000, checked347⟩,
  ⟨348, c348, 4000, checked348⟩,
  ⟨349, c349, 4000, checked349⟩,
  ⟨350, c350, 4000, checked350⟩,
  ⟨351, c351, 4000, checked351⟩,
  ⟨352, c352, 4000, checked352⟩,
  ⟨353, c353, 4000, checked353⟩,
  ⟨354, c354, 4000, checked354⟩,
  ⟨355, c355, 4000, checked355⟩,
  ⟨356, c356, 4000, checked356⟩,
  ⟨357, c357, 4000, checked357⟩]

end PA215.ContractShards.Shard002Part5
