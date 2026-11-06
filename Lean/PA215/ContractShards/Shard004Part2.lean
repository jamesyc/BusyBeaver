import PA215.CertifiedContracts
import PA215.Census.C004
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard004Part2
open PA215.Contracts PA215.Census

def original550 : RawOriginal := C004.records[38]'(by decide)
theorem original_id550 : original550.index = 550 := by decide

def c550 : Contract := original550.toContract.get (by decide)
theorem binding550 : original550.toContract = some c550 := rfl

theorem checked550 : check 4000 c550 = true := by decide

def original551 : RawOriginal := C004.records[39]'(by decide)
theorem original_id551 : original551.index = 551 := by decide

def c551 : Contract := original551.toContract.get (by decide)
theorem binding551 : original551.toContract = some c551 := rfl

theorem checked551 : check 4000 c551 = true := by decide

def original552 : RawOriginal := C004.records[40]'(by decide)
theorem original_id552 : original552.index = 552 := by decide

def c552 : Contract := original552.toContract.get (by decide)
theorem binding552 : original552.toContract = some c552 := rfl

theorem checked552 : check 4000 c552 = true := by decide

def original553 : RawOriginal := C004.records[41]'(by decide)
theorem original_id553 : original553.index = 553 := by decide

def c553 : Contract := original553.toContract.get (by decide)
theorem binding553 : original553.toContract = some c553 := rfl

theorem checked553 : check 4000 c553 = true := by decide

def original554 : RawOriginal := C004.records[42]'(by decide)
theorem original_id554 : original554.index = 554 := by decide

def c554 : Contract := original554.toContract.get (by decide)
theorem binding554 : original554.toContract = some c554 := rfl

theorem checked554 : check 4000 c554 = true := by decide

def original555 : RawOriginal := C004.records[43]'(by decide)
theorem original_id555 : original555.index = 555 := by decide

def c555 : Contract := original555.toContract.get (by decide)
theorem binding555 : original555.toContract = some c555 := rfl

theorem checked555 : check 4000 c555 = true := by decide

def original556 : RawOriginal := C004.records[44]'(by decide)
theorem original_id556 : original556.index = 556 := by decide

def c556 : Contract := original556.toContract.get (by decide)
theorem binding556 : original556.toContract = some c556 := rfl

theorem checked556 : check 4000 c556 = true := by decide

def original557 : RawOriginal := C004.records[45]'(by decide)
theorem original_id557 : original557.index = 557 := by decide

def c557 : Contract := original557.toContract.get (by decide)
theorem binding557 : original557.toContract = some c557 := rfl

theorem checked557 : check 4000 c557 = true := by decide

def original558 : RawOriginal := C004.records[46]'(by decide)
theorem original_id558 : original558.index = 558 := by decide

def c558 : Contract := original558.toContract.get (by decide)
theorem binding558 : original558.toContract = some c558 := rfl

theorem checked558 : check 4000 c558 = true := by decide

def original559 : RawOriginal := C004.records[47]'(by decide)
theorem original_id559 : original559.index = 559 := by decide

def c559 : Contract := original559.toContract.get (by decide)
theorem binding559 : original559.toContract = some c559 := rfl

theorem checked559 : check 4000 c559 = true := by decide

def original560 : RawOriginal := C004.records[48]'(by decide)
theorem original_id560 : original560.index = 560 := by decide

def c560 : Contract := original560.toContract.get (by decide)
theorem binding560 : original560.toContract = some c560 := rfl

theorem checked560 : check 4000 c560 = true := by decide

def original561 : RawOriginal := C004.records[49]'(by decide)
theorem original_id561 : original561.index = 561 := by decide

def c561 : Contract := original561.toContract.get (by decide)
theorem binding561 : original561.toContract = some c561 := rfl

theorem checked561 : check 4000 c561 = true := by decide

def original562 : RawOriginal := C004.records[50]'(by decide)
theorem original_id562 : original562.index = 562 := by decide

def c562 : Contract := original562.toContract.get (by decide)
theorem binding562 : original562.toContract = some c562 := rfl

theorem checked562 : check 4000 c562 = true := by decide

def original563 : RawOriginal := C004.records[51]'(by decide)
theorem original_id563 : original563.index = 563 := by decide

def c563 : Contract := original563.toContract.get (by decide)
theorem binding563 : original563.toContract = some c563 := rfl

theorem checked563 : check 4000 c563 = true := by decide

def original564 : RawOriginal := C004.records[52]'(by decide)
theorem original_id564 : original564.index = 564 := by decide

def c564 : Contract := original564.toContract.get (by decide)
theorem binding564 : original564.toContract = some c564 := rfl

theorem checked564 : check 4000 c564 = true := by decide

def original565 : RawOriginal := C004.records[53]'(by decide)
theorem original_id565 : original565.index = 565 := by decide

def c565 : Contract := original565.toContract.get (by decide)
theorem binding565 : original565.toContract = some c565 := rfl

theorem checked565 : check 4000 c565 = true := by decide

def records : List Certified := [
  ⟨550, c550, 4000, checked550⟩,
  ⟨551, c551, 4000, checked551⟩,
  ⟨552, c552, 4000, checked552⟩,
  ⟨553, c553, 4000, checked553⟩,
  ⟨554, c554, 4000, checked554⟩,
  ⟨555, c555, 4000, checked555⟩,
  ⟨556, c556, 4000, checked556⟩,
  ⟨557, c557, 4000, checked557⟩,
  ⟨558, c558, 4000, checked558⟩,
  ⟨559, c559, 4000, checked559⟩,
  ⟨560, c560, 4000, checked560⟩,
  ⟨561, c561, 4000, checked561⟩,
  ⟨562, c562, 4000, checked562⟩,
  ⟨563, c563, 4000, checked563⟩,
  ⟨564, c564, 4000, checked564⟩,
  ⟨565, c565, 4000, checked565⟩]

end PA215.ContractShards.Shard004Part2
