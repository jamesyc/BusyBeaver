import PA215.CertifiedContracts
import PA215.Census.C002
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard002Part4
open PA215.Contracts PA215.Census

def original326 : RawOriginal := C002.records[70]'(by decide)
theorem original_id326 : original326.index = 326 := by decide

def c326 : Contract := original326.toContract.get (by decide)
theorem binding326 : original326.toContract = some c326 := rfl

theorem checked326 : check 4000 c326 = true := by decide

def original327 : RawOriginal := C002.records[71]'(by decide)
theorem original_id327 : original327.index = 327 := by decide

def c327 : Contract := original327.toContract.get (by decide)
theorem binding327 : original327.toContract = some c327 := rfl

theorem checked327 : check 4000 c327 = true := by decide

def original328 : RawOriginal := C002.records[72]'(by decide)
theorem original_id328 : original328.index = 328 := by decide

def c328 : Contract := original328.toContract.get (by decide)
theorem binding328 : original328.toContract = some c328 := rfl

theorem checked328 : check 4000 c328 = true := by decide

def original329 : RawOriginal := C002.records[73]'(by decide)
theorem original_id329 : original329.index = 329 := by decide

def c329 : Contract := original329.toContract.get (by decide)
theorem binding329 : original329.toContract = some c329 := rfl

theorem checked329 : check 4000 c329 = true := by decide

def original330 : RawOriginal := C002.records[74]'(by decide)
theorem original_id330 : original330.index = 330 := by decide

def c330 : Contract := original330.toContract.get (by decide)
theorem binding330 : original330.toContract = some c330 := rfl

theorem checked330 : check 4000 c330 = true := by decide

def original331 : RawOriginal := C002.records[75]'(by decide)
theorem original_id331 : original331.index = 331 := by decide

def c331 : Contract := original331.toContract.get (by decide)
theorem binding331 : original331.toContract = some c331 := rfl

theorem checked331 : check 4000 c331 = true := by decide

def original332 : RawOriginal := C002.records[76]'(by decide)
theorem original_id332 : original332.index = 332 := by decide

def c332 : Contract := original332.toContract.get (by decide)
theorem binding332 : original332.toContract = some c332 := rfl

theorem checked332 : check 4000 c332 = true := by decide

def original333 : RawOriginal := C002.records[77]'(by decide)
theorem original_id333 : original333.index = 333 := by decide

def c333 : Contract := original333.toContract.get (by decide)
theorem binding333 : original333.toContract = some c333 := rfl

theorem checked333 : check 4000 c333 = true := by decide

def original334 : RawOriginal := C002.records[78]'(by decide)
theorem original_id334 : original334.index = 334 := by decide

def c334 : Contract := original334.toContract.get (by decide)
theorem binding334 : original334.toContract = some c334 := rfl

theorem checked334 : check 4000 c334 = true := by decide

def original335 : RawOriginal := C002.records[79]'(by decide)
theorem original_id335 : original335.index = 335 := by decide

def c335 : Contract := original335.toContract.get (by decide)
theorem binding335 : original335.toContract = some c335 := rfl

theorem checked335 : check 4000 c335 = true := by decide

def original336 : RawOriginal := C002.records[80]'(by decide)
theorem original_id336 : original336.index = 336 := by decide

def c336 : Contract := original336.toContract.get (by decide)
theorem binding336 : original336.toContract = some c336 := rfl

theorem checked336 : check 4000 c336 = true := by decide

def original337 : RawOriginal := C002.records[81]'(by decide)
theorem original_id337 : original337.index = 337 := by decide

def c337 : Contract := original337.toContract.get (by decide)
theorem binding337 : original337.toContract = some c337 := rfl

theorem checked337 : check 4000 c337 = true := by decide

def original338 : RawOriginal := C002.records[82]'(by decide)
theorem original_id338 : original338.index = 338 := by decide

def c338 : Contract := original338.toContract.get (by decide)
theorem binding338 : original338.toContract = some c338 := rfl

theorem checked338 : check 4000 c338 = true := by decide

def original339 : RawOriginal := C002.records[83]'(by decide)
theorem original_id339 : original339.index = 339 := by decide

def c339 : Contract := original339.toContract.get (by decide)
theorem binding339 : original339.toContract = some c339 := rfl

theorem checked339 : check 4000 c339 = true := by decide

def original340 : RawOriginal := C002.records[84]'(by decide)
theorem original_id340 : original340.index = 340 := by decide

def c340 : Contract := original340.toContract.get (by decide)
theorem binding340 : original340.toContract = some c340 := rfl

theorem checked340 : check 4000 c340 = true := by decide

def original341 : RawOriginal := C002.records[85]'(by decide)
theorem original_id341 : original341.index = 341 := by decide

def c341 : Contract := original341.toContract.get (by decide)
theorem binding341 : original341.toContract = some c341 := rfl

theorem checked341 : check 4000 c341 = true := by decide

def records : List Certified := [
  ⟨326, c326, 4000, checked326⟩,
  ⟨327, c327, 4000, checked327⟩,
  ⟨328, c328, 4000, checked328⟩,
  ⟨329, c329, 4000, checked329⟩,
  ⟨330, c330, 4000, checked330⟩,
  ⟨331, c331, 4000, checked331⟩,
  ⟨332, c332, 4000, checked332⟩,
  ⟨333, c333, 4000, checked333⟩,
  ⟨334, c334, 4000, checked334⟩,
  ⟨335, c335, 4000, checked335⟩,
  ⟨336, c336, 4000, checked336⟩,
  ⟨337, c337, 4000, checked337⟩,
  ⟨338, c338, 4000, checked338⟩,
  ⟨339, c339, 4000, checked339⟩,
  ⟨340, c340, 4000, checked340⟩,
  ⟨341, c341, 4000, checked341⟩]

end PA215.ContractShards.Shard002Part4
