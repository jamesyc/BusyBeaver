import PA215.CertifiedContracts
import PA215.Census.C002
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard002Part6
open PA215.Contracts PA215.Census

def original358 : RawOriginal := C002.records[102]'(by decide)
theorem original_id358 : original358.index = 358 := by decide

def c358 : Contract := original358.toContract.get (by decide)
theorem binding358 : original358.toContract = some c358 := rfl

theorem checked358 : check 4000 c358 = true := by decide

def original359 : RawOriginal := C002.records[103]'(by decide)
theorem original_id359 : original359.index = 359 := by decide

def c359 : Contract := original359.toContract.get (by decide)
theorem binding359 : original359.toContract = some c359 := rfl

theorem checked359 : check 4000 c359 = true := by decide

def original360 : RawOriginal := C002.records[104]'(by decide)
theorem original_id360 : original360.index = 360 := by decide

def c360 : Contract := original360.toContract.get (by decide)
theorem binding360 : original360.toContract = some c360 := rfl

theorem checked360 : check 4000 c360 = true := by decide

def original361 : RawOriginal := C002.records[105]'(by decide)
theorem original_id361 : original361.index = 361 := by decide

def c361 : Contract := original361.toContract.get (by decide)
theorem binding361 : original361.toContract = some c361 := rfl

theorem checked361 : check 4000 c361 = true := by decide

def original362 : RawOriginal := C002.records[106]'(by decide)
theorem original_id362 : original362.index = 362 := by decide

def c362 : Contract := original362.toContract.get (by decide)
theorem binding362 : original362.toContract = some c362 := rfl

theorem checked362 : check 4000 c362 = true := by decide

def original363 : RawOriginal := C002.records[107]'(by decide)
theorem original_id363 : original363.index = 363 := by decide

def c363 : Contract := original363.toContract.get (by decide)
theorem binding363 : original363.toContract = some c363 := rfl

theorem checked363 : check 4000 c363 = true := by decide

def original364 : RawOriginal := C002.records[108]'(by decide)
theorem original_id364 : original364.index = 364 := by decide

def c364 : Contract := original364.toContract.get (by decide)
theorem binding364 : original364.toContract = some c364 := rfl

theorem checked364 : check 4000 c364 = true := by decide

def original365 : RawOriginal := C002.records[109]'(by decide)
theorem original_id365 : original365.index = 365 := by decide

def c365 : Contract := original365.toContract.get (by decide)
theorem binding365 : original365.toContract = some c365 := rfl

theorem checked365 : check 4000 c365 = true := by decide

def original366 : RawOriginal := C002.records[110]'(by decide)
theorem original_id366 : original366.index = 366 := by decide

def c366 : Contract := original366.toContract.get (by decide)
theorem binding366 : original366.toContract = some c366 := rfl

theorem checked366 : check 4000 c366 = true := by decide

def original367 : RawOriginal := C002.records[111]'(by decide)
theorem original_id367 : original367.index = 367 := by decide

def c367 : Contract := original367.toContract.get (by decide)
theorem binding367 : original367.toContract = some c367 := rfl

theorem checked367 : check 4000 c367 = true := by decide

def original368 : RawOriginal := C002.records[112]'(by decide)
theorem original_id368 : original368.index = 368 := by decide

def c368 : Contract := original368.toContract.get (by decide)
theorem binding368 : original368.toContract = some c368 := rfl

theorem checked368 : check 4000 c368 = true := by decide

def original369 : RawOriginal := C002.records[113]'(by decide)
theorem original_id369 : original369.index = 369 := by decide

def c369 : Contract := original369.toContract.get (by decide)
theorem binding369 : original369.toContract = some c369 := rfl

theorem checked369 : check 4000 c369 = true := by decide

def original370 : RawOriginal := C002.records[114]'(by decide)
theorem original_id370 : original370.index = 370 := by decide

def c370 : Contract := original370.toContract.get (by decide)
theorem binding370 : original370.toContract = some c370 := rfl

theorem checked370 : check 4000 c370 = true := by decide

def original371 : RawOriginal := C002.records[115]'(by decide)
theorem original_id371 : original371.index = 371 := by decide

def c371 : Contract := original371.toContract.get (by decide)
theorem binding371 : original371.toContract = some c371 := rfl

theorem checked371 : check 4000 c371 = true := by decide

def original372 : RawOriginal := C002.records[116]'(by decide)
theorem original_id372 : original372.index = 372 := by decide

def c372 : Contract := original372.toContract.get (by decide)
theorem binding372 : original372.toContract = some c372 := rfl

theorem checked372 : check 4000 c372 = true := by decide

def original373 : RawOriginal := C002.records[117]'(by decide)
theorem original_id373 : original373.index = 373 := by decide

def c373 : Contract := original373.toContract.get (by decide)
theorem binding373 : original373.toContract = some c373 := rfl

theorem checked373 : check 4000 c373 = true := by decide

def records : List Certified := [
  ⟨358, c358, 4000, checked358⟩,
  ⟨359, c359, 4000, checked359⟩,
  ⟨360, c360, 4000, checked360⟩,
  ⟨361, c361, 4000, checked361⟩,
  ⟨362, c362, 4000, checked362⟩,
  ⟨363, c363, 4000, checked363⟩,
  ⟨364, c364, 4000, checked364⟩,
  ⟨365, c365, 4000, checked365⟩,
  ⟨366, c366, 4000, checked366⟩,
  ⟨367, c367, 4000, checked367⟩,
  ⟨368, c368, 4000, checked368⟩,
  ⟨369, c369, 4000, checked369⟩,
  ⟨370, c370, 4000, checked370⟩,
  ⟨371, c371, 4000, checked371⟩,
  ⟨372, c372, 4000, checked372⟩,
  ⟨373, c373, 4000, checked373⟩]

end PA215.ContractShards.Shard002Part6
