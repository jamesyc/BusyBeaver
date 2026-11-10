import PA215.CertifiedContracts
import PA215.Census.C002
import PA215.Census.C003
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard002Part7
open PA215.Contracts PA215.Census

def original374 : RawOriginal := C002.records[118]'(by decide)
theorem original_id374 : original374.index = 374 := by decide

def c374 : Contract := original374.toContract.get (by decide)
theorem binding374 : original374.toContract = some c374 := rfl

theorem checked374 : check 4000 c374 = true := by decide

def original375 : RawOriginal := C002.records[119]'(by decide)
theorem original_id375 : original375.index = 375 := by decide

def c375 : Contract := original375.toContract.get (by decide)
theorem binding375 : original375.toContract = some c375 := rfl

theorem checked375 : check 4000 c375 = true := by decide

def original376 : RawOriginal := C002.records[120]'(by decide)
theorem original_id376 : original376.index = 376 := by decide

def c376 : Contract := original376.toContract.get (by decide)
theorem binding376 : original376.toContract = some c376 := rfl

theorem checked376 : check 4000 c376 = true := by decide

def original377 : RawOriginal := C002.records[121]'(by decide)
theorem original_id377 : original377.index = 377 := by decide

def c377 : Contract := original377.toContract.get (by decide)
theorem binding377 : original377.toContract = some c377 := rfl

theorem checked377 : check 4000 c377 = true := by decide

def original378 : RawOriginal := C002.records[122]'(by decide)
theorem original_id378 : original378.index = 378 := by decide

def c378 : Contract := original378.toContract.get (by decide)
theorem binding378 : original378.toContract = some c378 := rfl

theorem checked378 : check 4000 c378 = true := by decide

def original379 : RawOriginal := C002.records[123]'(by decide)
theorem original_id379 : original379.index = 379 := by decide

def c379 : Contract := original379.toContract.get (by decide)
theorem binding379 : original379.toContract = some c379 := rfl

theorem checked379 : check 4000 c379 = true := by decide

def original380 : RawOriginal := C002.records[124]'(by decide)
theorem original_id380 : original380.index = 380 := by decide

def c380 : Contract := original380.toContract.get (by decide)
theorem binding380 : original380.toContract = some c380 := rfl

theorem checked380 : check 4000 c380 = true := by decide

def original381 : RawOriginal := C002.records[125]'(by decide)
theorem original_id381 : original381.index = 381 := by decide

def c381 : Contract := original381.toContract.get (by decide)
theorem binding381 : original381.toContract = some c381 := rfl

theorem checked381 : check 4000 c381 = true := by decide

def original382 : RawOriginal := C002.records[126]'(by decide)
theorem original_id382 : original382.index = 382 := by decide

def c382 : Contract := original382.toContract.get (by decide)
theorem binding382 : original382.toContract = some c382 := rfl

theorem checked382 : check 4000 c382 = true := by decide

def original383 : RawOriginal := C002.records[127]'(by decide)
theorem original_id383 : original383.index = 383 := by decide

def c383 : Contract := original383.toContract.get (by decide)
theorem binding383 : original383.toContract = some c383 := rfl

theorem checked383 : check 4000 c383 = true := by decide

def original384 : RawOriginal := C003.records[0]'(by decide)
theorem original_id384 : original384.index = 384 := by decide

def c384 : Contract := original384.toContract.get (by decide)
theorem binding384 : original384.toContract = some c384 := rfl

theorem checked384 : check 4000 c384 = true := by decide

def original385 : RawOriginal := C003.records[1]'(by decide)
theorem original_id385 : original385.index = 385 := by decide

def c385 : Contract := original385.toContract.get (by decide)
theorem binding385 : original385.toContract = some c385 := rfl

theorem checked385 : check 4000 c385 = true := by decide

def original386 : RawOriginal := C003.records[2]'(by decide)
theorem original_id386 : original386.index = 386 := by decide

def c386 : Contract := original386.toContract.get (by decide)
theorem binding386 : original386.toContract = some c386 := rfl

theorem checked386 : check 4000 c386 = true := by decide

def original387 : RawOriginal := C003.records[3]'(by decide)
theorem original_id387 : original387.index = 387 := by decide

def c387 : Contract := original387.toContract.get (by decide)
theorem binding387 : original387.toContract = some c387 := rfl

theorem checked387 : check 4000 c387 = true := by decide

def original388 : RawOriginal := C003.records[4]'(by decide)
theorem original_id388 : original388.index = 388 := by decide

def c388 : Contract := original388.toContract.get (by decide)
theorem binding388 : original388.toContract = some c388 := rfl

theorem checked388 : check 4000 c388 = true := by decide

def original389 : RawOriginal := C003.records[5]'(by decide)
theorem original_id389 : original389.index = 389 := by decide

def c389 : Contract := original389.toContract.get (by decide)
theorem binding389 : original389.toContract = some c389 := rfl

theorem checked389 : check 4000 c389 = true := by decide

def records : List Certified := [
  ⟨374, c374, 4000, checked374⟩,
  ⟨375, c375, 4000, checked375⟩,
  ⟨376, c376, 4000, checked376⟩,
  ⟨377, c377, 4000, checked377⟩,
  ⟨378, c378, 4000, checked378⟩,
  ⟨379, c379, 4000, checked379⟩,
  ⟨380, c380, 4000, checked380⟩,
  ⟨381, c381, 4000, checked381⟩,
  ⟨382, c382, 4000, checked382⟩,
  ⟨383, c383, 4000, checked383⟩,
  ⟨384, c384, 4000, checked384⟩,
  ⟨385, c385, 4000, checked385⟩,
  ⟨386, c386, 4000, checked386⟩,
  ⟨387, c387, 4000, checked387⟩,
  ⟨388, c388, 4000, checked388⟩,
  ⟨389, c389, 4000, checked389⟩]

end PA215.ContractShards.Shard002Part7
