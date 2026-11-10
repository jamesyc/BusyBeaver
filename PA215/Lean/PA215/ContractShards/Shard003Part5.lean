import PA215.CertifiedContracts
import PA215.Census.C003
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard003Part5
open PA215.Contracts PA215.Census

def original470 : RawOriginal := C003.records[86]'(by decide)
theorem original_id470 : original470.index = 470 := by decide

def c470 : Contract := original470.toContract.get (by decide)
theorem binding470 : original470.toContract = some c470 := rfl

theorem checked470 : check 4000 c470 = true := by decide

def original471 : RawOriginal := C003.records[87]'(by decide)
theorem original_id471 : original471.index = 471 := by decide

def c471 : Contract := original471.toContract.get (by decide)
theorem binding471 : original471.toContract = some c471 := rfl

theorem checked471 : check 4000 c471 = true := by decide

def original472 : RawOriginal := C003.records[88]'(by decide)
theorem original_id472 : original472.index = 472 := by decide

def c472 : Contract := original472.toContract.get (by decide)
theorem binding472 : original472.toContract = some c472 := rfl

theorem checked472 : check 4000 c472 = true := by decide

def original473 : RawOriginal := C003.records[89]'(by decide)
theorem original_id473 : original473.index = 473 := by decide

def c473 : Contract := original473.toContract.get (by decide)
theorem binding473 : original473.toContract = some c473 := rfl

theorem checked473 : check 4000 c473 = true := by decide

def original474 : RawOriginal := C003.records[90]'(by decide)
theorem original_id474 : original474.index = 474 := by decide

def c474 : Contract := original474.toContract.get (by decide)
theorem binding474 : original474.toContract = some c474 := rfl

theorem checked474 : check 4000 c474 = true := by decide

def original475 : RawOriginal := C003.records[91]'(by decide)
theorem original_id475 : original475.index = 475 := by decide

def c475 : Contract := original475.toContract.get (by decide)
theorem binding475 : original475.toContract = some c475 := rfl

theorem checked475 : check 4000 c475 = true := by decide

def original476 : RawOriginal := C003.records[92]'(by decide)
theorem original_id476 : original476.index = 476 := by decide

def c476 : Contract := original476.toContract.get (by decide)
theorem binding476 : original476.toContract = some c476 := rfl

theorem checked476 : check 4000 c476 = true := by decide

def original477 : RawOriginal := C003.records[93]'(by decide)
theorem original_id477 : original477.index = 477 := by decide

def c477 : Contract := original477.toContract.get (by decide)
theorem binding477 : original477.toContract = some c477 := rfl

theorem checked477 : check 4000 c477 = true := by decide

def original478 : RawOriginal := C003.records[94]'(by decide)
theorem original_id478 : original478.index = 478 := by decide

def c478 : Contract := original478.toContract.get (by decide)
theorem binding478 : original478.toContract = some c478 := rfl

theorem checked478 : check 4000 c478 = true := by decide

def original479 : RawOriginal := C003.records[95]'(by decide)
theorem original_id479 : original479.index = 479 := by decide

def c479 : Contract := original479.toContract.get (by decide)
theorem binding479 : original479.toContract = some c479 := rfl

theorem checked479 : check 4000 c479 = true := by decide

def original480 : RawOriginal := C003.records[96]'(by decide)
theorem original_id480 : original480.index = 480 := by decide

def c480 : Contract := original480.toContract.get (by decide)
theorem binding480 : original480.toContract = some c480 := rfl

theorem checked480 : check 4000 c480 = true := by decide

def original481 : RawOriginal := C003.records[97]'(by decide)
theorem original_id481 : original481.index = 481 := by decide

def c481 : Contract := original481.toContract.get (by decide)
theorem binding481 : original481.toContract = some c481 := rfl

theorem checked481 : check 4000 c481 = true := by decide

def original482 : RawOriginal := C003.records[98]'(by decide)
theorem original_id482 : original482.index = 482 := by decide

def c482 : Contract := original482.toContract.get (by decide)
theorem binding482 : original482.toContract = some c482 := rfl

theorem checked482 : check 4000 c482 = true := by decide

def original483 : RawOriginal := C003.records[99]'(by decide)
theorem original_id483 : original483.index = 483 := by decide

def c483 : Contract := original483.toContract.get (by decide)
theorem binding483 : original483.toContract = some c483 := rfl

theorem checked483 : check 4000 c483 = true := by decide

def original484 : RawOriginal := C003.records[100]'(by decide)
theorem original_id484 : original484.index = 484 := by decide

def c484 : Contract := original484.toContract.get (by decide)
theorem binding484 : original484.toContract = some c484 := rfl

theorem checked484 : check 4000 c484 = true := by decide

def original485 : RawOriginal := C003.records[101]'(by decide)
theorem original_id485 : original485.index = 485 := by decide

def c485 : Contract := original485.toContract.get (by decide)
theorem binding485 : original485.toContract = some c485 := rfl

theorem checked485 : check 4000 c485 = true := by decide

def records : List Certified := [
  ⟨470, c470, 4000, checked470⟩,
  ⟨471, c471, 4000, checked471⟩,
  ⟨472, c472, 4000, checked472⟩,
  ⟨473, c473, 4000, checked473⟩,
  ⟨474, c474, 4000, checked474⟩,
  ⟨475, c475, 4000, checked475⟩,
  ⟨476, c476, 4000, checked476⟩,
  ⟨477, c477, 4000, checked477⟩,
  ⟨478, c478, 4000, checked478⟩,
  ⟨479, c479, 4000, checked479⟩,
  ⟨480, c480, 4000, checked480⟩,
  ⟨481, c481, 4000, checked481⟩,
  ⟨482, c482, 4000, checked482⟩,
  ⟨483, c483, 4000, checked483⟩,
  ⟨484, c484, 4000, checked484⟩,
  ⟨485, c485, 4000, checked485⟩]

end PA215.ContractShards.Shard003Part5
