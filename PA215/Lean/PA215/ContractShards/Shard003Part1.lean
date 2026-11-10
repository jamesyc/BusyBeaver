import PA215.CertifiedContracts
import PA215.Census.C003
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard003Part1
open PA215.Contracts PA215.Census

def original406 : RawOriginal := C003.records[22]'(by decide)
theorem original_id406 : original406.index = 406 := by decide

def c406 : Contract := original406.toContract.get (by decide)
theorem binding406 : original406.toContract = some c406 := rfl

theorem checked406 : check 4000 c406 = true := by decide

def original407 : RawOriginal := C003.records[23]'(by decide)
theorem original_id407 : original407.index = 407 := by decide

def c407 : Contract := original407.toContract.get (by decide)
theorem binding407 : original407.toContract = some c407 := rfl

theorem checked407 : check 4000 c407 = true := by decide

def original408 : RawOriginal := C003.records[24]'(by decide)
theorem original_id408 : original408.index = 408 := by decide

def c408 : Contract := original408.toContract.get (by decide)
theorem binding408 : original408.toContract = some c408 := rfl

theorem checked408 : check 4000 c408 = true := by decide

def original409 : RawOriginal := C003.records[25]'(by decide)
theorem original_id409 : original409.index = 409 := by decide

def c409 : Contract := original409.toContract.get (by decide)
theorem binding409 : original409.toContract = some c409 := rfl

theorem checked409 : check 4000 c409 = true := by decide

def original410 : RawOriginal := C003.records[26]'(by decide)
theorem original_id410 : original410.index = 410 := by decide

def c410 : Contract := original410.toContract.get (by decide)
theorem binding410 : original410.toContract = some c410 := rfl

theorem checked410 : check 4000 c410 = true := by decide

def original411 : RawOriginal := C003.records[27]'(by decide)
theorem original_id411 : original411.index = 411 := by decide

def c411 : Contract := original411.toContract.get (by decide)
theorem binding411 : original411.toContract = some c411 := rfl

theorem checked411 : check 4000 c411 = true := by decide

def original412 : RawOriginal := C003.records[28]'(by decide)
theorem original_id412 : original412.index = 412 := by decide

def c412 : Contract := original412.toContract.get (by decide)
theorem binding412 : original412.toContract = some c412 := rfl

theorem checked412 : check 4000 c412 = true := by decide

def original413 : RawOriginal := C003.records[29]'(by decide)
theorem original_id413 : original413.index = 413 := by decide

def c413 : Contract := original413.toContract.get (by decide)
theorem binding413 : original413.toContract = some c413 := rfl

theorem checked413 : check 4000 c413 = true := by decide

def original414 : RawOriginal := C003.records[30]'(by decide)
theorem original_id414 : original414.index = 414 := by decide

def c414 : Contract := original414.toContract.get (by decide)
theorem binding414 : original414.toContract = some c414 := rfl

theorem checked414 : check 4000 c414 = true := by decide

def original415 : RawOriginal := C003.records[31]'(by decide)
theorem original_id415 : original415.index = 415 := by decide

def c415 : Contract := original415.toContract.get (by decide)
theorem binding415 : original415.toContract = some c415 := rfl

theorem checked415 : check 4000 c415 = true := by decide

def original416 : RawOriginal := C003.records[32]'(by decide)
theorem original_id416 : original416.index = 416 := by decide

def c416 : Contract := original416.toContract.get (by decide)
theorem binding416 : original416.toContract = some c416 := rfl

theorem checked416 : check 4000 c416 = true := by decide

def original417 : RawOriginal := C003.records[33]'(by decide)
theorem original_id417 : original417.index = 417 := by decide

def c417 : Contract := original417.toContract.get (by decide)
theorem binding417 : original417.toContract = some c417 := rfl

theorem checked417 : check 4000 c417 = true := by decide

def original418 : RawOriginal := C003.records[34]'(by decide)
theorem original_id418 : original418.index = 418 := by decide

def c418 : Contract := original418.toContract.get (by decide)
theorem binding418 : original418.toContract = some c418 := rfl

theorem checked418 : check 4000 c418 = true := by decide

def original419 : RawOriginal := C003.records[35]'(by decide)
theorem original_id419 : original419.index = 419 := by decide

def c419 : Contract := original419.toContract.get (by decide)
theorem binding419 : original419.toContract = some c419 := rfl

theorem checked419 : check 4000 c419 = true := by decide

def original420 : RawOriginal := C003.records[36]'(by decide)
theorem original_id420 : original420.index = 420 := by decide

def c420 : Contract := original420.toContract.get (by decide)
theorem binding420 : original420.toContract = some c420 := rfl

theorem checked420 : check 4000 c420 = true := by decide

def original421 : RawOriginal := C003.records[37]'(by decide)
theorem original_id421 : original421.index = 421 := by decide

def c421 : Contract := original421.toContract.get (by decide)
theorem binding421 : original421.toContract = some c421 := rfl

theorem checked421 : check 4000 c421 = true := by decide

def records : List Certified := [
  ⟨406, c406, 4000, checked406⟩,
  ⟨407, c407, 4000, checked407⟩,
  ⟨408, c408, 4000, checked408⟩,
  ⟨409, c409, 4000, checked409⟩,
  ⟨410, c410, 4000, checked410⟩,
  ⟨411, c411, 4000, checked411⟩,
  ⟨412, c412, 4000, checked412⟩,
  ⟨413, c413, 4000, checked413⟩,
  ⟨414, c414, 4000, checked414⟩,
  ⟨415, c415, 4000, checked415⟩,
  ⟨416, c416, 4000, checked416⟩,
  ⟨417, c417, 4000, checked417⟩,
  ⟨418, c418, 4000, checked418⟩,
  ⟨419, c419, 4000, checked419⟩,
  ⟨420, c420, 4000, checked420⟩,
  ⟨421, c421, 4000, checked421⟩]

end PA215.ContractShards.Shard003Part1
