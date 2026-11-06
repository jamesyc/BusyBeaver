import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C030
import PA215.Census.C031
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard030Part7
open PA215.Contracts PA215.Census

def original3958 : RawOriginal := C030.records[118]'(by decide)
theorem original_id3958 : original3958.index = 3958 := by decide

def c3958 : Contract := original3958.toContract.get (by decide)
theorem binding3958 : original3958.toContract = some c3958 := rfl

theorem checked3958 : check 4000 c3958 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3959 : RawOriginal := C030.records[119]'(by decide)
theorem original_id3959 : original3959.index = 3959 := by decide

def c3959 : Contract := original3959.toContract.get (by decide)
theorem binding3959 : original3959.toContract = some c3959 := rfl

theorem checked3959 : check 4000 c3959 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3960 : RawOriginal := C030.records[120]'(by decide)
theorem original_id3960 : original3960.index = 3960 := by decide

def c3960 : Contract := original3960.toContract.get (by decide)
theorem binding3960 : original3960.toContract = some c3960 := rfl

theorem checked3960 : check 4000 c3960 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3961 : RawOriginal := C030.records[121]'(by decide)
theorem original_id3961 : original3961.index = 3961 := by decide

def c3961 : Contract := original3961.toContract.get (by decide)
theorem binding3961 : original3961.toContract = some c3961 := rfl

theorem checked3961 : check 4000 c3961 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3962 : RawOriginal := C030.records[122]'(by decide)
theorem original_id3962 : original3962.index = 3962 := by decide

def c3962 : Contract := original3962.toContract.get (by decide)
theorem binding3962 : original3962.toContract = some c3962 := rfl

theorem checked3962 : check 4000 c3962 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3963 : RawOriginal := C030.records[123]'(by decide)
theorem original_id3963 : original3963.index = 3963 := by decide

def c3963 : Contract := original3963.toContract.get (by decide)
theorem binding3963 : original3963.toContract = some c3963 := rfl

theorem checked3963 : check 4000 c3963 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3964 : RawOriginal := C030.records[124]'(by decide)
theorem original_id3964 : original3964.index = 3964 := by decide

def c3964 : Contract := original3964.toContract.get (by decide)
theorem binding3964 : original3964.toContract = some c3964 := rfl

theorem checked3964 : check 4000 c3964 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3965 : RawOriginal := C030.records[125]'(by decide)
theorem original_id3965 : original3965.index = 3965 := by decide

def c3965 : Contract := original3965.toContract.get (by decide)
theorem binding3965 : original3965.toContract = some c3965 := rfl

theorem checked3965 : check 4000 c3965 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3966 : RawOriginal := C030.records[126]'(by decide)
theorem original_id3966 : original3966.index = 3966 := by decide

def c3966 : Contract := original3966.toContract.get (by decide)
theorem binding3966 : original3966.toContract = some c3966 := rfl

theorem checked3966 : check 4000 c3966 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3967 : RawOriginal := C030.records[127]'(by decide)
theorem original_id3967 : original3967.index = 3967 := by decide

def c3967 : Contract := original3967.toContract.get (by decide)
theorem binding3967 : original3967.toContract = some c3967 := rfl

theorem checked3967 : check 4000 c3967 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3968 : RawOriginal := C031.records[0]'(by decide)
theorem original_id3968 : original3968.index = 3968 := by decide

def c3968 : Contract := original3968.toContract.get (by decide)
theorem binding3968 : original3968.toContract = some c3968 := rfl

theorem checked3968 : check 4000 c3968 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3969 : RawOriginal := C031.records[1]'(by decide)
theorem original_id3969 : original3969.index = 3969 := by decide

def c3969 : Contract := original3969.toContract.get (by decide)
theorem binding3969 : original3969.toContract = some c3969 := rfl

theorem checked3969 : check 4000 c3969 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3970 : RawOriginal := C031.records[2]'(by decide)
theorem original_id3970 : original3970.index = 3970 := by decide

def c3970 : Contract := original3970.toContract.get (by decide)
theorem binding3970 : original3970.toContract = some c3970 := rfl

theorem checked3970 : check 4000 c3970 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3971 : RawOriginal := C031.records[3]'(by decide)
theorem original_id3971 : original3971.index = 3971 := by decide

def c3971 : Contract := original3971.toContract.get (by decide)
theorem binding3971 : original3971.toContract = some c3971 := rfl

theorem checked3971 : check 4000 c3971 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3972 : RawOriginal := C031.records[4]'(by decide)
theorem original_id3972 : original3972.index = 3972 := by decide

def c3972 : Contract := original3972.toContract.get (by decide)
theorem binding3972 : original3972.toContract = some c3972 := rfl

theorem checked3972 : check 4000 c3972 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original3973 : RawOriginal := C031.records[5]'(by decide)
theorem original_id3973 : original3973.index = 3973 := by decide

def c3973 : Contract := original3973.toContract.get (by decide)
theorem binding3973 : original3973.toContract = some c3973 := rfl

theorem checked3973 : check 4000 c3973 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨3958, c3958, 4000, checked3958⟩,
  ⟨3959, c3959, 4000, checked3959⟩,
  ⟨3960, c3960, 4000, checked3960⟩,
  ⟨3961, c3961, 4000, checked3961⟩,
  ⟨3962, c3962, 4000, checked3962⟩,
  ⟨3963, c3963, 4000, checked3963⟩,
  ⟨3964, c3964, 4000, checked3964⟩,
  ⟨3965, c3965, 4000, checked3965⟩,
  ⟨3966, c3966, 4000, checked3966⟩,
  ⟨3967, c3967, 4000, checked3967⟩,
  ⟨3968, c3968, 4000, checked3968⟩,
  ⟨3969, c3969, 4000, checked3969⟩,
  ⟨3970, c3970, 4000, checked3970⟩,
  ⟨3971, c3971, 4000, checked3971⟩,
  ⟨3972, c3972, 4000, checked3972⟩,
  ⟨3973, c3973, 4000, checked3973⟩]

end PA215.ContractShards.Shard030Part7
