import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C039
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard039Part1
open PA215.Contracts PA215.Census

def original5015 : RawOriginal := C039.records[23]'(by decide)
theorem original_id5015 : original5015.index = 5015 := by decide

def c5015 : Contract := original5015.toContract.get (by decide)
theorem binding5015 : original5015.toContract = some c5015 := rfl

theorem checked5015 : check 4000 c5015 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5016 : RawOriginal := C039.records[24]'(by decide)
theorem original_id5016 : original5016.index = 5016 := by decide

def c5016 : Contract := original5016.toContract.get (by decide)
theorem binding5016 : original5016.toContract = some c5016 := rfl

theorem checked5016 : check 4000 c5016 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5017 : RawOriginal := C039.records[25]'(by decide)
theorem original_id5017 : original5017.index = 5017 := by decide

def c5017 : Contract := original5017.toContract.get (by decide)
theorem binding5017 : original5017.toContract = some c5017 := rfl

theorem checked5017 : check 4000 c5017 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5018 : RawOriginal := C039.records[26]'(by decide)
theorem original_id5018 : original5018.index = 5018 := by decide

def c5018 : Contract := original5018.toContract.get (by decide)
theorem binding5018 : original5018.toContract = some c5018 := rfl

theorem checked5018 : check 4000 c5018 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5019 : RawOriginal := C039.records[27]'(by decide)
theorem original_id5019 : original5019.index = 5019 := by decide

def c5019 : Contract := original5019.toContract.get (by decide)
theorem binding5019 : original5019.toContract = some c5019 := rfl

theorem checked5019 : check 4000 c5019 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5020 : RawOriginal := C039.records[28]'(by decide)
theorem original_id5020 : original5020.index = 5020 := by decide

def c5020 : Contract := original5020.toContract.get (by decide)
theorem binding5020 : original5020.toContract = some c5020 := rfl

theorem checked5020 : check 4000 c5020 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5021 : RawOriginal := C039.records[29]'(by decide)
theorem original_id5021 : original5021.index = 5021 := by decide

def c5021 : Contract := original5021.toContract.get (by decide)
theorem binding5021 : original5021.toContract = some c5021 := rfl

theorem checked5021 : check 4000 c5021 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5022 : RawOriginal := C039.records[30]'(by decide)
theorem original_id5022 : original5022.index = 5022 := by decide

def c5022 : Contract := original5022.toContract.get (by decide)
theorem binding5022 : original5022.toContract = some c5022 := rfl

theorem checked5022 : check 4000 c5022 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5023 : RawOriginal := C039.records[31]'(by decide)
theorem original_id5023 : original5023.index = 5023 := by decide

def c5023 : Contract := original5023.toContract.get (by decide)
theorem binding5023 : original5023.toContract = some c5023 := rfl

theorem checked5023 : check 4000 c5023 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5024 : RawOriginal := C039.records[32]'(by decide)
theorem original_id5024 : original5024.index = 5024 := by decide

def c5024 : Contract := original5024.toContract.get (by decide)
theorem binding5024 : original5024.toContract = some c5024 := rfl

theorem checked5024 : check 4000 c5024 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5025 : RawOriginal := C039.records[33]'(by decide)
theorem original_id5025 : original5025.index = 5025 := by decide

def c5025 : Contract := original5025.toContract.get (by decide)
theorem binding5025 : original5025.toContract = some c5025 := rfl

theorem checked5025 : check 4000 c5025 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5026 : RawOriginal := C039.records[34]'(by decide)
theorem original_id5026 : original5026.index = 5026 := by decide

def c5026 : Contract := original5026.toContract.get (by decide)
theorem binding5026 : original5026.toContract = some c5026 := rfl

theorem checked5026 : check 4000 c5026 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5027 : RawOriginal := C039.records[35]'(by decide)
theorem original_id5027 : original5027.index = 5027 := by decide

def c5027 : Contract := original5027.toContract.get (by decide)
theorem binding5027 : original5027.toContract = some c5027 := rfl

theorem checked5027 : check 4000 c5027 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5028 : RawOriginal := C039.records[36]'(by decide)
theorem original_id5028 : original5028.index = 5028 := by decide

def c5028 : Contract := original5028.toContract.get (by decide)
theorem binding5028 : original5028.toContract = some c5028 := rfl

theorem checked5028 : check 4000 c5028 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5029 : RawOriginal := C039.records[37]'(by decide)
theorem original_id5029 : original5029.index = 5029 := by decide

def c5029 : Contract := original5029.toContract.get (by decide)
theorem binding5029 : original5029.toContract = some c5029 := rfl

theorem checked5029 : check 4000 c5029 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original5030 : RawOriginal := C039.records[38]'(by decide)
theorem original_id5030 : original5030.index = 5030 := by decide

def c5030 : Contract := original5030.toContract.get (by decide)
theorem binding5030 : original5030.toContract = some c5030 := rfl

theorem checked5030 : check 4000 c5030 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨5015, c5015, 4000, checked5015⟩,
  ⟨5016, c5016, 4000, checked5016⟩,
  ⟨5017, c5017, 4000, checked5017⟩,
  ⟨5018, c5018, 4000, checked5018⟩,
  ⟨5019, c5019, 4000, checked5019⟩,
  ⟨5020, c5020, 4000, checked5020⟩,
  ⟨5021, c5021, 4000, checked5021⟩,
  ⟨5022, c5022, 4000, checked5022⟩,
  ⟨5023, c5023, 4000, checked5023⟩,
  ⟨5024, c5024, 4000, checked5024⟩,
  ⟨5025, c5025, 4000, checked5025⟩,
  ⟨5026, c5026, 4000, checked5026⟩,
  ⟨5027, c5027, 4000, checked5027⟩,
  ⟨5028, c5028, 4000, checked5028⟩,
  ⟨5029, c5029, 4000, checked5029⟩,
  ⟨5030, c5030, 4000, checked5030⟩]

end PA215.ContractShards.Shard039Part1
