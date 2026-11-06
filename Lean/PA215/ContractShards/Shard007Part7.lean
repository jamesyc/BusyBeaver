import PA215.CertifiedContracts
import PA215.Census.C007
import PA215.Census.C008
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard007Part7
open PA215.Contracts PA215.Census

def original1014 : RawOriginal := C007.records[118]'(by decide)
theorem original_id1014 : original1014.index = 1014 := by decide

def c1014 : Contract := original1014.toContract.get (by decide)
theorem binding1014 : original1014.toContract = some c1014 := rfl

theorem checked1014 : check 4000 c1014 = true := by decide

def original1015 : RawOriginal := C007.records[119]'(by decide)
theorem original_id1015 : original1015.index = 1015 := by decide

def c1015 : Contract := original1015.toContract.get (by decide)
theorem binding1015 : original1015.toContract = some c1015 := rfl

theorem checked1015 : check 4000 c1015 = true := by decide

def original1016 : RawOriginal := C007.records[120]'(by decide)
theorem original_id1016 : original1016.index = 1016 := by decide

def c1016 : Contract := original1016.toContract.get (by decide)
theorem binding1016 : original1016.toContract = some c1016 := rfl

theorem checked1016 : check 4000 c1016 = true := by decide

def original1017 : RawOriginal := C007.records[121]'(by decide)
theorem original_id1017 : original1017.index = 1017 := by decide

def c1017 : Contract := original1017.toContract.get (by decide)
theorem binding1017 : original1017.toContract = some c1017 := rfl

theorem checked1017 : check 4000 c1017 = true := by decide

def original1018 : RawOriginal := C007.records[122]'(by decide)
theorem original_id1018 : original1018.index = 1018 := by decide

def c1018 : Contract := original1018.toContract.get (by decide)
theorem binding1018 : original1018.toContract = some c1018 := rfl

theorem checked1018 : check 4000 c1018 = true := by decide

def original1019 : RawOriginal := C007.records[123]'(by decide)
theorem original_id1019 : original1019.index = 1019 := by decide

def c1019 : Contract := original1019.toContract.get (by decide)
theorem binding1019 : original1019.toContract = some c1019 := rfl

theorem checked1019 : check 4000 c1019 = true := by decide

def original1020 : RawOriginal := C007.records[124]'(by decide)
theorem original_id1020 : original1020.index = 1020 := by decide

def c1020 : Contract := original1020.toContract.get (by decide)
theorem binding1020 : original1020.toContract = some c1020 := rfl

theorem checked1020 : check 4000 c1020 = true := by decide

def original1021 : RawOriginal := C007.records[125]'(by decide)
theorem original_id1021 : original1021.index = 1021 := by decide

def c1021 : Contract := original1021.toContract.get (by decide)
theorem binding1021 : original1021.toContract = some c1021 := rfl

theorem checked1021 : check 4000 c1021 = true := by decide

def original1022 : RawOriginal := C007.records[126]'(by decide)
theorem original_id1022 : original1022.index = 1022 := by decide

def c1022 : Contract := original1022.toContract.get (by decide)
theorem binding1022 : original1022.toContract = some c1022 := rfl

theorem checked1022 : check 4000 c1022 = true := by decide

def original1023 : RawOriginal := C007.records[127]'(by decide)
theorem original_id1023 : original1023.index = 1023 := by decide

def c1023 : Contract := original1023.toContract.get (by decide)
theorem binding1023 : original1023.toContract = some c1023 := rfl

theorem checked1023 : check 4000 c1023 = true := by decide

def original1024 : RawOriginal := C008.records[0]'(by decide)
theorem original_id1024 : original1024.index = 1024 := by decide

def c1024 : Contract := original1024.toContract.get (by decide)
theorem binding1024 : original1024.toContract = some c1024 := rfl

theorem checked1024 : check 4000 c1024 = true := by decide

def original1025 : RawOriginal := C008.records[1]'(by decide)
theorem original_id1025 : original1025.index = 1025 := by decide

def c1025 : Contract := original1025.toContract.get (by decide)
theorem binding1025 : original1025.toContract = some c1025 := rfl

theorem checked1025 : check 4000 c1025 = true := by decide

def original1026 : RawOriginal := C008.records[2]'(by decide)
theorem original_id1026 : original1026.index = 1026 := by decide

def c1026 : Contract := original1026.toContract.get (by decide)
theorem binding1026 : original1026.toContract = some c1026 := rfl

theorem checked1026 : check 4000 c1026 = true := by decide

def original1027 : RawOriginal := C008.records[3]'(by decide)
theorem original_id1027 : original1027.index = 1027 := by decide

def c1027 : Contract := original1027.toContract.get (by decide)
theorem binding1027 : original1027.toContract = some c1027 := rfl

theorem checked1027 : check 4000 c1027 = true := by decide

def original1028 : RawOriginal := C008.records[4]'(by decide)
theorem original_id1028 : original1028.index = 1028 := by decide

def c1028 : Contract := original1028.toContract.get (by decide)
theorem binding1028 : original1028.toContract = some c1028 := rfl

theorem checked1028 : check 4000 c1028 = true := by decide

def original1029 : RawOriginal := C008.records[5]'(by decide)
theorem original_id1029 : original1029.index = 1029 := by decide

def c1029 : Contract := original1029.toContract.get (by decide)
theorem binding1029 : original1029.toContract = some c1029 := rfl

theorem checked1029 : check 4000 c1029 = true := by decide

def records : List Certified := [
  ⟨1014, c1014, 4000, checked1014⟩,
  ⟨1015, c1015, 4000, checked1015⟩,
  ⟨1016, c1016, 4000, checked1016⟩,
  ⟨1017, c1017, 4000, checked1017⟩,
  ⟨1018, c1018, 4000, checked1018⟩,
  ⟨1019, c1019, 4000, checked1019⟩,
  ⟨1020, c1020, 4000, checked1020⟩,
  ⟨1021, c1021, 4000, checked1021⟩,
  ⟨1022, c1022, 4000, checked1022⟩,
  ⟨1023, c1023, 4000, checked1023⟩,
  ⟨1024, c1024, 4000, checked1024⟩,
  ⟨1025, c1025, 4000, checked1025⟩,
  ⟨1026, c1026, 4000, checked1026⟩,
  ⟨1027, c1027, 4000, checked1027⟩,
  ⟨1028, c1028, 4000, checked1028⟩,
  ⟨1029, c1029, 4000, checked1029⟩]

end PA215.ContractShards.Shard007Part7
