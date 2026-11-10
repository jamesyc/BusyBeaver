import PA215.CertifiedContracts
import PA215.Census.C008
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard008Part2
open PA215.Contracts PA215.Census

def original1062 : RawOriginal := C008.records[38]'(by decide)
theorem original_id1062 : original1062.index = 1062 := by decide

def c1062 : Contract := original1062.toContract.get (by decide)
theorem binding1062 : original1062.toContract = some c1062 := rfl

theorem checked1062 : check 4000 c1062 = true := by decide

def original1063 : RawOriginal := C008.records[39]'(by decide)
theorem original_id1063 : original1063.index = 1063 := by decide

def c1063 : Contract := original1063.toContract.get (by decide)
theorem binding1063 : original1063.toContract = some c1063 := rfl

theorem checked1063 : check 4000 c1063 = true := by decide

def original1064 : RawOriginal := C008.records[40]'(by decide)
theorem original_id1064 : original1064.index = 1064 := by decide

def c1064 : Contract := original1064.toContract.get (by decide)
theorem binding1064 : original1064.toContract = some c1064 := rfl

theorem checked1064 : check 4000 c1064 = true := by decide

def original1065 : RawOriginal := C008.records[41]'(by decide)
theorem original_id1065 : original1065.index = 1065 := by decide

def c1065 : Contract := original1065.toContract.get (by decide)
theorem binding1065 : original1065.toContract = some c1065 := rfl

theorem checked1065 : check 4000 c1065 = true := by decide

def original1066 : RawOriginal := C008.records[42]'(by decide)
theorem original_id1066 : original1066.index = 1066 := by decide

def c1066 : Contract := original1066.toContract.get (by decide)
theorem binding1066 : original1066.toContract = some c1066 := rfl

theorem checked1066 : check 4000 c1066 = true := by decide

def original1067 : RawOriginal := C008.records[43]'(by decide)
theorem original_id1067 : original1067.index = 1067 := by decide

def c1067 : Contract := original1067.toContract.get (by decide)
theorem binding1067 : original1067.toContract = some c1067 := rfl

theorem checked1067 : check 4000 c1067 = true := by decide

def original1068 : RawOriginal := C008.records[44]'(by decide)
theorem original_id1068 : original1068.index = 1068 := by decide

def c1068 : Contract := original1068.toContract.get (by decide)
theorem binding1068 : original1068.toContract = some c1068 := rfl

theorem checked1068 : check 4000 c1068 = true := by decide

def original1069 : RawOriginal := C008.records[45]'(by decide)
theorem original_id1069 : original1069.index = 1069 := by decide

def c1069 : Contract := original1069.toContract.get (by decide)
theorem binding1069 : original1069.toContract = some c1069 := rfl

theorem checked1069 : check 4000 c1069 = true := by decide

def original1070 : RawOriginal := C008.records[46]'(by decide)
theorem original_id1070 : original1070.index = 1070 := by decide

def c1070 : Contract := original1070.toContract.get (by decide)
theorem binding1070 : original1070.toContract = some c1070 := rfl

theorem checked1070 : check 4000 c1070 = true := by decide

def original1071 : RawOriginal := C008.records[47]'(by decide)
theorem original_id1071 : original1071.index = 1071 := by decide

def c1071 : Contract := original1071.toContract.get (by decide)
theorem binding1071 : original1071.toContract = some c1071 := rfl

theorem checked1071 : check 4000 c1071 = true := by decide

def original1072 : RawOriginal := C008.records[48]'(by decide)
theorem original_id1072 : original1072.index = 1072 := by decide

def c1072 : Contract := original1072.toContract.get (by decide)
theorem binding1072 : original1072.toContract = some c1072 := rfl

theorem checked1072 : check 4000 c1072 = true := by decide

def original1073 : RawOriginal := C008.records[49]'(by decide)
theorem original_id1073 : original1073.index = 1073 := by decide

def c1073 : Contract := original1073.toContract.get (by decide)
theorem binding1073 : original1073.toContract = some c1073 := rfl

theorem checked1073 : check 4000 c1073 = true := by decide

def original1074 : RawOriginal := C008.records[50]'(by decide)
theorem original_id1074 : original1074.index = 1074 := by decide

def c1074 : Contract := original1074.toContract.get (by decide)
theorem binding1074 : original1074.toContract = some c1074 := rfl

theorem checked1074 : check 4000 c1074 = true := by decide

def original1075 : RawOriginal := C008.records[51]'(by decide)
theorem original_id1075 : original1075.index = 1075 := by decide

def c1075 : Contract := original1075.toContract.get (by decide)
theorem binding1075 : original1075.toContract = some c1075 := rfl

theorem checked1075 : check 4000 c1075 = true := by decide

def original1076 : RawOriginal := C008.records[52]'(by decide)
theorem original_id1076 : original1076.index = 1076 := by decide

def c1076 : Contract := original1076.toContract.get (by decide)
theorem binding1076 : original1076.toContract = some c1076 := rfl

theorem checked1076 : check 4000 c1076 = true := by decide

def original1077 : RawOriginal := C008.records[53]'(by decide)
theorem original_id1077 : original1077.index = 1077 := by decide

def c1077 : Contract := original1077.toContract.get (by decide)
theorem binding1077 : original1077.toContract = some c1077 := rfl

theorem checked1077 : check 4000 c1077 = true := by decide

def records : List Certified := [
  ⟨1062, c1062, 4000, checked1062⟩,
  ⟨1063, c1063, 4000, checked1063⟩,
  ⟨1064, c1064, 4000, checked1064⟩,
  ⟨1065, c1065, 4000, checked1065⟩,
  ⟨1066, c1066, 4000, checked1066⟩,
  ⟨1067, c1067, 4000, checked1067⟩,
  ⟨1068, c1068, 4000, checked1068⟩,
  ⟨1069, c1069, 4000, checked1069⟩,
  ⟨1070, c1070, 4000, checked1070⟩,
  ⟨1071, c1071, 4000, checked1071⟩,
  ⟨1072, c1072, 4000, checked1072⟩,
  ⟨1073, c1073, 4000, checked1073⟩,
  ⟨1074, c1074, 4000, checked1074⟩,
  ⟨1075, c1075, 4000, checked1075⟩,
  ⟨1076, c1076, 4000, checked1076⟩,
  ⟨1077, c1077, 4000, checked1077⟩]

end PA215.ContractShards.Shard008Part2
