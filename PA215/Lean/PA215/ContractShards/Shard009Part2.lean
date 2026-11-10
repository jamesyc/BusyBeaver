import PA215.CertifiedContracts
import PA215.Census.C009
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard009Part2
open PA215.Contracts PA215.Census

def original1190 : RawOriginal := C009.records[38]'(by decide)
theorem original_id1190 : original1190.index = 1190 := by decide

def c1190 : Contract := original1190.toContract.get (by decide)
theorem binding1190 : original1190.toContract = some c1190 := rfl

theorem checked1190 : check 4000 c1190 = true := by decide

def original1191 : RawOriginal := C009.records[39]'(by decide)
theorem original_id1191 : original1191.index = 1191 := by decide

def c1191 : Contract := original1191.toContract.get (by decide)
theorem binding1191 : original1191.toContract = some c1191 := rfl

theorem checked1191 : check 4000 c1191 = true := by decide

def original1192 : RawOriginal := C009.records[40]'(by decide)
theorem original_id1192 : original1192.index = 1192 := by decide

def c1192 : Contract := original1192.toContract.get (by decide)
theorem binding1192 : original1192.toContract = some c1192 := rfl

theorem checked1192 : check 4000 c1192 = true := by decide

def original1193 : RawOriginal := C009.records[41]'(by decide)
theorem original_id1193 : original1193.index = 1193 := by decide

def c1193 : Contract := original1193.toContract.get (by decide)
theorem binding1193 : original1193.toContract = some c1193 := rfl

theorem checked1193 : check 4000 c1193 = true := by decide

def original1194 : RawOriginal := C009.records[42]'(by decide)
theorem original_id1194 : original1194.index = 1194 := by decide

def c1194 : Contract := original1194.toContract.get (by decide)
theorem binding1194 : original1194.toContract = some c1194 := rfl

theorem checked1194 : check 4000 c1194 = true := by decide

def original1195 : RawOriginal := C009.records[43]'(by decide)
theorem original_id1195 : original1195.index = 1195 := by decide

def c1195 : Contract := original1195.toContract.get (by decide)
theorem binding1195 : original1195.toContract = some c1195 := rfl

theorem checked1195 : check 4000 c1195 = true := by decide

def original1196 : RawOriginal := C009.records[44]'(by decide)
theorem original_id1196 : original1196.index = 1196 := by decide

def c1196 : Contract := original1196.toContract.get (by decide)
theorem binding1196 : original1196.toContract = some c1196 := rfl

theorem checked1196 : check 4000 c1196 = true := by decide

def original1197 : RawOriginal := C009.records[45]'(by decide)
theorem original_id1197 : original1197.index = 1197 := by decide

def c1197 : Contract := original1197.toContract.get (by decide)
theorem binding1197 : original1197.toContract = some c1197 := rfl

theorem checked1197 : check 4000 c1197 = true := by decide

def original1198 : RawOriginal := C009.records[46]'(by decide)
theorem original_id1198 : original1198.index = 1198 := by decide

def c1198 : Contract := original1198.toContract.get (by decide)
theorem binding1198 : original1198.toContract = some c1198 := rfl

theorem checked1198 : check 4000 c1198 = true := by decide

def original1199 : RawOriginal := C009.records[47]'(by decide)
theorem original_id1199 : original1199.index = 1199 := by decide

def c1199 : Contract := original1199.toContract.get (by decide)
theorem binding1199 : original1199.toContract = some c1199 := rfl

theorem checked1199 : check 4000 c1199 = true := by decide

def original1200 : RawOriginal := C009.records[48]'(by decide)
theorem original_id1200 : original1200.index = 1200 := by decide

def c1200 : Contract := original1200.toContract.get (by decide)
theorem binding1200 : original1200.toContract = some c1200 := rfl

theorem checked1200 : check 4000 c1200 = true := by decide

def original1201 : RawOriginal := C009.records[49]'(by decide)
theorem original_id1201 : original1201.index = 1201 := by decide

def c1201 : Contract := original1201.toContract.get (by decide)
theorem binding1201 : original1201.toContract = some c1201 := rfl

theorem checked1201 : check 4000 c1201 = true := by decide

def original1202 : RawOriginal := C009.records[50]'(by decide)
theorem original_id1202 : original1202.index = 1202 := by decide

def c1202 : Contract := original1202.toContract.get (by decide)
theorem binding1202 : original1202.toContract = some c1202 := rfl

theorem checked1202 : check 4000 c1202 = true := by decide

def original1203 : RawOriginal := C009.records[51]'(by decide)
theorem original_id1203 : original1203.index = 1203 := by decide

def c1203 : Contract := original1203.toContract.get (by decide)
theorem binding1203 : original1203.toContract = some c1203 := rfl

theorem checked1203 : check 4000 c1203 = true := by decide

def original1204 : RawOriginal := C009.records[52]'(by decide)
theorem original_id1204 : original1204.index = 1204 := by decide

def c1204 : Contract := original1204.toContract.get (by decide)
theorem binding1204 : original1204.toContract = some c1204 := rfl

theorem checked1204 : check 4000 c1204 = true := by decide

def original1205 : RawOriginal := C009.records[53]'(by decide)
theorem original_id1205 : original1205.index = 1205 := by decide

def c1205 : Contract := original1205.toContract.get (by decide)
theorem binding1205 : original1205.toContract = some c1205 := rfl

theorem checked1205 : check 4000 c1205 = true := by decide

def records : List Certified := [
  ⟨1190, c1190, 4000, checked1190⟩,
  ⟨1191, c1191, 4000, checked1191⟩,
  ⟨1192, c1192, 4000, checked1192⟩,
  ⟨1193, c1193, 4000, checked1193⟩,
  ⟨1194, c1194, 4000, checked1194⟩,
  ⟨1195, c1195, 4000, checked1195⟩,
  ⟨1196, c1196, 4000, checked1196⟩,
  ⟨1197, c1197, 4000, checked1197⟩,
  ⟨1198, c1198, 4000, checked1198⟩,
  ⟨1199, c1199, 4000, checked1199⟩,
  ⟨1200, c1200, 4000, checked1200⟩,
  ⟨1201, c1201, 4000, checked1201⟩,
  ⟨1202, c1202, 4000, checked1202⟩,
  ⟨1203, c1203, 4000, checked1203⟩,
  ⟨1204, c1204, 4000, checked1204⟩,
  ⟨1205, c1205, 4000, checked1205⟩]

end PA215.ContractShards.Shard009Part2
