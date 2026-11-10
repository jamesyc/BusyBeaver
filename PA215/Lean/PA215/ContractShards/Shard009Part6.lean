import PA215.CertifiedContracts
import PA215.Census.C009
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard009Part6
open PA215.Contracts PA215.Census

def original1254 : RawOriginal := C009.records[102]'(by decide)
theorem original_id1254 : original1254.index = 1254 := by decide

def c1254 : Contract := original1254.toContract.get (by decide)
theorem binding1254 : original1254.toContract = some c1254 := rfl

theorem checked1254 : check 4000 c1254 = true := by decide

def original1255 : RawOriginal := C009.records[103]'(by decide)
theorem original_id1255 : original1255.index = 1255 := by decide

def c1255 : Contract := original1255.toContract.get (by decide)
theorem binding1255 : original1255.toContract = some c1255 := rfl

theorem checked1255 : check 4000 c1255 = true := by decide

def original1256 : RawOriginal := C009.records[104]'(by decide)
theorem original_id1256 : original1256.index = 1256 := by decide

def c1256 : Contract := original1256.toContract.get (by decide)
theorem binding1256 : original1256.toContract = some c1256 := rfl

theorem checked1256 : check 4000 c1256 = true := by decide

def original1257 : RawOriginal := C009.records[105]'(by decide)
theorem original_id1257 : original1257.index = 1257 := by decide

def c1257 : Contract := original1257.toContract.get (by decide)
theorem binding1257 : original1257.toContract = some c1257 := rfl

theorem checked1257 : check 4000 c1257 = true := by decide

def original1258 : RawOriginal := C009.records[106]'(by decide)
theorem original_id1258 : original1258.index = 1258 := by decide

def c1258 : Contract := original1258.toContract.get (by decide)
theorem binding1258 : original1258.toContract = some c1258 := rfl

theorem checked1258 : check 4000 c1258 = true := by decide

def original1259 : RawOriginal := C009.records[107]'(by decide)
theorem original_id1259 : original1259.index = 1259 := by decide

def c1259 : Contract := original1259.toContract.get (by decide)
theorem binding1259 : original1259.toContract = some c1259 := rfl

theorem checked1259 : check 4000 c1259 = true := by decide

def original1260 : RawOriginal := C009.records[108]'(by decide)
theorem original_id1260 : original1260.index = 1260 := by decide

def c1260 : Contract := original1260.toContract.get (by decide)
theorem binding1260 : original1260.toContract = some c1260 := rfl

theorem checked1260 : check 4000 c1260 = true := by decide

def original1261 : RawOriginal := C009.records[109]'(by decide)
theorem original_id1261 : original1261.index = 1261 := by decide

def c1261 : Contract := original1261.toContract.get (by decide)
theorem binding1261 : original1261.toContract = some c1261 := rfl

theorem checked1261 : check 4000 c1261 = true := by decide

def original1262 : RawOriginal := C009.records[110]'(by decide)
theorem original_id1262 : original1262.index = 1262 := by decide

def c1262 : Contract := original1262.toContract.get (by decide)
theorem binding1262 : original1262.toContract = some c1262 := rfl

theorem checked1262 : check 4000 c1262 = true := by decide

def original1263 : RawOriginal := C009.records[111]'(by decide)
theorem original_id1263 : original1263.index = 1263 := by decide

def c1263 : Contract := original1263.toContract.get (by decide)
theorem binding1263 : original1263.toContract = some c1263 := rfl

theorem checked1263 : check 4000 c1263 = true := by decide

def original1264 : RawOriginal := C009.records[112]'(by decide)
theorem original_id1264 : original1264.index = 1264 := by decide

def c1264 : Contract := original1264.toContract.get (by decide)
theorem binding1264 : original1264.toContract = some c1264 := rfl

theorem checked1264 : check 4000 c1264 = true := by decide

def original1265 : RawOriginal := C009.records[113]'(by decide)
theorem original_id1265 : original1265.index = 1265 := by decide

def c1265 : Contract := original1265.toContract.get (by decide)
theorem binding1265 : original1265.toContract = some c1265 := rfl

theorem checked1265 : check 4000 c1265 = true := by decide

def original1266 : RawOriginal := C009.records[114]'(by decide)
theorem original_id1266 : original1266.index = 1266 := by decide

def c1266 : Contract := original1266.toContract.get (by decide)
theorem binding1266 : original1266.toContract = some c1266 := rfl

theorem checked1266 : check 4000 c1266 = true := by decide

def original1267 : RawOriginal := C009.records[115]'(by decide)
theorem original_id1267 : original1267.index = 1267 := by decide

def c1267 : Contract := original1267.toContract.get (by decide)
theorem binding1267 : original1267.toContract = some c1267 := rfl

theorem checked1267 : check 4000 c1267 = true := by decide

def original1268 : RawOriginal := C009.records[116]'(by decide)
theorem original_id1268 : original1268.index = 1268 := by decide

def c1268 : Contract := original1268.toContract.get (by decide)
theorem binding1268 : original1268.toContract = some c1268 := rfl

theorem checked1268 : check 4000 c1268 = true := by decide

def original1269 : RawOriginal := C009.records[117]'(by decide)
theorem original_id1269 : original1269.index = 1269 := by decide

def c1269 : Contract := original1269.toContract.get (by decide)
theorem binding1269 : original1269.toContract = some c1269 := rfl

theorem checked1269 : check 4000 c1269 = true := by decide

def records : List Certified := [
  ⟨1254, c1254, 4000, checked1254⟩,
  ⟨1255, c1255, 4000, checked1255⟩,
  ⟨1256, c1256, 4000, checked1256⟩,
  ⟨1257, c1257, 4000, checked1257⟩,
  ⟨1258, c1258, 4000, checked1258⟩,
  ⟨1259, c1259, 4000, checked1259⟩,
  ⟨1260, c1260, 4000, checked1260⟩,
  ⟨1261, c1261, 4000, checked1261⟩,
  ⟨1262, c1262, 4000, checked1262⟩,
  ⟨1263, c1263, 4000, checked1263⟩,
  ⟨1264, c1264, 4000, checked1264⟩,
  ⟨1265, c1265, 4000, checked1265⟩,
  ⟨1266, c1266, 4000, checked1266⟩,
  ⟨1267, c1267, 4000, checked1267⟩,
  ⟨1268, c1268, 4000, checked1268⟩,
  ⟨1269, c1269, 4000, checked1269⟩]

end PA215.ContractShards.Shard009Part6
