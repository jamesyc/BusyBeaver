import PA215.CertifiedContracts
import PA215.Census.C007
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard007Part2
open PA215.Contracts PA215.Census

def original934 : RawOriginal := C007.records[38]'(by decide)
theorem original_id934 : original934.index = 934 := by decide

def c934 : Contract := original934.toContract.get (by decide)
theorem binding934 : original934.toContract = some c934 := rfl

theorem checked934 : check 4000 c934 = true := by decide

def original935 : RawOriginal := C007.records[39]'(by decide)
theorem original_id935 : original935.index = 935 := by decide

def c935 : Contract := original935.toContract.get (by decide)
theorem binding935 : original935.toContract = some c935 := rfl

theorem checked935 : check 4000 c935 = true := by decide

def original936 : RawOriginal := C007.records[40]'(by decide)
theorem original_id936 : original936.index = 936 := by decide

def c936 : Contract := original936.toContract.get (by decide)
theorem binding936 : original936.toContract = some c936 := rfl

theorem checked936 : check 4000 c936 = true := by decide

def original937 : RawOriginal := C007.records[41]'(by decide)
theorem original_id937 : original937.index = 937 := by decide

def c937 : Contract := original937.toContract.get (by decide)
theorem binding937 : original937.toContract = some c937 := rfl

theorem checked937 : check 4000 c937 = true := by decide

def original938 : RawOriginal := C007.records[42]'(by decide)
theorem original_id938 : original938.index = 938 := by decide

def c938 : Contract := original938.toContract.get (by decide)
theorem binding938 : original938.toContract = some c938 := rfl

theorem checked938 : check 4000 c938 = true := by decide

def original939 : RawOriginal := C007.records[43]'(by decide)
theorem original_id939 : original939.index = 939 := by decide

def c939 : Contract := original939.toContract.get (by decide)
theorem binding939 : original939.toContract = some c939 := rfl

theorem checked939 : check 4000 c939 = true := by decide

def original940 : RawOriginal := C007.records[44]'(by decide)
theorem original_id940 : original940.index = 940 := by decide

def c940 : Contract := original940.toContract.get (by decide)
theorem binding940 : original940.toContract = some c940 := rfl

theorem checked940 : check 4000 c940 = true := by decide

def original941 : RawOriginal := C007.records[45]'(by decide)
theorem original_id941 : original941.index = 941 := by decide

def c941 : Contract := original941.toContract.get (by decide)
theorem binding941 : original941.toContract = some c941 := rfl

theorem checked941 : check 4000 c941 = true := by decide

def original942 : RawOriginal := C007.records[46]'(by decide)
theorem original_id942 : original942.index = 942 := by decide

def c942 : Contract := original942.toContract.get (by decide)
theorem binding942 : original942.toContract = some c942 := rfl

theorem checked942 : check 4000 c942 = true := by decide

def original943 : RawOriginal := C007.records[47]'(by decide)
theorem original_id943 : original943.index = 943 := by decide

def c943 : Contract := original943.toContract.get (by decide)
theorem binding943 : original943.toContract = some c943 := rfl

theorem checked943 : check 4000 c943 = true := by decide

def original944 : RawOriginal := C007.records[48]'(by decide)
theorem original_id944 : original944.index = 944 := by decide

def c944 : Contract := original944.toContract.get (by decide)
theorem binding944 : original944.toContract = some c944 := rfl

theorem checked944 : check 4000 c944 = true := by decide

def original945 : RawOriginal := C007.records[49]'(by decide)
theorem original_id945 : original945.index = 945 := by decide

def c945 : Contract := original945.toContract.get (by decide)
theorem binding945 : original945.toContract = some c945 := rfl

theorem checked945 : check 4000 c945 = true := by decide

def original946 : RawOriginal := C007.records[50]'(by decide)
theorem original_id946 : original946.index = 946 := by decide

def c946 : Contract := original946.toContract.get (by decide)
theorem binding946 : original946.toContract = some c946 := rfl

theorem checked946 : check 4000 c946 = true := by decide

def original947 : RawOriginal := C007.records[51]'(by decide)
theorem original_id947 : original947.index = 947 := by decide

def c947 : Contract := original947.toContract.get (by decide)
theorem binding947 : original947.toContract = some c947 := rfl

theorem checked947 : check 4000 c947 = true := by decide

def original948 : RawOriginal := C007.records[52]'(by decide)
theorem original_id948 : original948.index = 948 := by decide

def c948 : Contract := original948.toContract.get (by decide)
theorem binding948 : original948.toContract = some c948 := rfl

theorem checked948 : check 4000 c948 = true := by decide

def original949 : RawOriginal := C007.records[53]'(by decide)
theorem original_id949 : original949.index = 949 := by decide

def c949 : Contract := original949.toContract.get (by decide)
theorem binding949 : original949.toContract = some c949 := rfl

theorem checked949 : check 4000 c949 = true := by decide

def records : List Certified := [
  ⟨934, c934, 4000, checked934⟩,
  ⟨935, c935, 4000, checked935⟩,
  ⟨936, c936, 4000, checked936⟩,
  ⟨937, c937, 4000, checked937⟩,
  ⟨938, c938, 4000, checked938⟩,
  ⟨939, c939, 4000, checked939⟩,
  ⟨940, c940, 4000, checked940⟩,
  ⟨941, c941, 4000, checked941⟩,
  ⟨942, c942, 4000, checked942⟩,
  ⟨943, c943, 4000, checked943⟩,
  ⟨944, c944, 4000, checked944⟩,
  ⟨945, c945, 4000, checked945⟩,
  ⟨946, c946, 4000, checked946⟩,
  ⟨947, c947, 4000, checked947⟩,
  ⟨948, c948, 4000, checked948⟩,
  ⟨949, c949, 4000, checked949⟩]

end PA215.ContractShards.Shard007Part2
