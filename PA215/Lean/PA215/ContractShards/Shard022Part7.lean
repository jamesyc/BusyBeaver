import PA215.FastNativeTable
import PA215.CertifiedContracts
import PA215.Census.C022
import PA215.Census.C023
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard022Part7
open PA215.Contracts PA215.Census

def original2934 : RawOriginal := C022.records[118]'(by decide)
theorem original_id2934 : original2934.index = 2934 := by decide

def c2934 : Contract := original2934.toContract.get (by decide)
theorem binding2934 : original2934.toContract = some c2934 := rfl

theorem checked2934 : check 4000 c2934 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2935 : RawOriginal := C022.records[119]'(by decide)
theorem original_id2935 : original2935.index = 2935 := by decide

def c2935 : Contract := original2935.toContract.get (by decide)
theorem binding2935 : original2935.toContract = some c2935 := rfl

theorem checked2935 : check 4000 c2935 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2936 : RawOriginal := C022.records[120]'(by decide)
theorem original_id2936 : original2936.index = 2936 := by decide

def c2936 : Contract := original2936.toContract.get (by decide)
theorem binding2936 : original2936.toContract = some c2936 := rfl

theorem checked2936 : check 4000 c2936 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2937 : RawOriginal := C022.records[121]'(by decide)
theorem original_id2937 : original2937.index = 2937 := by decide

def c2937 : Contract := original2937.toContract.get (by decide)
theorem binding2937 : original2937.toContract = some c2937 := rfl

theorem checked2937 : check 4000 c2937 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2938 : RawOriginal := C022.records[122]'(by decide)
theorem original_id2938 : original2938.index = 2938 := by decide

def c2938 : Contract := original2938.toContract.get (by decide)
theorem binding2938 : original2938.toContract = some c2938 := rfl

theorem checked2938 : check 4000 c2938 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2939 : RawOriginal := C022.records[123]'(by decide)
theorem original_id2939 : original2939.index = 2939 := by decide

def c2939 : Contract := original2939.toContract.get (by decide)
theorem binding2939 : original2939.toContract = some c2939 := rfl

theorem checked2939 : check 4000 c2939 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2940 : RawOriginal := C022.records[124]'(by decide)
theorem original_id2940 : original2940.index = 2940 := by decide

def c2940 : Contract := original2940.toContract.get (by decide)
theorem binding2940 : original2940.toContract = some c2940 := rfl

theorem checked2940 : check 4000 c2940 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2941 : RawOriginal := C022.records[125]'(by decide)
theorem original_id2941 : original2941.index = 2941 := by decide

def c2941 : Contract := original2941.toContract.get (by decide)
theorem binding2941 : original2941.toContract = some c2941 := rfl

theorem checked2941 : check 4000 c2941 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2942 : RawOriginal := C022.records[126]'(by decide)
theorem original_id2942 : original2942.index = 2942 := by decide

def c2942 : Contract := original2942.toContract.get (by decide)
theorem binding2942 : original2942.toContract = some c2942 := rfl

theorem checked2942 : check 4000 c2942 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2943 : RawOriginal := C022.records[127]'(by decide)
theorem original_id2943 : original2943.index = 2943 := by decide

def c2943 : Contract := original2943.toContract.get (by decide)
theorem binding2943 : original2943.toContract = some c2943 := rfl

theorem checked2943 : check 4000 c2943 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2944 : RawOriginal := C023.records[0]'(by decide)
theorem original_id2944 : original2944.index = 2944 := by decide

def c2944 : Contract := original2944.toContract.get (by decide)
theorem binding2944 : original2944.toContract = some c2944 := rfl

theorem checked2944 : check 4000 c2944 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2945 : RawOriginal := C023.records[1]'(by decide)
theorem original_id2945 : original2945.index = 2945 := by decide

def c2945 : Contract := original2945.toContract.get (by decide)
theorem binding2945 : original2945.toContract = some c2945 := rfl

theorem checked2945 : check 4000 c2945 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2946 : RawOriginal := C023.records[2]'(by decide)
theorem original_id2946 : original2946.index = 2946 := by decide

def c2946 : Contract := original2946.toContract.get (by decide)
theorem binding2946 : original2946.toContract = some c2946 := rfl

theorem checked2946 : check 4000 c2946 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2947 : RawOriginal := C023.records[3]'(by decide)
theorem original_id2947 : original2947.index = 2947 := by decide

def c2947 : Contract := original2947.toContract.get (by decide)
theorem binding2947 : original2947.toContract = some c2947 := rfl

theorem checked2947 : check 4000 c2947 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2948 : RawOriginal := C023.records[4]'(by decide)
theorem original_id2948 : original2948.index = 2948 := by decide

def c2948 : Contract := original2948.toContract.get (by decide)
theorem binding2948 : original2948.toContract = some c2948 := rfl

theorem checked2948 : check 4000 c2948 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def original2949 : RawOriginal := C023.records[5]'(by decide)
theorem original_id2949 : original2949.index = 2949 := by decide

def c2949 : Contract := original2949.toContract.get (by decide)
theorem binding2949 : original2949.toContract = some c2949 := rfl

theorem checked2949 : check 4000 c2949 = true := by
  rw [← PA215.FastNativeTable.fastCheck_eq_check]
  decide

def records : List Certified := [
  ⟨2934, c2934, 4000, checked2934⟩,
  ⟨2935, c2935, 4000, checked2935⟩,
  ⟨2936, c2936, 4000, checked2936⟩,
  ⟨2937, c2937, 4000, checked2937⟩,
  ⟨2938, c2938, 4000, checked2938⟩,
  ⟨2939, c2939, 4000, checked2939⟩,
  ⟨2940, c2940, 4000, checked2940⟩,
  ⟨2941, c2941, 4000, checked2941⟩,
  ⟨2942, c2942, 4000, checked2942⟩,
  ⟨2943, c2943, 4000, checked2943⟩,
  ⟨2944, c2944, 4000, checked2944⟩,
  ⟨2945, c2945, 4000, checked2945⟩,
  ⟨2946, c2946, 4000, checked2946⟩,
  ⟨2947, c2947, 4000, checked2947⟩,
  ⟨2948, c2948, 4000, checked2948⟩,
  ⟨2949, c2949, 4000, checked2949⟩]

end PA215.ContractShards.Shard022Part7
