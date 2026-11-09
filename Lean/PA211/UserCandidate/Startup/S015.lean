module

public import PA213.StartupData
public import PA211.UserCandidate.CandidateTable

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.Startup
open PA215.Zip PA213.Startup PA211.UserCandidate.CandidateTable

theorem run240 : run machine 256 checkpoint240 = some checkpoint241 := by decide +kernel
theorem reach240 : Reach machine checkpoint240 checkpoint241 := ⟨256, run240⟩

theorem run241 : run machine 256 checkpoint241 = some checkpoint242 := by decide +kernel
theorem reach241 : Reach machine checkpoint241 checkpoint242 := ⟨256, run241⟩

theorem run242 : run machine 256 checkpoint242 = some checkpoint243 := by decide +kernel
theorem reach242 : Reach machine checkpoint242 checkpoint243 := ⟨256, run242⟩

theorem run243 : run machine 256 checkpoint243 = some checkpoint244 := by decide +kernel
theorem reach243 : Reach machine checkpoint243 checkpoint244 := ⟨256, run243⟩

theorem run244 : run machine 256 checkpoint244 = some checkpoint245 := by decide +kernel
theorem reach244 : Reach machine checkpoint244 checkpoint245 := ⟨256, run244⟩

theorem run245 : run machine 256 checkpoint245 = some checkpoint246 := by decide +kernel
theorem reach245 : Reach machine checkpoint245 checkpoint246 := ⟨256, run245⟩

theorem run246 : run machine 256 checkpoint246 = some checkpoint247 := by decide +kernel
theorem reach246 : Reach machine checkpoint246 checkpoint247 := ⟨256, run246⟩

theorem run247 : run machine 256 checkpoint247 = some checkpoint248 := by decide +kernel
theorem reach247 : Reach machine checkpoint247 checkpoint248 := ⟨256, run247⟩

theorem run248 : run machine 256 checkpoint248 = some checkpoint249 := by decide +kernel
theorem reach248 : Reach machine checkpoint248 checkpoint249 := ⟨256, run248⟩

theorem run249 : run machine 256 checkpoint249 = some checkpoint250 := by decide +kernel
theorem reach249 : Reach machine checkpoint249 checkpoint250 := ⟨256, run249⟩

theorem run250 : run machine 256 checkpoint250 = some checkpoint251 := by decide +kernel
theorem reach250 : Reach machine checkpoint250 checkpoint251 := ⟨256, run250⟩

theorem run251 : run machine 256 checkpoint251 = some checkpoint252 := by decide +kernel
theorem reach251 : Reach machine checkpoint251 checkpoint252 := ⟨256, run251⟩

theorem run252 : run machine 252 checkpoint252 = some checkpoint253 := by decide +kernel
theorem reach252 : Reach machine checkpoint252 checkpoint253 := ⟨252, run252⟩

end PA211.UserCandidate.Startup
