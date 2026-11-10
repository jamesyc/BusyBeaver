import PA213.StartupData
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA213.Startup
open PA215.Zip PA213.CandidateTable

theorem run224 : run machine 256 checkpoint224 = some checkpoint225 := by decide +kernel
theorem reach224 : Reach machine checkpoint224 checkpoint225 := ⟨256, run224⟩

theorem run225 : run machine 256 checkpoint225 = some checkpoint226 := by decide +kernel
theorem reach225 : Reach machine checkpoint225 checkpoint226 := ⟨256, run225⟩

theorem run226 : run machine 256 checkpoint226 = some checkpoint227 := by decide +kernel
theorem reach226 : Reach machine checkpoint226 checkpoint227 := ⟨256, run226⟩

theorem run227 : run machine 256 checkpoint227 = some checkpoint228 := by decide +kernel
theorem reach227 : Reach machine checkpoint227 checkpoint228 := ⟨256, run227⟩

theorem run228 : run machine 256 checkpoint228 = some checkpoint229 := by decide +kernel
theorem reach228 : Reach machine checkpoint228 checkpoint229 := ⟨256, run228⟩

theorem run229 : run machine 256 checkpoint229 = some checkpoint230 := by decide +kernel
theorem reach229 : Reach machine checkpoint229 checkpoint230 := ⟨256, run229⟩

theorem run230 : run machine 256 checkpoint230 = some checkpoint231 := by decide +kernel
theorem reach230 : Reach machine checkpoint230 checkpoint231 := ⟨256, run230⟩

theorem run231 : run machine 256 checkpoint231 = some checkpoint232 := by decide +kernel
theorem reach231 : Reach machine checkpoint231 checkpoint232 := ⟨256, run231⟩

theorem run232 : run machine 256 checkpoint232 = some checkpoint233 := by decide +kernel
theorem reach232 : Reach machine checkpoint232 checkpoint233 := ⟨256, run232⟩

theorem run233 : run machine 256 checkpoint233 = some checkpoint234 := by decide +kernel
theorem reach233 : Reach machine checkpoint233 checkpoint234 := ⟨256, run233⟩

theorem run234 : run machine 256 checkpoint234 = some checkpoint235 := by decide +kernel
theorem reach234 : Reach machine checkpoint234 checkpoint235 := ⟨256, run234⟩

theorem run235 : run machine 256 checkpoint235 = some checkpoint236 := by decide +kernel
theorem reach235 : Reach machine checkpoint235 checkpoint236 := ⟨256, run235⟩

theorem run236 : run machine 256 checkpoint236 = some checkpoint237 := by decide +kernel
theorem reach236 : Reach machine checkpoint236 checkpoint237 := ⟨256, run236⟩

theorem run237 : run machine 256 checkpoint237 = some checkpoint238 := by decide +kernel
theorem reach237 : Reach machine checkpoint237 checkpoint238 := ⟨256, run237⟩

theorem run238 : run machine 256 checkpoint238 = some checkpoint239 := by decide +kernel
theorem reach238 : Reach machine checkpoint238 checkpoint239 := ⟨256, run238⟩

theorem run239 : run machine 256 checkpoint239 = some checkpoint240 := by decide +kernel
theorem reach239 : Reach machine checkpoint239 checkpoint240 := ⟨256, run239⟩

end PA213.Startup
