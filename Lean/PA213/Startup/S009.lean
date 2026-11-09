module

public import PA213.StartupData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA213.Startup
open PA215.Zip PA213.CandidateTable

theorem run144 : run machine 256 checkpoint144 = some checkpoint145 := by decide +kernel
theorem reach144 : Reach machine checkpoint144 checkpoint145 := ⟨256, run144⟩

theorem run145 : run machine 256 checkpoint145 = some checkpoint146 := by decide +kernel
theorem reach145 : Reach machine checkpoint145 checkpoint146 := ⟨256, run145⟩

theorem run146 : run machine 256 checkpoint146 = some checkpoint147 := by decide +kernel
theorem reach146 : Reach machine checkpoint146 checkpoint147 := ⟨256, run146⟩

theorem run147 : run machine 256 checkpoint147 = some checkpoint148 := by decide +kernel
theorem reach147 : Reach machine checkpoint147 checkpoint148 := ⟨256, run147⟩

theorem run148 : run machine 256 checkpoint148 = some checkpoint149 := by decide +kernel
theorem reach148 : Reach machine checkpoint148 checkpoint149 := ⟨256, run148⟩

theorem run149 : run machine 256 checkpoint149 = some checkpoint150 := by decide +kernel
theorem reach149 : Reach machine checkpoint149 checkpoint150 := ⟨256, run149⟩

theorem run150 : run machine 256 checkpoint150 = some checkpoint151 := by decide +kernel
theorem reach150 : Reach machine checkpoint150 checkpoint151 := ⟨256, run150⟩

theorem run151 : run machine 256 checkpoint151 = some checkpoint152 := by decide +kernel
theorem reach151 : Reach machine checkpoint151 checkpoint152 := ⟨256, run151⟩

theorem run152 : run machine 256 checkpoint152 = some checkpoint153 := by decide +kernel
theorem reach152 : Reach machine checkpoint152 checkpoint153 := ⟨256, run152⟩

theorem run153 : run machine 256 checkpoint153 = some checkpoint154 := by decide +kernel
theorem reach153 : Reach machine checkpoint153 checkpoint154 := ⟨256, run153⟩

theorem run154 : run machine 256 checkpoint154 = some checkpoint155 := by decide +kernel
theorem reach154 : Reach machine checkpoint154 checkpoint155 := ⟨256, run154⟩

theorem run155 : run machine 256 checkpoint155 = some checkpoint156 := by decide +kernel
theorem reach155 : Reach machine checkpoint155 checkpoint156 := ⟨256, run155⟩

theorem run156 : run machine 256 checkpoint156 = some checkpoint157 := by decide +kernel
theorem reach156 : Reach machine checkpoint156 checkpoint157 := ⟨256, run156⟩

theorem run157 : run machine 256 checkpoint157 = some checkpoint158 := by decide +kernel
theorem reach157 : Reach machine checkpoint157 checkpoint158 := ⟨256, run157⟩

theorem run158 : run machine 256 checkpoint158 = some checkpoint159 := by decide +kernel
theorem reach158 : Reach machine checkpoint158 checkpoint159 := ⟨256, run158⟩

theorem run159 : run machine 256 checkpoint159 = some checkpoint160 := by decide +kernel
theorem reach159 : Reach machine checkpoint159 checkpoint160 := ⟨256, run159⟩

end PA213.Startup
