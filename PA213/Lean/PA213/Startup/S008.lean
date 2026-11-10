import PA213.StartupData
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA213.Startup
open PA215.Zip PA213.CandidateTable

theorem run128 : run machine 256 checkpoint128 = some checkpoint129 := by decide +kernel
theorem reach128 : Reach machine checkpoint128 checkpoint129 := ⟨256, run128⟩

theorem run129 : run machine 256 checkpoint129 = some checkpoint130 := by decide +kernel
theorem reach129 : Reach machine checkpoint129 checkpoint130 := ⟨256, run129⟩

theorem run130 : run machine 256 checkpoint130 = some checkpoint131 := by decide +kernel
theorem reach130 : Reach machine checkpoint130 checkpoint131 := ⟨256, run130⟩

theorem run131 : run machine 256 checkpoint131 = some checkpoint132 := by decide +kernel
theorem reach131 : Reach machine checkpoint131 checkpoint132 := ⟨256, run131⟩

theorem run132 : run machine 256 checkpoint132 = some checkpoint133 := by decide +kernel
theorem reach132 : Reach machine checkpoint132 checkpoint133 := ⟨256, run132⟩

theorem run133 : run machine 256 checkpoint133 = some checkpoint134 := by decide +kernel
theorem reach133 : Reach machine checkpoint133 checkpoint134 := ⟨256, run133⟩

theorem run134 : run machine 256 checkpoint134 = some checkpoint135 := by decide +kernel
theorem reach134 : Reach machine checkpoint134 checkpoint135 := ⟨256, run134⟩

theorem run135 : run machine 256 checkpoint135 = some checkpoint136 := by decide +kernel
theorem reach135 : Reach machine checkpoint135 checkpoint136 := ⟨256, run135⟩

theorem run136 : run machine 256 checkpoint136 = some checkpoint137 := by decide +kernel
theorem reach136 : Reach machine checkpoint136 checkpoint137 := ⟨256, run136⟩

theorem run137 : run machine 256 checkpoint137 = some checkpoint138 := by decide +kernel
theorem reach137 : Reach machine checkpoint137 checkpoint138 := ⟨256, run137⟩

theorem run138 : run machine 256 checkpoint138 = some checkpoint139 := by decide +kernel
theorem reach138 : Reach machine checkpoint138 checkpoint139 := ⟨256, run138⟩

theorem run139 : run machine 256 checkpoint139 = some checkpoint140 := by decide +kernel
theorem reach139 : Reach machine checkpoint139 checkpoint140 := ⟨256, run139⟩

theorem run140 : run machine 256 checkpoint140 = some checkpoint141 := by decide +kernel
theorem reach140 : Reach machine checkpoint140 checkpoint141 := ⟨256, run140⟩

theorem run141 : run machine 256 checkpoint141 = some checkpoint142 := by decide +kernel
theorem reach141 : Reach machine checkpoint141 checkpoint142 := ⟨256, run141⟩

theorem run142 : run machine 256 checkpoint142 = some checkpoint143 := by decide +kernel
theorem reach142 : Reach machine checkpoint142 checkpoint143 := ⟨256, run142⟩

theorem run143 : run machine 256 checkpoint143 = some checkpoint144 := by decide +kernel
theorem reach143 : Reach machine checkpoint143 checkpoint144 := ⟨256, run143⟩

end PA213.Startup
