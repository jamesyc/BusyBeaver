import PA213.StartupData
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA213.Startup
open PA215.Zip PA213.CandidateTable

theorem run176 : run machine 256 checkpoint176 = some checkpoint177 := by decide +kernel
theorem reach176 : Reach machine checkpoint176 checkpoint177 := ⟨256, run176⟩

theorem run177 : run machine 256 checkpoint177 = some checkpoint178 := by decide +kernel
theorem reach177 : Reach machine checkpoint177 checkpoint178 := ⟨256, run177⟩

theorem run178 : run machine 256 checkpoint178 = some checkpoint179 := by decide +kernel
theorem reach178 : Reach machine checkpoint178 checkpoint179 := ⟨256, run178⟩

theorem run179 : run machine 256 checkpoint179 = some checkpoint180 := by decide +kernel
theorem reach179 : Reach machine checkpoint179 checkpoint180 := ⟨256, run179⟩

theorem run180 : run machine 256 checkpoint180 = some checkpoint181 := by decide +kernel
theorem reach180 : Reach machine checkpoint180 checkpoint181 := ⟨256, run180⟩

theorem run181 : run machine 256 checkpoint181 = some checkpoint182 := by decide +kernel
theorem reach181 : Reach machine checkpoint181 checkpoint182 := ⟨256, run181⟩

theorem run182 : run machine 256 checkpoint182 = some checkpoint183 := by decide +kernel
theorem reach182 : Reach machine checkpoint182 checkpoint183 := ⟨256, run182⟩

theorem run183 : run machine 256 checkpoint183 = some checkpoint184 := by decide +kernel
theorem reach183 : Reach machine checkpoint183 checkpoint184 := ⟨256, run183⟩

theorem run184 : run machine 256 checkpoint184 = some checkpoint185 := by decide +kernel
theorem reach184 : Reach machine checkpoint184 checkpoint185 := ⟨256, run184⟩

theorem run185 : run machine 256 checkpoint185 = some checkpoint186 := by decide +kernel
theorem reach185 : Reach machine checkpoint185 checkpoint186 := ⟨256, run185⟩

theorem run186 : run machine 256 checkpoint186 = some checkpoint187 := by decide +kernel
theorem reach186 : Reach machine checkpoint186 checkpoint187 := ⟨256, run186⟩

theorem run187 : run machine 256 checkpoint187 = some checkpoint188 := by decide +kernel
theorem reach187 : Reach machine checkpoint187 checkpoint188 := ⟨256, run187⟩

theorem run188 : run machine 256 checkpoint188 = some checkpoint189 := by decide +kernel
theorem reach188 : Reach machine checkpoint188 checkpoint189 := ⟨256, run188⟩

theorem run189 : run machine 256 checkpoint189 = some checkpoint190 := by decide +kernel
theorem reach189 : Reach machine checkpoint189 checkpoint190 := ⟨256, run189⟩

theorem run190 : run machine 256 checkpoint190 = some checkpoint191 := by decide +kernel
theorem reach190 : Reach machine checkpoint190 checkpoint191 := ⟨256, run190⟩

theorem run191 : run machine 256 checkpoint191 = some checkpoint192 := by decide +kernel
theorem reach191 : Reach machine checkpoint191 checkpoint192 := ⟨256, run191⟩

end PA213.Startup
