import PA213.StartupData
import PA211.UserCandidate.CandidateTable
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.Startup
open PA215.Zip PA213.Startup PA211.UserCandidate.CandidateTable

theorem run096 : run machine 256 checkpoint096 = some checkpoint097 := by decide +kernel
theorem reach096 : Reach machine checkpoint096 checkpoint097 := ⟨256, run096⟩

theorem run097 : run machine 256 checkpoint097 = some checkpoint098 := by decide +kernel
theorem reach097 : Reach machine checkpoint097 checkpoint098 := ⟨256, run097⟩

theorem run098 : run machine 256 checkpoint098 = some checkpoint099 := by decide +kernel
theorem reach098 : Reach machine checkpoint098 checkpoint099 := ⟨256, run098⟩

theorem run099 : run machine 256 checkpoint099 = some checkpoint100 := by decide +kernel
theorem reach099 : Reach machine checkpoint099 checkpoint100 := ⟨256, run099⟩

theorem run100 : run machine 256 checkpoint100 = some checkpoint101 := by decide +kernel
theorem reach100 : Reach machine checkpoint100 checkpoint101 := ⟨256, run100⟩

theorem run101 : run machine 256 checkpoint101 = some checkpoint102 := by decide +kernel
theorem reach101 : Reach machine checkpoint101 checkpoint102 := ⟨256, run101⟩

theorem run102 : run machine 256 checkpoint102 = some checkpoint103 := by decide +kernel
theorem reach102 : Reach machine checkpoint102 checkpoint103 := ⟨256, run102⟩

theorem run103 : run machine 256 checkpoint103 = some checkpoint104 := by decide +kernel
theorem reach103 : Reach machine checkpoint103 checkpoint104 := ⟨256, run103⟩

theorem run104 : run machine 256 checkpoint104 = some checkpoint105 := by decide +kernel
theorem reach104 : Reach machine checkpoint104 checkpoint105 := ⟨256, run104⟩

theorem run105 : run machine 256 checkpoint105 = some checkpoint106 := by decide +kernel
theorem reach105 : Reach machine checkpoint105 checkpoint106 := ⟨256, run105⟩

theorem run106 : run machine 256 checkpoint106 = some checkpoint107 := by decide +kernel
theorem reach106 : Reach machine checkpoint106 checkpoint107 := ⟨256, run106⟩

theorem run107 : run machine 256 checkpoint107 = some checkpoint108 := by decide +kernel
theorem reach107 : Reach machine checkpoint107 checkpoint108 := ⟨256, run107⟩

theorem run108 : run machine 256 checkpoint108 = some checkpoint109 := by decide +kernel
theorem reach108 : Reach machine checkpoint108 checkpoint109 := ⟨256, run108⟩

theorem run109 : run machine 256 checkpoint109 = some checkpoint110 := by decide +kernel
theorem reach109 : Reach machine checkpoint109 checkpoint110 := ⟨256, run109⟩

theorem run110 : run machine 256 checkpoint110 = some checkpoint111 := by decide +kernel
theorem reach110 : Reach machine checkpoint110 checkpoint111 := ⟨256, run110⟩

theorem run111 : run machine 256 checkpoint111 = some checkpoint112 := by decide +kernel
theorem reach111 : Reach machine checkpoint111 checkpoint112 := ⟨256, run111⟩

end PA211.UserCandidate.Startup
