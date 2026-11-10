import PA213.StartupData
import PA211.UserCandidate.CandidateTable
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.Startup
open PA215.Zip PA213.Startup PA211.UserCandidate.CandidateTable

theorem run032 : run machine 256 checkpoint032 = some checkpoint033 := by decide +kernel
theorem reach032 : Reach machine checkpoint032 checkpoint033 := ⟨256, run032⟩

theorem run033 : run machine 256 checkpoint033 = some checkpoint034 := by decide +kernel
theorem reach033 : Reach machine checkpoint033 checkpoint034 := ⟨256, run033⟩

theorem run034 : run machine 256 checkpoint034 = some checkpoint035 := by decide +kernel
theorem reach034 : Reach machine checkpoint034 checkpoint035 := ⟨256, run034⟩

theorem run035 : run machine 256 checkpoint035 = some checkpoint036 := by decide +kernel
theorem reach035 : Reach machine checkpoint035 checkpoint036 := ⟨256, run035⟩

theorem run036 : run machine 256 checkpoint036 = some checkpoint037 := by decide +kernel
theorem reach036 : Reach machine checkpoint036 checkpoint037 := ⟨256, run036⟩

theorem run037 : run machine 256 checkpoint037 = some checkpoint038 := by decide +kernel
theorem reach037 : Reach machine checkpoint037 checkpoint038 := ⟨256, run037⟩

theorem run038 : run machine 256 checkpoint038 = some checkpoint039 := by decide +kernel
theorem reach038 : Reach machine checkpoint038 checkpoint039 := ⟨256, run038⟩

theorem run039 : run machine 256 checkpoint039 = some checkpoint040 := by decide +kernel
theorem reach039 : Reach machine checkpoint039 checkpoint040 := ⟨256, run039⟩

theorem run040 : run machine 256 checkpoint040 = some checkpoint041 := by decide +kernel
theorem reach040 : Reach machine checkpoint040 checkpoint041 := ⟨256, run040⟩

theorem run041 : run machine 256 checkpoint041 = some checkpoint042 := by decide +kernel
theorem reach041 : Reach machine checkpoint041 checkpoint042 := ⟨256, run041⟩

theorem run042 : run machine 256 checkpoint042 = some checkpoint043 := by decide +kernel
theorem reach042 : Reach machine checkpoint042 checkpoint043 := ⟨256, run042⟩

theorem run043 : run machine 256 checkpoint043 = some checkpoint044 := by decide +kernel
theorem reach043 : Reach machine checkpoint043 checkpoint044 := ⟨256, run043⟩

theorem run044 : run machine 256 checkpoint044 = some checkpoint045 := by decide +kernel
theorem reach044 : Reach machine checkpoint044 checkpoint045 := ⟨256, run044⟩

theorem run045 : run machine 256 checkpoint045 = some checkpoint046 := by decide +kernel
theorem reach045 : Reach machine checkpoint045 checkpoint046 := ⟨256, run045⟩

theorem run046 : run machine 256 checkpoint046 = some checkpoint047 := by decide +kernel
theorem reach046 : Reach machine checkpoint046 checkpoint047 := ⟨256, run046⟩

theorem run047 : run machine 256 checkpoint047 = some checkpoint048 := by decide +kernel
theorem reach047 : Reach machine checkpoint047 checkpoint048 := ⟨256, run047⟩

end PA211.UserCandidate.Startup
