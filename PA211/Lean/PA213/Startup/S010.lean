import PA213.StartupData
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA213.Startup
open PA215.Zip PA213.CandidateTable

theorem run160 : run machine 256 checkpoint160 = some checkpoint161 := by decide +kernel
theorem reach160 : Reach machine checkpoint160 checkpoint161 := ⟨256, run160⟩

theorem run161 : run machine 256 checkpoint161 = some checkpoint162 := by decide +kernel
theorem reach161 : Reach machine checkpoint161 checkpoint162 := ⟨256, run161⟩

theorem run162 : run machine 256 checkpoint162 = some checkpoint163 := by decide +kernel
theorem reach162 : Reach machine checkpoint162 checkpoint163 := ⟨256, run162⟩

theorem run163 : run machine 256 checkpoint163 = some checkpoint164 := by decide +kernel
theorem reach163 : Reach machine checkpoint163 checkpoint164 := ⟨256, run163⟩

theorem run164 : run machine 256 checkpoint164 = some checkpoint165 := by decide +kernel
theorem reach164 : Reach machine checkpoint164 checkpoint165 := ⟨256, run164⟩

theorem run165 : run machine 256 checkpoint165 = some checkpoint166 := by decide +kernel
theorem reach165 : Reach machine checkpoint165 checkpoint166 := ⟨256, run165⟩

theorem run166 : run machine 256 checkpoint166 = some checkpoint167 := by decide +kernel
theorem reach166 : Reach machine checkpoint166 checkpoint167 := ⟨256, run166⟩

theorem run167 : run machine 256 checkpoint167 = some checkpoint168 := by decide +kernel
theorem reach167 : Reach machine checkpoint167 checkpoint168 := ⟨256, run167⟩

theorem run168 : run machine 256 checkpoint168 = some checkpoint169 := by decide +kernel
theorem reach168 : Reach machine checkpoint168 checkpoint169 := ⟨256, run168⟩

theorem run169 : run machine 256 checkpoint169 = some checkpoint170 := by decide +kernel
theorem reach169 : Reach machine checkpoint169 checkpoint170 := ⟨256, run169⟩

theorem run170 : run machine 256 checkpoint170 = some checkpoint171 := by decide +kernel
theorem reach170 : Reach machine checkpoint170 checkpoint171 := ⟨256, run170⟩

theorem run171 : run machine 256 checkpoint171 = some checkpoint172 := by decide +kernel
theorem reach171 : Reach machine checkpoint171 checkpoint172 := ⟨256, run171⟩

theorem run172 : run machine 256 checkpoint172 = some checkpoint173 := by decide +kernel
theorem reach172 : Reach machine checkpoint172 checkpoint173 := ⟨256, run172⟩

theorem run173 : run machine 256 checkpoint173 = some checkpoint174 := by decide +kernel
theorem reach173 : Reach machine checkpoint173 checkpoint174 := ⟨256, run173⟩

theorem run174 : run machine 256 checkpoint174 = some checkpoint175 := by decide +kernel
theorem reach174 : Reach machine checkpoint174 checkpoint175 := ⟨256, run174⟩

theorem run175 : run machine 256 checkpoint175 = some checkpoint176 := by decide +kernel
theorem reach175 : Reach machine checkpoint175 checkpoint176 := ⟨256, run175⟩

end PA213.Startup
