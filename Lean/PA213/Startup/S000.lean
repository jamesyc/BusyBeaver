module

public import PA213.StartupData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA213.Startup
open PA215.Zip PA213.CandidateTable

theorem run000 : run machine 256 checkpoint000 = some checkpoint001 := by decide +kernel
theorem reach000 : Reach machine checkpoint000 checkpoint001 := ⟨256, run000⟩

theorem run001 : run machine 256 checkpoint001 = some checkpoint002 := by decide +kernel
theorem reach001 : Reach machine checkpoint001 checkpoint002 := ⟨256, run001⟩

theorem run002 : run machine 256 checkpoint002 = some checkpoint003 := by decide +kernel
theorem reach002 : Reach machine checkpoint002 checkpoint003 := ⟨256, run002⟩

theorem run003 : run machine 256 checkpoint003 = some checkpoint004 := by decide +kernel
theorem reach003 : Reach machine checkpoint003 checkpoint004 := ⟨256, run003⟩

theorem run004 : run machine 256 checkpoint004 = some checkpoint005 := by decide +kernel
theorem reach004 : Reach machine checkpoint004 checkpoint005 := ⟨256, run004⟩

theorem run005 : run machine 256 checkpoint005 = some checkpoint006 := by decide +kernel
theorem reach005 : Reach machine checkpoint005 checkpoint006 := ⟨256, run005⟩

theorem run006 : run machine 256 checkpoint006 = some checkpoint007 := by decide +kernel
theorem reach006 : Reach machine checkpoint006 checkpoint007 := ⟨256, run006⟩

theorem run007 : run machine 256 checkpoint007 = some checkpoint008 := by decide +kernel
theorem reach007 : Reach machine checkpoint007 checkpoint008 := ⟨256, run007⟩

theorem run008 : run machine 256 checkpoint008 = some checkpoint009 := by decide +kernel
theorem reach008 : Reach machine checkpoint008 checkpoint009 := ⟨256, run008⟩

theorem run009 : run machine 256 checkpoint009 = some checkpoint010 := by decide +kernel
theorem reach009 : Reach machine checkpoint009 checkpoint010 := ⟨256, run009⟩

theorem run010 : run machine 256 checkpoint010 = some checkpoint011 := by decide +kernel
theorem reach010 : Reach machine checkpoint010 checkpoint011 := ⟨256, run010⟩

theorem run011 : run machine 256 checkpoint011 = some checkpoint012 := by decide +kernel
theorem reach011 : Reach machine checkpoint011 checkpoint012 := ⟨256, run011⟩

theorem run012 : run machine 256 checkpoint012 = some checkpoint013 := by decide +kernel
theorem reach012 : Reach machine checkpoint012 checkpoint013 := ⟨256, run012⟩

theorem run013 : run machine 256 checkpoint013 = some checkpoint014 := by decide +kernel
theorem reach013 : Reach machine checkpoint013 checkpoint014 := ⟨256, run013⟩

theorem run014 : run machine 256 checkpoint014 = some checkpoint015 := by decide +kernel
theorem reach014 : Reach machine checkpoint014 checkpoint015 := ⟨256, run014⟩

theorem run015 : run machine 256 checkpoint015 = some checkpoint016 := by decide +kernel
theorem reach015 : Reach machine checkpoint015 checkpoint016 := ⟨256, run015⟩

end PA213.Startup
