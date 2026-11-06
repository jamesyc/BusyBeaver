import PA215.Source.AXHead3Plan
import PA215.Source.ActualAXCode
set_option maxRecDepth 100000
namespace PA215.Source.AXHead3

def initial : AXMacro.Store := ⟨0,0,0,0,0,[]⟩
def finalStore : AXMacro.Store := ⟨824,0,0,0,0,[]⟩
theorem macro_checked : AXMacro.run code initial = some finalStore := by decide

def start : Configuration := ⟨.at 1784,fun _ => 0⟩
def finish : Configuration := ⟨.at 2061,fun r => if r=1 then 824 else 0⟩

theorem start_eq : AXMacro.configAt 1784 initial 0 (fun _ => 0) = start := by
  apply congrArg (fun r => Configuration.mk (.at 1784) r)
  funext r
  simp [AXMacro.registers,initial,AXCode.stackCode]

theorem finish_eq : AXMacro.configAt 2061 finalStore 0 (fun _ => 0) = finish := by
  apply congrArg (fun r => Configuration.mk (.at 2061) r)
  funext r
  simp [AXMacro.registers,finalStore,AXCode.stackCode]

/-- Actual primitive-source reachability, obtained from all277 bound instructions
and verified helper semantics, not from an external execution log. -/
theorem exact_source_output : ∃ n, Steps exactSites n start finish := by
  obtain ⟨n,hn⟩ := plan.sound initial finalStore macro_checked 0 (fun _ => 0)
  exact ⟨n,by simpa only [start_eq,finish_eq] using hn⟩

theorem macro_checked_frame (l : Nat) :
    AXMacro.run code ⟨0,0,0,0,l,[]⟩ = some ⟨824,0,0,0,l,[]⟩ := by rfl

/-- The counterexample value is independent of the existing formula-stack tail
and unrelated register frame; it is not an artifact of resetting that tail. -/
theorem exact_source_frame (l bottom : Nat) (f : Registers) :
    ∃ n, Steps exactSites n
      (AXMacro.configAt 1784 ⟨0,0,0,0,l,[]⟩ bottom f)
      (AXMacro.configAt 2061 ⟨824,0,0,0,l,[]⟩ bottom f) :=
  plan.sound _ _ (macro_checked_frame l) bottom f

theorem old_spec_value : AXCode.rho3 0 0 0 = 4316 := by decide
theorem actual_spec_value : ActualAXCode.rho3 0 0 0 = 824 := by decide
/-- The third AX head produces a different value from the rho3 formula. -/
theorem spec_disagrees : finish.registers 1 ≠ AXCode.rho3 0 0 0 := by decide
#print axioms exact_source_output
#print axioms exact_source_frame
#print axioms spec_disagrees
end PA215.Source.AXHead3
