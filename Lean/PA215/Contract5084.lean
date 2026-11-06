import PA215.Census.C039

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PA215.Contract5084
open PA215.Contracts PA215.Runtime PA215.NativeTable PA215.Census

/-- The literal original5084 record, not a replacement target. -/
def original : RawOriginal := C039.records[92]'(by decide)

theorem original_id : original.index = 5084 := by decide

def contract : Contract := original.toContract.get (by decide)

theorem original_binding : original.toContract = some contract := by rfl

theorem branch_none : contract.branch = none := by decide

/-- Kernel-checked runtime certificate for contract 5084. -/
theorem checked : check 4000 contract = true := by decide

/-- Complete indexed original5084 frame theorem, not just a local return lemma. -/
theorem uniform (n : Nat) (vs : List Nat) (hl : 10 ≤ vs.length) :
    PA215.Zip.Reach1 machine (conc n vs contract.initial) (conc n vs contract.target) := by
  apply sound 4000 contract checked n vs
  rw [branch_none]
  exact ⟨hl, trivial⟩

end PA215.Contract5084
