import PA215.OriginalHaltCertified
import PA215.OriginalSelectors
import PA215.Contract5114
set_option maxRecDepth 100000
namespace PA215.IndexedContracts
open PA215.Census
attribute [local irreducible] originalAt

def terminal5114 : OriginalHaltCertified ⟨5114, by decide⟩ := by
  have h : originalAt ⟨5114, by decide⟩ = C039.records[122]'(by decide) :=
    originalAt_C039 ⟨122, by decide⟩
  refine ⟨?_, ?_, 4000, ?_⟩
  · rw [h]; rfl
  · rw [h]; rfl
  · rw [h]; exact PA215.Contract5114.checked

end PA215.IndexedContracts
