module
public import DirectDepthShift
public import DirectSubstTraversal
public import ExecutableZFAxioms
@[expose] public section
namespace RosserDirect.SchemaRename
open ZFR

theorem sep_map : sourceShiftIndex 1 ∘ sourceShiftIndex 1 = sepIndex := by
 funext i
 simp only [Function.comp_apply,sourceShiftIndex,sepIndex]
 split_ifs <;> omega

theorem repC_map : sourceShiftIndex 2 ∘ sourceShiftIndex 2 = repCIndex := by
 funext i
 simp only [Function.comp_apply,sourceShiftIndex,repCIndex]
 split_ifs <;> omega

theorem repA_map : substMap 2 ∘ sourceShiftIndex 1 ∘ sourceShiftIndex 2 = repAIndex := by
 funext i
 cases i with
 | zero => rfl
 | succ i =>
  cases i with
  | zero => rfl
  | succ i => simp [Function.comp_def,sourceShiftIndex,substMap,repAIndex,show ¬i+1+1<2 by omega,show ¬i+1+1+1<1 by omega]

theorem repB_map : substMap 0 ∘ substMap 3 ∘ sourceShiftIndex 1 ∘ sourceShiftIndex 2 ∘ sourceShiftIndex 2 = repBIndex := by
 funext i
 cases i with
 | zero => rfl
 | succ i =>
  cases i with
  | zero => rfl
  | succ i => simp [Function.comp_def,sourceShiftIndex,substMap,repBIndex,show ¬i+1+1<2 by omega,show ¬i+1+1+1<2 by omega,show ¬i+1+1+1+1<1 by omega]

theorem separation (f : Formula) :
 DepthShift.shifted 1 (DepthShift.shifted 1 f) = rename sepIndex f := by
 simpa only [DepthShift.shifted,rename_comp,sep_map]

theorem replacementC (f : Formula) :
 DepthShift.shifted 2 (DepthShift.shifted 2 f) = rename repCIndex f := by
 simpa only [DepthShift.shifted,rename_comp,repC_map]

theorem replacementA (f : Formula) :
 subst 2 (DepthShift.shifted 1 (DepthShift.shifted 2 f)) = rename repAIndex f := by
 simp only [subst,DepthShift.shifted,rename_comp,Function.comp_assoc,repA_map]

theorem replacementB (f : Formula) :
 subst 0 (subst 3 (DepthShift.shifted 1 (DepthShift.shifted 2 (DepthShift.shifted 2 f)))) = rename repBIndex f := by
 simp only [subst,DepthShift.shifted,rename_comp,Function.comp_assoc,repB_map]
end RosserDirect.SchemaRename
