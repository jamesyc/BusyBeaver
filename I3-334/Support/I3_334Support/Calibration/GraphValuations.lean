module
public import I3_334Support.Calibration.VariableTerms
public import I3_334Support.Arithmetic.FiniteTraces
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Basic
@[expose] public section

namespace PalomarI3380.Calibration.CodedGraph

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Valuations use two internally finite vectors, one for bound
variables and one for free variables. Missing coordinates use a fixed
point of the model, including when the missing index is nonstandard. -/
noncomputable def lookup (entries index fallback : M) : M :=
  if index < len entries then entries.[index] else fallback

noncomputable def lookupDef : 𝚺ᴬ₁.Semisentence 4 :=
  .mkSigma “out entries index fallback. ∃ length, !lenDef length entries ∧
    ((index<length ∧ !nthDef out entries index) ∨ (length≤index ∧ out=fallback))”

theorem lookup_eval (out entries index fallback : M) :
    lookupDef.val.Evalb ![out,entries,index,fallback] ↔ out=lookup entries index fallback := by
  by_cases valid : index < len entries <;>
    simp [lookupDef,lookup,len_defined.iff,nth_defined.iff,valid,not_le_of_gt,le_of_not_gt]

theorem lookup_zero (x entries fallback : M) : lookup (x ∷ entries) 0 fallback=x := by
  simp [lookup,len_adjoin,lt_add_one]

theorem lookup_succ (x entries index fallback : M) :
    lookup (x ∷ entries) (index+1) fallback = lookup entries index fallback := by
  rw [lookup,lookup,len_adjoin]
  by_cases h : index < len entries
  · have h' : index+1 < len entries+1 := add_lt_add_left h 1
    simp [h,h',nth_adjoin_succ]
  · have h' : ¬index+1 < len entries+1 := fun smaller => h ((add_lt_add_iff_right 1).mp smaller)
    simp [h,h']

noncomputable def variableValue (term assignment fallback : M) : M :=
  let index := π₂ (term-1)
  let v := if π₁ (term-1)=0 then π₁ assignment else π₂ assignment
  lookup v index fallback

noncomputable def variableValueDef : 𝚺ᴬ₁.Semisentence 4 :=
  .mkSigma “out term assignment fallback. ∃ raw kind index bind free entries,
    !subDef raw term 1 ∧ !pairDef raw kind index ∧ !pairDef assignment bind free ∧
    ((kind=0 ∧ entries=bind) ∨ (kind≠0 ∧ entries=free)) ∧ !lookupDef out entries index fallback”

theorem variableValue_eval (out term assignment fallback : M) :
    variableValueDef.val.Evalb ![out,term,assignment,fallback] ↔ out=variableValue term assignment fallback := by
  have split (code l r : M) : code=⟪l,r⟫ ↔ l=π₁ code ∧ r=π₂ code := by
    constructor
    · rintro rfl; simp
    · rintro ⟨rfl,rfl⟩; exact (pair_unpair _).symm
  by_cases bound : π₁ (term-1)=0 <;>
    simp [variableValueDef,variableValue,sub_defined.iff,pair_defined.iff,split,lookup_eval,bound]

@[simp] theorem variableValue_bound (i b f default : M) :
    variableValue (^#i) ⟪b,f⟫ default = lookup b i default := by
  simp [variableValue,qqBvar,Arithmetic.add_sub_self]

@[simp] theorem variableValue_free (i b f default : M) :
    variableValue (^&i) ⟪b,f⟫ default = lookup f i default := by
  simp [variableValue,qqFvar,Arithmetic.add_sub_self]

noncomputable def valuesDef : 𝚺ᴬ₁.Semisentence 4 :=
  .mkSigma “values terms env fallback. ∃ length,
    !lenDef length terms ∧ !lenDef length values ∧
    ∀ i < length, ∃ t x, !nthDef t terms i ∧ !nthDef x values i ∧ !variableValueDef x t env fallback”

def Values (values terms env fallback : M) : Prop :=
  len values = len terms ∧ ∀ i < len terms, values.[i] = variableValue terms.[i] env fallback

theorem values_eval (values terms env fallback : M) :
    valuesDef.val.Evalb ![values,terms,env,fallback] ↔ Values values terms env fallback := by
  simp [valuesDef,Values,len_defined.iff,nth_defined.iff,variableValue_eval,eq_comm]

theorem variableValue_definable : 𝚺ᴬ₁-Function₃ (variableValue (M := M)) :=
  (show 𝚺ᴬ₁-Function₃ (variableValue (M := M)) via variableValueDef from
    .mk fun v => by
      have vec : ![v 0,v 1,v 2,v 3] = v := by
        funext i
        refine Fin.cases rfl (fun i => ?_) i
        refine Fin.cases rfl (fun i => ?_) i
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun i => i.elim0) i
      have meaning := variableValue_eval (v 0) (v 1) (v 2) (v 3)
      exact vec ▸ meaning).to_definable

theorem values_exist (terms env fallback : M) : ∃! values, Values values terms env fallback := by
  have eval := variableValue_definable (M := M)
  obtain ⟨v,length,entries⟩ := PalomarI3380.Arithmetic.tabulateVector
    (fun i => variableValue terms.[i] env fallback) (by definability) (len terms)
  refine ⟨v,⟨length,entries⟩,fun w hw => ?_⟩
  exact nth_ext' _ hw.1 length (fun i hi => (hw.2 i hi).trans (entries i hi).symm)

@[simp] theorem values_matrix {arity : Nat} (terms : Fin arity → M) (env fallback : M) :
    Values (matrixToVec fun i => variableValue (terms i) env fallback) (matrixToVec terms) env fallback := by
  refine ⟨by simp,?_⟩
  intro i fits
  rw [matrixToVec_len] at fits
  have castBelow : ∃ j : Fin arity, (j.val : M)=i := by
    induction arity with
    | zero => simp at fits
    | succ arity ih =>
      rw [Nat.cast_succ] at fits
      rcases lt_or_eq_of_le (lt_succ_iff_le.mp fits) with lt | eq
      · obtain ⟨j,his⟩ := ih (Fin.init terms) lt
        exact ⟨j.castSucc,his⟩
      · exact ⟨Fin.last arity,eq.symm⟩
  obtain ⟨j,rfl⟩ := castBelow
  simp only [matrixToVec_nth]

end PalomarI3380.Calibration.CodedGraph
