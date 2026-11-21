module
public import I3_380.Calibration.TermWords
public import I3_380.Search.Arithmetic.TokenConsumption
@[expose] public section

namespace PalomarI3380.Calibration.TermWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ArithmeticMachine.SourceWords

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem filter_arity_is_standard {k f : M} (valid : FilterLanguage.IsFunc k f) :
    ∃ n : Nat, k = (n : M) := by
  simp [Language.IsFunc,Language.isFunc,FFL.FirstOrder.Semiformula.EvalAux,FFL.FirstOrder.Semiterm.val,standardModel,numeral_eq_natCast] at valid
  rcases valid with ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩
  · change k = (ORingStructure.numeral 0 : M) at h
    exact ⟨0,h.trans (numeral_eq_natCast_app 0)⟩
  · change k = (ORingStructure.numeral 1 : M) at h
    exact ⟨1,h.trans (numeral_eq_natCast_app 1)⟩
  · change k = (ORingStructure.numeral 2 : M) at h
    exact ⟨2,h.trans (numeral_eq_natCast_app 2)⟩
  · change k = (ORingStructure.numeral 3 : M) at h
    exact ⟨3,h.trans (numeral_eq_natCast_app 3)⟩

/-- The printer emits a valid preorder tree even for a term whose code
or number of nodes is nonstandard. This uses arithmetic induction on the
model's term codes and the finite function signature. -/
theorem termTokens_consumes [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] {root : M} (wellFormed : IsUTerm FilterLanguage root) :
    ConsumesTree (termTokens root) := by
  let P := fun t : M => IsUTerm FilterLanguage t → ConsumesTree (termTokens t)
  have cases' : 𝚺ᴬ_[2]-Predicate (IsUTerm (V := M) FilterLanguage) := by definability
  have consumption : 𝚷ᴬ_[2]-Relation₃ (Consumes (M := M)) :=
    .of_lt consumes_definable (by decide)
  have oneTree : 𝚷ᴬ_[2]-Predicate (fun t : M => ConsumesTree (termTokens t)) := by
    change 𝚷ᴬ_[2].Definable (fun v : Fin 1 → M =>
      ∀ count : M, 0 < count → Consumes (termTokens (v 0)) count (count-1))
    apply Bounding.HierarchySymbol.Definable.all
    have live : 𝚺ᴬ_[2].Definable (fun v : Fin 2 → M => 0 < v 0) := by definability
    have printed : 𝚺ᴬ₁.DefinableFunction (fun v : Fin 2 → M => termTokens (v 1)) := by definability
    have printedHigher : 𝚺ᴬ_[2].DefinableFunction (fun v : Fin 2 → M => termTokens (v 1)) :=
      .of_lt printed (by decide)
    letI : 𝚷ᴬ_[2]-Relation₃ (Consumes (M := M)) := consumption
    have scan : 𝚷ᴬ_[2].Definable (fun v : Fin 2 → M => Consumes (termTokens (v 1)) (v 0) (v 0-1)) :=
      Bounding.HierarchySymbol.Definable.comp₃ printedHigher (by definability) (by definability)
    exact Bounding.HierarchySymbol.Definable.imp live scan
  have definable : 𝚷ᴬ_[2]-Predicate P := Bounding.HierarchySymbol.Definable.imp cases' oneTree
  have all : ∀ t : M, P t := by
    apply InductionOnHierarchy.order_induction_sigma 𝚷 2 definable
    intro t previous recognized
    rcases IsUTerm.case_iff.mp recognized with ⟨k,rfl⟩ | ⟨x,rfl⟩ | ⟨k,f,args,func,argument,rfl⟩
    · rw [termTokens,termConstruction.result_bvar]
      exact ConsumesTree.leaf (1 : M)
    · rw [termTokens,termConstruction.result_fvar]
      exact ConsumesTree.leaf (1 : M)
    · obtain ⟨n,rfl⟩ := filter_arity_is_standard func
      let encoded := termConstruction.resultVec FilterLanguage ![] (n : M) args
      have width : len encoded = (n : M) := termConstruction.resultVec_lh FilterLanguage ![] argument
      have trees : ∀ i < len encoded, ConsumesTree encoded.[i] := by
        intro i hi
        rw [width] at hi
        have lt : args.[i] < ^func (n : M) f args := by
          have smaller : args.[i] < args := nth_lt_self (by rwa [← argument.lh])
          exact lt_trans smaller (terms_lt_qqFunc _ _ _)
        have tree := previous args.[i] lt (argument.nth hi)
        simpa only [encoded,termConstruction.nth_resultVec FilterLanguage ![] argument hi,termTokens] using tree
      intro count live
      have first : Consumes (?[ (⟪(n : M),f⟫ : M) ]) count (count-1+(n : M)) := by
        simpa only [Arithmetic.pi₁_pair] using Consumes.one (⟪(n : M),f⟫ : M) count live
      have rest := Consumes.forest width trees (count-1)
      have words : termTokens (^func (n : M) f args) = ⟪(n : M),f⟫ ∷ flattenTokens encoded := by
        simp [termTokens,termConstruction,func,argument,encoded]
      rw [words]
      simpa only [appendVector_cons,appendVector_nil] using first.append rest
  exact all root wellFormed

end PalomarI3380.Calibration.TermWords
