module
public import I3_334Support.Calibration.GraphValuations
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Functions
@[expose] public section

namespace PalomarI3380.Calibration.CodedGraph

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem variableValue_bshift {t : M} (typed : IsUTerm GraphLanguage t) (b f x fallback : M) :
    variableValue (termBShift GraphLanguage t) ⟪x ∷ b,f⟫ fallback =
      variableValue t ⟪b,f⟫ fallback := by
  rcases IsUTerm.case_iff.mp typed with ⟨n,rfl⟩ | ⟨n,rfl⟩ | ⟨_,_,_,invalid,_,_⟩
  · simp [lookup_succ]
  · simp
  · exact (graphLanguage_no_function invalid).elim

theorem Values.qVec {w n m b f a fallback : M} (typed : IsSemitermVec GraphLanguage n m w)
    (reads : Values a w ⟪b,f⟫ fallback) (x : M) :
    Values (x ∷ a) (qVec GraphLanguage w) ⟪x ∷ b,f⟫ fallback := by
  have valLength : len a=n := reads.1.trans typed.lh
  refine ⟨by simp [valLength,len_qVec typed.isUTerm],?_⟩
  intro i fits
  rcases zero_or_succ i with rfl | ⟨i,rfl⟩
  · simp [Bootstrapping.qVec,lookup_zero]
  · have before : i < n := by simpa only [len_qVec typed.isUTerm,add_lt_add_iff_right] using fits
    have entry := reads.2 i (typed.lh.symm ▸ before)
    have code : (Bootstrapping.qVec GraphLanguage w).[i+1] = termBShift GraphLanguage w.[i] := by
      unfold Bootstrapping.qVec
      rw [nth_adjoin_succ,typed.lh,nth_termBShiftVec typed.isUTerm before]
    rw [nth_adjoin_succ,code,variableValue_bshift (typed.isUTerm.nth before)]
    exact entry

theorem variableValue_subst {t w n b f a fallback : M} (term : IsSemiterm GraphLanguage n t)
    (size : len w=n) (values : Values a w ⟪b,f⟫ fallback) :
    variableValue (termSubst GraphLanguage w t) ⟪b,f⟫ fallback =
      variableValue t ⟪a,f⟫ fallback := by
  rcases graph_term_cases.mp term with ⟨i,inside,rfl⟩ | ⟨i,rfl⟩
  · have original : i < len w := size.symm ▸ inside
    have fit : i < len a := values.1.symm ▸ original
    simp only [termSubst_bvar,variableValue_bound,lookup,fit,↓reduceIte]
    exact (values.2 i original).symm
  · simp

theorem Values.substitute {k n ts w b f a fallback vals : M}
    (terms : IsSemitermVec GraphLanguage k n ts)
    (size : len w=n) (assigned : Values a w ⟪b,f⟫ fallback) :
    Values vals (termSubstVec GraphLanguage k w ts) ⟪b,f⟫ fallback ↔
      Values vals ts ⟪a,f⟫ fallback := by
  unfold Values
  rw [len_termSubstVec terms.isUTerm,terms.lh]
  refine and_congr_right (fun _ => forall_congr' fun i => imp_congr_right fun inside => ?_)
  rw [nth_termSubstVec terms.isUTerm inside,variableValue_subst (terms.nth inside) size assigned]

noncomputable def substGuard : 𝚺ᴬ₁.Semisentence 5 :=
  .mkSigma “p q original modified fallback. ∃ n m w a b f,
    !((isSemiformula GraphLanguage).sigma) n p ∧ !((isSemitermVec GraphLanguage).sigma) n m w ∧
    !(substsGraph GraphLanguage) q w p ∧ !pairDef original a f ∧ !pairDef modified b f ∧
    !valuesDef a w modified fallback”

theorem substGuard_eval (p q original modified fallback : M) :
    substGuard.val.Evalb ![p,q,original,modified,fallback] ↔
      ∃ n m w a b f, IsSemiformula GraphLanguage n p ∧ IsSemitermVec GraphLanguage n m w ∧
        q=subst GraphLanguage w p ∧ original=⟪a,f⟫ ∧ modified=⟪b,f⟫ ∧ Values a w modified fallback := by
  have code (n : M) :
      (isSemiformula GraphLanguage).sigma.val.Evalb ![n,p] ↔ IsSemiformula GraphLanguage n p := by
    rw [Bounding.HierarchySymbol.Semiformula.val_sigma]
    exact IsSemiformula.defined.iff
  have substitutions (n m w : M) :
      (isSemitermVec GraphLanguage).sigma.val.Evalb ![n,m,w] ↔ IsSemitermVec GraphLanguage n m w := by
    rw [Bounding.HierarchySymbol.Semiformula.val_sigma]
    exact IsSemitermVec.defined.iff
  have mapped (w : M) :
      (substsGraph GraphLanguage).val.Evalb ![q,w,p] ↔ q=subst GraphLanguage w p := subst.defined.iff
  simp [substGuard,code,substitutions,mapped,pair_defined.iff,values_eval]

end PalomarI3380.Calibration.CodedGraph
