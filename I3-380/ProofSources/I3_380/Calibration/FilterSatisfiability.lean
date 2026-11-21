module
public import I3_380.Calibration.FilterTheory
public import I3_380.RelationAlgebra.Representation
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder Manifest RelationLaws

theorem structureOf_model {A : Type} [Nonempty A] (M : Algebra A) (hM : M.Models preceding)
    (F : SubidentityUltrafilter M)
    (hit : F.member (support M (M.inf (M.constant .D) (M.neg (M.constant .J)))) ∨
      F.member (support M (M.inf (M.constant .J) (M.neg (M.constant .D))))) :
    letI := structureOf M F.member
    A↓[FilterLanguage] ⊧* filterTheory := by
  letI := structureOf M F.member
  letI : Tarski.Structure.Eq FilterLanguage A := ⟨fun _ _ => Iff.rfl⟩
  have underlying : algebraOf A = M := algebra_structureOf M F.member
  have predicate : F.member = chosenOf A := rfl
  apply models_theory_iff.mpr
  intro p belongs
  rcases belongs with logic | basis
  · exact (models_theory_iff.mp (inferInstance : A↓[FilterLanguage] ⊧* 𝗘𝗤 FilterLanguage) p logic)
  · rcases List.mem_cons.mp basis with rfl | equation
    · apply filterSentence_eval.mpr
      rw [underlying]
      exact ⟨F,predicate,hit⟩
    · obtain ⟨e,he,rfl⟩ := List.mem_map.mp equation
      apply (equationSentence_eval e).mpr
      exact underlying.symm ▸ hM e he

theorem filter_satisfiable_of_underivability (h : ¬Derives final (.const .D) (.const .J)) :
    Semantics.Satisfiable (Tarski.Struc.{0,0} FilterLanguage) filterTheory := by
  obtain ⟨M,laws,different⟩ := separating_term_algebra h
  obtain ⟨enumerate,surjective⟩ := termClasses_countable final
  obtain ⟨F,hit⟩ := (RelationLaws.of_model M laws).filter_of_distinction enumerate surjective different
  letI : Nonempty (Derives.Classes final) := ⟨M.constant .D⟩
  refine ⟨⟨_,inferInstance,structureOf M F.member⟩,?_⟩
  exact structureOf_model M laws F hit

end PalomarI3380.Calibration
