module
public import ConcreteOmegaMultiplication
public import RelationalInterpretationAPI
@[expose] public section
namespace ZF207.OmegaInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
def arithmeticFuncGraph {k} : Language.ORing.Func k → SetTheorySemisentence (k+1)
 | .zero => zeroGraph
 | .one => “z. ∃ e, !zeroGraph e ∧ !succGraph z e”
 | .add => “z a n. !addGraph z n a”
 | .mul => “z a n. !mulGraph z n a”
def arithmeticRelGraph {k} : Language.ORing.Rel k → SetTheorySemisentence k
 | .eq => “x y. x = y”
 | .lt => “x y. x ∈ y”
/-- Genuine relational translation, with all domain/function obligations proved.
No assertion yet that its induced structure satisfies PA. -/
def arithmeticTranslation : DirectTranslation (𝗭𝗙 : SetTheory) ℒₒᵣ where
 domain := ⟨domain⟩
 rel r := ⟨arithmeticRelGraph r⟩
 func f := ⟨arithmeticFuncGraph f⟩
 domain_nonempty := by
  apply SetTheory.complete.{0}
  intro V _ _ _
  simpa [Semiformula.Operator.val, models_iff] using (show ∃ x : V, x ∈ (ω : V) from ⟨∅,empty_mem_ω⟩)
 preserve_eq := by
  apply SetTheory.complete.{0}
  intro V _ _ _
  simp [Semiformula.Operator.val, models_iff,arithmeticRelGraph]
 func_defined f := by
  cases f
  all_goals
   apply SetTheory.complete.{0}
   intro V _ _ _
  · simpa [Semiformula.Operator.val, models_iff,arithmeticFuncGraph] using (show ∃! x : V, x ∈ (ω : V) ∧ x = ∅ from ⟨∅,⟨empty_mem_ω,rfl⟩,fun _ h => h.2⟩)
  · simp [Semiformula.Operator.val, models_iff,arithmeticFuncGraph]
    exact ⟨succ (∅ : V), ⟨ω_succ_closed empty_mem_ω,rfl⟩, fun _ h => h.2⟩
  · simp [Semiformula.Operator.val, models_iff,arithmeticFuncGraph,add_graph_defined.iff]
    intro v ha hn
    exact ⟨add (v 0) (v 1),⟨add_mem_omega _ _ ha hn,rfl⟩,fun _ h => h.2⟩
  · simp [Semiformula.Operator.val, models_iff,arithmeticFuncGraph,mul_graph_defined.iff]
    intro v ha hn
    exact ⟨mul (v 0) (v 1),⟨mul_mem_omega _ _ ha hn,rfl⟩,fun _ h => h.2⟩
end ZF207.OmegaInterpretation
