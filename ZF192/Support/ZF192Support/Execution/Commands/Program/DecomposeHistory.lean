module
public import ZF192Support.Execution.Commands.Program.SpliceHistory
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelOperationalConcat
open ZFR.ArithmeticRepresentation ZF192Support.ModelCommands
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def decomposeFormula (hist:ArithmeticSemiformula Nat 1) (app:𝚺ᴬ₁.Semisentence 3) :
 ArithmeticSemiformula Nat 1 :=
 “n. !hist n → ∃p, ∃one, !listConsGraph one &0 0 ∧ !app n p one”
lemma decomposeFormula_eval (initial:M) (n:M) :
 (decomposeFormula (rootedRunFormula 0) appendGraph).Eval ![n] (fun _=>initial) ↔
 (runHistory initial n → ∃p,n=append p (modelListCons initial 0)) := by
 simp [decomposeFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',
 Matrix.empty_eq,Empty.eq_elim,Matrix.constant_eq_singleton,rootedRunFormula_eval,ruleCons_defined.iff,append_defined.iff]
lemma runHistory_decompose (initial n:M) (h:runHistory initial n) :
 ∃p,n=append p (modelListCons initial 0) := by
 have all : ∀z:M,runHistory initial z → ∃p,z=append p (modelListCons initial 0) := by
  apply model_list_induction (decomposeFormula (rootedRunFormula 0) appendGraph)
   (fun _=>initial) (fun z=>runHistory initial z→∃p,z=append p (modelListCons initial 0))
   (decomposeFormula_eval initial)
  · intro hz; exact False.elim (hz.1 rfl)
  · intro a t ih hh
    have ht: modelTrace (runEdge initial) t := ((modelTrace_cons _ _ _).mp hh.2).1
    by_cases ht0:t=0
    · subst t
      have ha:a=initial := by
       simpa [runEdge, ZF192Support.ModelScheduler.rootedEdge] using ((modelTrace_cons _ _ _).mp hh.2).2
      subst a
      exact ⟨0,(append_zero _).symm⟩
    · obtain ⟨p,hp⟩ := ih ⟨ht0,ht⟩
      refine ⟨modelListCons a p,?_⟩
      rw [append_cons,←hp]
 exact all n h
/-- Compose two arbitrary internally coded runs sharing their boundary state.
No externally finite list or pre-supplied decomposition is needed. -/
lemma command_history_concat (initial mid later earlier:M)
 (hl:runHistory mid later) (he:runHistory initial earlier)
 (hboundary:modelListHead earlier=mid) :
 ∃combined,runHistory initial combined ∧
 modelListHead combined=modelListHead later := by
 obtain ⟨p,hp⟩ := runHistory_decompose mid later hl
 refine ⟨append p earlier,?_,?_⟩
 · apply command_history_splice mid initial p mid earlier
   · simpa only [←hp] using hl
   · exact he
   · exact hboundary
 · rw [hp]
   apply append_head_eq
   simpa only [modelListHead_cons] using hboundary
end ZF192Support.ModelOperationalConcat
