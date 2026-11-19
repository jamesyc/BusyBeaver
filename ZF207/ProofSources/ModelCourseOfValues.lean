module
public import GraphPrimitiveRecursion
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Bounding.HierarchySymbol
namespace ZFR.ArithmeticRepresentation

def historyBlueprint {k} (step : 𝚺ᴬ₁.Semisentence (k+3)) : PR.Blueprint k where
 zero := .mkSigma “#0 = 0”
 succ := .mkSigma “s h i. ∃ z, !step z h i ⋯ ∧ !seqConsDef s h z”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def historyConstruction {k} (step : 𝚺ᴬ₁.Semisentence (k+3))
 (hs : GraphTotalIn (M := M) step) : PR.Construction M (historyBlueprint step) where
 zero := fun _ => 0
 succ := fun v i h => h ⁀' graphValue step hs (h :> i :> v)
 zero_defined := .mk (by intro v; simp [historyBlueprint])
 succ_defined := .mk (by
   intro v
   simp [historyBlueprint,Semiformula.eval_rew,Empty.eq_elim,Function.comp_def,
     Matrix.comp_vecCons',seqCons_defined.iff]
   change (∃ x, step.val.Evalb (x :> v 1 :> v 2 :> fun i => v i.succ.succ.succ) ∧ _) ↔ _
   simp only [graphValue_spec step hs]
   simp)

lemma history_seq_length {k} (step : 𝚺ᴬ₁.Semisentence (k+3))
 (hs : GraphTotalIn (M := M) step) (v : Fin k → M) (u : M) :
 Seq ((historyConstruction step hs).result v u) ∧ lh ((historyConstruction step hs).result v u)=u := by
 let c := historyConstruction step hs
 induction u using ISigma1.sigma1_succ_induction
 · have hf : 𝚺ᴬ₁.DefinableFunction (fun w : Fin 1 → M => c.result v (w 0)) := by
     have h := c.result_definable.substitution (f := fun i (w : Fin 1 → M) => (w 0 :> v) i) (by
       intro i
       refine Fin.cases ?_ (fun j => ?_) i
       · exact DefinableFunction.var 0
       · exact DefinableFunction.const (v j))
     simpa using h
   change 𝚺ᴬ₁-Predicate (fun u => Seq (c.result v u) ∧ lh (c.result v u)=u)
   have hseq := Definable.comp₁ (Γ := 𝚺) (P := Seq) hf
   have hlh := DefinableFunction₁.comp (Γ := 𝚺) (F := lh) hf
   exact hseq.and (Definable.comp₂ (P := Eq) hlh (DefinableFunction.var 0))
 case zero =>
   rw [PR.Construction.result_zero]
   change Seq (0:M) ∧ lh (0:M)=0
   simpa [emptyset_def] using And.intro (seq_empty (V := M)) (lh_empty (V := M))
 case succ u ih =>
   rw [PR.Construction.result_succ]
   change Seq (c.result v u ⁀' _) ∧ lh (c.result v u ⁀' _)=u+1
   exact ⟨ih.1.seqCons _,by rw [ih.1.lh_seqCons,ih.2]⟩

lemma history_last {k} (step : 𝚺ᴬ₁.Semisentence (k+3))
 (hs : GraphTotalIn (M := M) step) (v : Fin k → M) (u : M) :
 znth ((historyConstruction step hs).result v (u+1)) u =
 graphValue step hs ((historyConstruction step hs).result v u :> u :> v) := by
 let c := historyConstruction step hs
 have ih := history_seq_length step hs v u
 rw [PR.Construction.result_succ]
 change znth (c.result v u ⁀' _) u=_
 apply (ih.1.seqCons _).znth_eq_of_mem
 simp [seqCons,ih.2]

lemma history_old {k} (step : 𝚺ᴬ₁.Semisentence (k+3))
 (hs : GraphTotalIn (M := M) step) (v : Fin k → M) (u i : M) (hi : i<u) :
 znth ((historyConstruction step hs).result v (u+1)) i =
 znth ((historyConstruction step hs).result v u) i := by
 let c := historyConstruction step hs
 have ih := history_seq_length step hs v u
 have hm := ih.1.znth (show i < lh (c.result v u) by change i < lh ((historyConstruction step hs).result v u); rw [ih.2]; exact hi)
 rw [PR.Construction.result_succ]
 change znth (c.result v u ⁀' _) i=_
 apply (ih.1.seqCons _).znth_eq_of_mem
 simp [seqCons,hm]

end ZFR.ArithmeticRepresentation
