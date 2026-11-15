module
public import ModelCourseOfValues
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Bounding.HierarchySymbol
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma history_result_definable {k} (step : 𝚺ᴬ₁.Semisentence (k+3))
 (hs : GraphTotalIn (M := M) step) (v : Fin k → M) :
 𝚺ᴬ₁.DefinableFunction₁ ((historyConstruction step hs).result v) := by
 let c := historyConstruction step hs
 have h := c.result_definable.substitution (f := fun i (w : Fin 1 → M) => (w 0 :> v) i) (by
   intro i
   refine Fin.cases ?_ (fun j => ?_) i
   · exact DefinableFunction.var 0
   · exact DefinableFunction.const (v j))
 simpa using h

lemma history_stable {k} (step : 𝚺ᴬ₁.Semisentence (k+3))
 (hs : GraphTotalIn (M := M) step) (v : Fin k → M) (i u w : M)
 (hi : i<u) (hu : u≤w) :
 znth ((historyConstruction step hs).result v w) i =
 znth ((historyConstruction step hs).result v u) i := by
 have hd := history_result_definable step hs v
 have h : ∀ w : M, u≤w → znth ((historyConstruction step hs).result v w) i =
   znth ((historyConstruction step hs).result v u) i := by
   intro w
   induction w using ISigma1.sigma1_succ_induction
   · definability
   case zero =>
     intro hle
     have hz : u=0 := le_antisymm hle (by simp)
     rw [hz]
   case succ w ih =>
     intro hle
     by_cases hprev : u≤w
     · rw [history_old step hs v w i (lt_of_lt_of_le hi hprev), ih hprev]
     · have he : u=w+1 := le_antisymm hle (succ_le_iff_lt.mpr (lt_of_not_ge hprev))
       rw [he]
 exact h w hu

end ZFR.ArithmeticRepresentation
