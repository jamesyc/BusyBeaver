module
public import ZF192Support.SetTheory.Omega.Domain
public import Foundation.FirstOrder.SetTheory.NaturalNumberRec
@[expose] public section
namespace ZF192Support.OmegaInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
/-- Addition by iteration of successor; output, index, parameter order. -/
def addBlueprint : NaturalNumberRec.Blueprint 1 where
 zero := “z a. z = a”
 succ := “z prev i a. !succ.dfn z prev”
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
noncomputable def addConstruction : NaturalNumberRec.Construction V addBlueprint where
 zero := fun v => v 0
 succ := fun _ _ prev => succ prev
 zero_defined := ⟨fun v => by simp [addBlueprint]⟩
 succ_defined := ⟨fun v => succ.defined.eval_iff ![v 0,v 1]⟩
noncomputable def add (a n : V) : V := addConstruction.result ![a] n
@[simp] theorem add_zero (a : V) : add a 0 = a :=
 addConstruction.result_zero ![a]
theorem add_succ (a n : V) (hn : n ∈ (ω : V)) :
 add a (succ n) = succ (add a n) := addConstruction.result_succ ![a] hn
/-- Concrete pure membership formula for the graph; no uninterpreted callback. -/
def addGraph : SetTheorySemisentence 3 := addBlueprint.resultDef
theorem add_graph_defined : DefinedFunction (fun v : Fin 2 → V => add (v 1) (v 0)) addGraph :=
 by
 have he : (fun v : Fin 2 → V => add (v 1) (v 0)) =
   (fun v => addConstruction.result (fun x => v x.succ) (v 0)) := by
  funext v
  unfold add
  congr 1
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl
 rw [he]
 exact addConstruction.result_defined
instance add_definable : ℒₛₑₜ-function₂[V] add := by
 apply DefinedFunction.to_definable (φ := (“z a n. !addGraph z n a” : SetTheorySemisentence 3))
 exact ⟨fun v => by simpa using (add_graph_defined (V := V)).eval_iff ![v 0,v 2,v 1]⟩
theorem add_mem_omega (a n : V) (ha : a ∈ (ω : V)) (hn : n ∈ (ω : V)) :
 add a n ∈ (ω : V) := by
 apply naturalNumber_induction (fun n => add a n ∈ (ω : V)) ?_ ?_ ?_ n hn
 · definability
 · simpa using ha
 · intro k hk ih
   rw [add_succ a k hk]
   exact ω_succ_closed ih
end ZF192Support.OmegaInterpretation
