module
public import I0451.Omega.ConcreteOmegaAddition
@[expose] public section
namespace ZF207.OmegaInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
def mulBlueprint : NaturalNumberRec.Blueprint 1 where
 zero := “z a. !isEmpty z”
 succ := “z prev i a. !addGraph z a prev”
attribute [local irreducible] addGraph add
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
noncomputable def mulConstruction : NaturalNumberRec.Construction V mulBlueprint where
 zero := fun _ => ∅
 succ := fun v _ prev => add prev (v 0)
 zero_defined := ⟨fun v => by simpa [mulBlueprint] using (zero_eval (V := V) ![v 0])⟩
 succ_defined := ⟨fun v => by
  simpa [mulBlueprint] using (add_graph_defined (V := V)).eval_iff ![v 0,v 3,v 1]⟩
noncomputable def mul (a n : V) : V := mulConstruction.result ![a] n
@[simp] theorem mul_zero (a : V) : mul a 0 = ∅ := mulConstruction.result_zero ![a]
theorem mul_succ (a n : V) (hn : n ∈ (ω : V)) :
 mul a (succ n) = add (mul a n) a := mulConstruction.result_succ ![a] hn
def mulGraph : SetTheorySemisentence 3 := mulBlueprint.resultDef
theorem mul_graph_defined : DefinedFunction (fun v : Fin 2 → V => mul (v 1) (v 0)) mulGraph := by
 have he : (fun v : Fin 2 → V => mul (v 1) (v 0)) =
   (fun v => mulConstruction.result (fun x => v x.succ) (v 0)) := by
  funext v
  unfold mul
  congr 1
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl
 rw [he]
 exact mulConstruction.result_defined
instance mul_definable : ℒₛₑₜ-function₂[V] mul := by
 apply DefinedFunction.to_definable (φ := (“z a n. !mulGraph z n a” : SetTheorySemisentence 3))
 exact ⟨fun v => by simpa using (mul_graph_defined (V := V)).eval_iff ![v 0,v 2,v 1]⟩
theorem mul_mem_omega (a n : V) (ha : a ∈ (ω : V)) (hn : n ∈ (ω : V)) :
 mul a n ∈ (ω : V) := by
 apply naturalNumber_induction (fun n => mul a n ∈ (ω : V)) ?_ ?_ ?_ n hn
 · definability
 · simp
 · intro k hk ih
   rw [mul_succ a k hk]
   exact add_mem_omega _ _ ih ha
end ZF207.OmegaInterpretation
