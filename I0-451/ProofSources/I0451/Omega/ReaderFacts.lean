module
public import I0451.Omega.CodedTranslation

/-! The template facts used by the internal arithmetic proof
translation are ordinary theorems of ZF. -/
@[expose] public section
namespace I0451.Omega

open FFL FFL.Entailment FFL.FirstOrder FFL.FirstOrder.SetTheory
open ZF207.Internal.Arith

private theorem reader_graphs {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
    (Defined (fun v : Fin 3 → V => projectOmega (v 1) = projectOmega (v 2)) omegaReader.eq) ∧
    (Defined (fun v : Fin 2 → V => projectOmega (v 1) = 0) omegaReader.zero) ∧
    (Defined (fun v : Fin 2 → V => projectOmega (v 1) = 1) omegaReader.one) ∧
    (Defined (fun v : Fin 4 → V => projectOmega (v 3) = projectOmega (v 1) + projectOmega (v 2)) omegaReader.add) ∧
    (Defined (fun v : Fin 4 → V => projectOmega (v 3) = projectOmega (v 1) * projectOmega (v 2)) omegaReader.mul) := by
  refine ⟨.mk ?_, .mk ?_, .mk ?_, .mk ?_, .mk ?_⟩
  · intro v; rw [Matrix.fun_eq_vec_three v]; exact (omegaReader_reads (v 0)).eq _ _
  · intro v; rw [Matrix.fun_eq_vec_two v]; exact (omegaReader_reads (v 0)).zero _
  · intro v; rw [Matrix.fun_eq_vec_two v]; exact (omegaReader_reads (v 0)).one _
  · intro v
    have eq : v = ![v 0,v 1,v 2,v 3] := by
      funext i; have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl <;> rfl
    rw [eq]; exact ((omegaReader_reads (v 0)).add _ _ _).trans eq_comm
  · intro v
    have eq : v = ![v 0,v 1,v 2,v 3] := by
      funext i; have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl <;> rfl
    rw [eq]; exact ((omegaReader_reads (v 0)).mul _ _ _).trans eq_comm

/-- Every implication built from these templates follows from their
operation graphs and the surjectivity of the omega interpretation. -/
theorem omegaReader_facts (T : SetTheory) [𝗭𝗙 ⪯ T] : InterpFacts omegaReader T := by
  constructor
  all_goals
    apply Entailment.WeakerThan.pbl (𝓢 := (𝗭𝗙 : SetTheory))
    apply SetTheory.complete.{0}
    intro V _ _ _
  · simp [models_iff, omegaReader]
  all_goals
    obtain ⟨eq, zero, one, add, mul⟩ := reader_graphs (V := V)
    simp [models_iff, eq.iff, zero.iff, one.iff, add.iff, mul.iff]
  all_goals
    first
    | exact (projectOmega_surjective (V := V)) _
    | exact fun a b => projectOmega_surjective _
    | intro a b c d e; simp_all
    | intro a b c d; simp_all
    | intro a b c; simp_all

end I0451.Omega
