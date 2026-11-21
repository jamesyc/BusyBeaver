module
public import I0451.ArithmeticHistories
public import I0451.ArithmeticCommandWitness

/-! Stop a coded command history at its first zero, which marks the
literal halt. The underlying sequence lemmas are independent of the machine. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem coded_command_history_exists (initial length : V) :
    ∃ book, Iteration boundaryCodeStep initial book length :=
  Iteration.exists _ boundaryCodeStep_defined _ _

theorem Iteration.command_run_of_zero {initial book length : V}
    (ran : Iteration boundaryCodeStep initial book length)
    (starts : initial ≠ 0) (stopped : znth book length = 0) :
    ∃ limit, CodedCommandRun initial book limit := by
  obtain ⟨k, within, zero, earlier⟩ := first_zero_at_most book length ⟨length, le_refl _, stopped⟩
  have positive : k ≠ 0 := by
    intro eq
    rw [eq, ran.begins] at zero
    exact starts zero
  obtain ⟨limit, hk⟩ := eq_succ_of_pos (pos_iff_ne_zero.mpr positive)
  subst k
  have lt : limit < length := succ_le_iff_lt.mp within
  have final := (ran.advances limit lt).symm.trans zero
  refine ⟨limit, ran.sequence, within.trans (by rw [ran.size]; simp), ran.begins, ?_, ?_, final⟩
  · exact fun j before => earlier j (lt_succ_iff_le.mpr before)
  · exact fun j before => (ran.advances j (lt_trans before lt)).symm

end I0451.Arithmetization
