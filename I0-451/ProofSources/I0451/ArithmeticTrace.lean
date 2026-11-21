module
public import I0451.Arithmetization
public import Foundation.FirstOrder.Arithmetic.Induction.Basic

/-! Internal composition of tape traces. The configuration parameter and
both lengths belong to the arithmetic model. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def traceBlueprint (table : Nat) : PR.Blueprint 1 where
  zero := .mkSigma “result start. result = start”
  succ := .mkSigma “result prior time start. !(tickDef table) result prior”

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def traceConstruction (table : Nat) : PR.Construction V (traceBlueprint table) where
  zero := fun v => v 0
  succ := fun _ _ prev => modelTick table prev
  zero_defined := .mk fun v => by simp [traceBlueprint]
  succ_defined := .mk fun v => by simpa [traceBlueprint] using tickDef_eval table (v 0) (v 1)

noncomputable def trace (table : Nat) (n start : V) : V :=
  (traceConstruction table).result ![start] n

theorem trace_eval (table : Nat) (endState n start : V) :
    (traceBlueprint table).resultDef.val.Evalb ![endState,n,start] ↔ endState = trace table n start := by
  simp only [(traceConstruction table).result_defined_iff, Matrix.cons_val_zero,
    Matrix.cons_val_succ, trace]
  rfl

@[simp] theorem trace_zero (table : Nat) (start : V) : trace table (0 : V) start = start := by
  change (traceConstruction table).result ![start] 0 = start
  rw [PR.Construction.result_zero]
  rfl

@[simp] theorem trace_succ (table : Nat) (n start : V) :
    trace table (n + 1) start = modelTick table (trace table n start) := by
  simp [trace, traceConstruction]

theorem trace_defined (table : Nat) : 𝚺ᴬ₁-Function₂[V] (trace table) via (traceBlueprint table).resultDef := by
  refine .mk fun v => ?_
  rw [Matrix.fun_eq_vec_three v]
  exact trace_eval table _ _ _

@[definability] instance trace_definable (table : Nat) : 𝚺ᴬ₁-Function₂[V] (trace table) :=
  (trace_defined table).to_definable

theorem trace_add (table : Nat) (start m n : V) :
    trace table (m + n) start = trace table n (trace table m start) := by
  induction n using ISigma1.sigma1_succ_induction with
  | zero => simp
  | succ n ih => rw [← add_assoc, trace_succ, trace_succ, ih]
  | hP => definability

theorem blankTime_defined (table : Nat) :
    𝚺ᴬ₁-Function₁[V] (atTime table) via (machineBlueprint table).resultDef := by
  refine .mk fun v => ?_
  have args : (fun i : Fin 0 => v i.succ.succ) = (![] : Fin 0 → V) := by
    funext i
    exact i.elim0
  have one : Fin.succ (0 : Fin 1) = (1 : Fin 2) := by decide
  simp only [(machineConstruction table).result_defined_iff, atTime, args, one]

@[definability] instance blankTime_definable (table : Nat) : 𝚺ᴬ₁-Function₁[V] (atTime table) :=
  (blankTime_defined table).to_definable

theorem trace_from_blank (table : Nat) (n : V) : trace table n (0 : V) = atTime table n := by
  induction n using ISigma1.sigma1_succ_induction with
  | zero => simp
  | succ n ih => simp [ih]
  | hP => definability

def Terminal (table : Nat) (state : V) : Prop :=
  modelDigit table (π₁ state) (π₂ (π₂ state)) = 0

theorem tick_terminal {table : Nat} {state : V} (terminal : Terminal table state) :
    modelTick table state = state := by
  unfold modelTick
  dsimp only
  exact ite_eq_left terminal

theorem trace_terminal {table : Nat} {state : V} (terminal : Terminal table state) (n : V) :
    trace table n state = state := by
  induction n using ISigma1.sigma1_succ_induction with
  | zero => exact trace_zero table state
  | succ n ih => rw [trace_succ, ih, tick_terminal terminal]
  | hP => definability

/-- Advancing the clock leaves the existence of a halting witness equivalent
in any arithmetic model. The clock remains at the terminal configuration
when the chosen prefix already contains a halt. -/
theorem halts_after_prefix (table : Nat) (m : V) :
    (haltsDef table).val.Evalb (![] : Fin 0 → V) ↔
      ∃ n : V, Terminal table (trace table n (trace table m (0 : V))) := by
  rw [haltsDef_eval]
  constructor
  · rintro ⟨t, stop⟩
    change Terminal table (atTime table t) at stop
    rw [← trace_from_blank] at stop
    rcases le_total m t with forward | past
    · obtain ⟨n, rfl⟩ := exists_add_of_le forward
      exact ⟨n, trace_add table 0 m n ▸ stop⟩
    · obtain ⟨d, rfl⟩ := exists_add_of_le past
      refine ⟨0, ?_⟩
      rw [trace_zero, trace_add, trace_terminal stop]
      exact stop
  · rintro ⟨n, stop⟩
    refine ⟨m + n, ?_⟩
    change Terminal table (atTime table (m + n))
    rw [← trace_from_blank, trace_add]
    exact stop

end I0451.Arithmetization
