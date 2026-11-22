module
public import ZF192Support.Execution.Commands.Scheduler.Soundness
public import ZF192Support.Execution.Registers.Scheduler.InitialComplete
public import ZF192Support.Machine.RegisterProgram.Projection
public import Mathlib.Logic.Relation

@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace ZF192Support.NativeCommands
open ZF192Support.NativeSource ZF192Support.ModelCommands ZFR.ArithmeticRepresentation
open CCodeSoundness
open RegisterMachine.Source RegisterMachine.SourceSimulation

/-- Successors are predecessors of the accessibility relation for termination. -/
private def advances (t s : ScalarState) : Prop := scalarNext program s = some t

def scalar (s : State Nat) : ScalarState := ⟨s.pc, s.registers⟩

private theorem step_scalar {s t : State Nat} (h : programStep s t) :
    advances (scalar t) (scalar s) := by
  unfold advances
  obtain ⟨k, _, hk, i, hi, he⟩ := h
  have hpc : (scalar s).pc = k := by simpa [scalar] using hk
  simp only [scalarNext, hpc, hi, Option.bind_some]
  have hex := execute_nat i (scalar s)
  have he' : execute i ⟨(scalar s).pc, (scalar s).registers⟩ = some t := he
  rw [he'] at hex
  cases hs : scalarExecute i (scalar s) with
  | none => simp [hs] at hex
  | some u =>
    simp only [hs, Option.map_some, Option.some.injEq] at hex
    cases u
    cases t
    cases hex
    rfl

private theorem walk_of_reaches {s t : State Nat} (h : nativeReaches s t) :
    Relation.ReflTransGen advances (scalar t) (scalar s) := by
  obtain ⟨hist, hh, he⟩ := h (stateCode s) (modelListCons (stateCode s) 0)
    (nativeRunHistory_singleton _) (modelListHead_cons _ _)
  have step {a b} (hs : codedStep a b)
      (ih : ∃ before, stateCode before = a ∧
        Relation.ReflTransGen advances (scalar before) (scalar s)) :
      ∃ after, stateCode after = b ∧ Relation.ReflTransGen advances (scalar after) (scalar s) := by
    obtain ⟨bef, aft, rfl, rfl, run⟩ := hs
    obtain ⟨prev, eq, walk⟩ := ih
    have hprev := stateCode_injective eq
    subst prev
    exact ⟨aft, rfl, walk.head (step_scalar run)⟩
  obtain ⟨state, eq, walk⟩ := ModelScheduler.rooted_nat_induction hh
    (P := fun a => ∃ before, stateCode before = a ∧
      Relation.ReflTransGen advances (scalar before) (scalar s))
    ⟨s, rfl, .refl⟩ step
  exact stateCode_injective (eq.trans he) ▸ walk

private theorem acc_of_terminates {s : ScalarState} (h : Terminates (scalarNext program) s) :
    Acc advances s := by
  induction h with
  | done he => exact .intro _ (fun _ hn => by simp [advances, he] at hn)
  | more he _ ih =>
    apply Acc.intro
    intro _ hn
    exact Option.some.inj (he.symm.trans hn) ▸ ih

private def invariant (s : ScalarState) : Prop :=
  ∃ (n : Nat) (w : Store Nat), s = scalar (commandState 25 n 0 0 w) ∧ soundStore w

/-- A sound command store always completes another candidate with positive progress. -/
theorem native_initial_nonterminates (hn : ¬ ExactProvable 1) :
    ¬ Terminates (scalarNext program) (scalar (nativeInitial (M := Nat))) := by
  intro ht
  have acc := (acc_of_terminates ht).transGen
  have impossible (s : ScalarState) (ha : Acc (Relation.TransGen advances) s) : ¬ invariant s := by
    induction ha with
    | intro s _ ih =>
      rintro ⟨n, w, rfl, hs⟩
      obtain ⟨out, hist, hp, hhist, hend⟩ := sound_candidate_completes hn n w hs
      have run := candidate_run_success successBodyContract_proved n w out hist hhist hend
      have hne : scalar (commandState 25 n 0 0 w) ≠ scalar (commandState 25 (n + 1) 0 0 out) := by
        intro he
        have h := congrArg (fun s : ScalarState => s.registers 6) he
        change n = n + 1 at h
        omega
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp (walk_of_reaches run) with he | hr
      · exact hne he
      · exact ih _ hr ⟨n + 1, out, rfl, hp⟩
  exact impossible _ acc ⟨2, ⟨0, 0, 0, 0⟩, rfl, zeroStore_sound⟩

end ZF192Support.NativeCommands
