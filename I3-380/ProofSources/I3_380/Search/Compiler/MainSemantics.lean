module
public import I3_380.Search.Compiler.TrialSemantics
public import I3_380.Search.Compiler.ProgramMatch
public import I3_380.Search.Compiler.SourceEquations
@[expose] public section

namespace PalomarI3380.Compiler.Source

def trialFlow (marker : Nat) : Flow :=
  if marker = 1 then .halt else .normal

def SchedulerState.finish (s : SchedulerState) (pending marker : Nat) : SchedulerState :=
  ⟨s.begin.nextWord, pending, if marker = 1 then 0 else marker⟩

theorem runPattern_index (pattern : List Pattern) (s : Store) :
    runPattern pattern s np = s np := by
  induction pattern generalizing s with
  | nil => rfl
  | cons p ps ih =>
    exact (ih (p.effect s)).trans (p.frame s np (by decide) (by decide) (by decide))

theorem TrialInput.prepare_index (c : TrialInput) (s : SchedulerState) : c.prepare s np = s.nextWord := by
  by_cases orientation : c.orientation = 0 <;>
    simp [prepare, orientation, stageStore, SchedulerState.store, Store.set, np, pl, goal, fr, lv, gues, dc]

theorem TrialInput.prepare_pl (c : TrialInput) (s : SchedulerState) : c.prepare s pl = c.pending := by
  by_cases orientation : c.orientation = 0 <;>
    simp [prepare, orientation, stageStore, SchedulerState.store, Store.set, pl, goal, fr, lv, gues, dc]

theorem executes_trial (s : SchedulerState) (c : TrialInput) (eqn : Equation) (pending residual : Nat)
    (head : TrialInput.decode s.begin.pending = c)
    (trieRun : LineRuns compiledRows (c.prepare s.begin)
      (controls (runPattern (rowPattern eqn) (c.prepare s.begin)) pending residual)) :
    Executes main s.store (trialFlow (c.mark eqn s.begin.current))
      (s.finish pending (c.mark eqn s.begin.current)).store := by
  let start := c.prepare s.begin
  let compared := runPattern (rowPattern eqn) start
  let state := controls compared pending residual
  have hInput := mainInput_runs s
  rw [head] at hInput
  have scratch : ClearScratch state :=
    ((runPattern_scratch _ _ (c.prepare_scratch s.begin)).setPL _).setSel _
  have output := mainOutput_runs state scratch
  have index : state np = s.begin.nextWord := by
    have noChange : state np = compared np := by simp [state, controls, Store.set, np, pl, sel]
    exact noChange.trans ((runPattern_index _ _).trans (c.prepare_index _))
  have pendingEq : state pl = pending := by simp [state, controls, Store.set, pl, sel]
  have marker : remainingMarker state = c.mark eqn s.begin.current :=
    (remainingMarker_controls _ _ _).trans (prepared_row_marker _ _ _)
  rw [index, pendingEq, marker] at output
  have before := (hInput.append trieRun).append output
  unfold main
  by_cases halts : c.mark eqn s.begin.current = 1
  · simp only [trialFlow, SchedulerState.finish, halts, ↓reduceIte]
    rw [halts] at before
    exact before.finish (acceptance_halt _ _) rfl
  · simp only [trialFlow, SchedulerState.finish, halts, ↓reduceIte]
    exact before.finish (acceptance_continue _ _ _ halts) rfl

/-- Each main iteration has the behavior of one numeric rewrite check,
with a residual input no larger than the undecoded suffix. -/
theorem main_runs (s : SchedulerState) :
    let c := TrialInput.decode s.begin.pending
    ∃ eqn ∈ rows, ∃ pending ≤ c.pending,
      Executes main s.store (trialFlow (c.mark eqn s.begin.current))
        (s.finish pending (c.mark eqn s.begin.current)).store := by
  dsimp only
  let c := TrialInput.decode s.begin.pending
  obtain ⟨row, member, pending, residual, bound, run⟩ :=
    literalRows_run (c.prepare s.begin) (c.prepare_scratch _)
  obtain ⟨eqn, inRows, rfl⟩ := List.mem_map.mp member
  have limit : pending ≤ c.pending := (c.prepare_pl s.begin) ▸ bound
  exact ⟨eqn, inRows, pending, limit, executes_trial s c eqn pending residual rfl run⟩

/-- A designated row can be run with any desired following suffix. The
selector data depends only on the row, independently of all trial fields. -/
theorem main_covers {e : Equation} (member : e ∈ rows) :
    ∃ selectors : List Nat, ∀ (s : SchedulerState) (c : TrialInput) (tail : Nat),
      s.begin.pending = ({ c with pending := encodeFields selectors tail } : TrialInput).encode →
      Executes main s.store (trialFlow (c.mark e s.begin.current))
        (s.finish tail (c.mark e s.begin.current)).store := by
  obtain ⟨selectors, cover⟩ := literalRows_cover member
  refine ⟨selectors, fun s c tail source => ?_⟩
  let d := {c with pending := encodeFields selectors tail}
  have decode : TrialInput.decode s.begin.pending = d := by
    exact (congrArg TrialInput.decode source).trans (TrialInput.decode_encode d)
  have run := cover (c.prepare s.begin) tail (c.prepare_scratch s.begin)
  have hInput : d.prepare s.begin = controls (c.prepare s.begin) (encodeFields selectors tail) 0 :=
    c.prepare_pending _ _
  have output : controls (runPattern (rowPattern e) (d.prepare s.begin)) tail 0 =
      controls (runPattern (rowPattern e) (c.prepare s.begin)) tail 0 := by
    rw [hInput, runPattern_controls, controls_override]
  have actual : LineRuns compiledRows (d.prepare s.begin)
      (controls (runPattern (rowPattern e) (d.prepare s.begin)) tail 0) := by
    rw [output, hInput]
    exact run
  exact executes_trial s d e tail 0 decode actual

end PalomarI3380.Compiler.Source
