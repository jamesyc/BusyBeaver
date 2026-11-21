module
public import I0451.Logic.Formula

/-! The command stream used by the nine-register search. A new candidate
is loaded without a decrement. On later iterations the nonempty queue
loses one before its operands are read, so inter-command tails have a
one-unit delimiter. -/
@[expose] public section
namespace I0451.Logic

open M6.Source.Cantor

inductive Command (α : Type := Nat) where
  | mp (operand : α)
  | drop (operand : α)
  | nip (operand : α)
  | extra (operand : α)
  | ax (mode operand parameter formula : α)
  deriving DecidableEq, Repr

def unpackCommand (payload : Nat) : Command × Nat :=
  let header := decode payload
  let operand := decode header.2
  match header.1 with
  | 0 => (.mp operand.1, operand.2)
  | 1 => (.drop operand.1, operand.2)
  | 2 => (.nip operand.1, operand.2)
  | 3 => (.extra operand.1, operand.2)
  | mode + 4 =>
    let parameter := decode operand.2
    let formula := decode parameter.2
    (.ax mode operand.1 parameter.1 formula.1, formula.2)

def packCommand (command : Command) (tail : Nat) : Nat :=
  match command with
  | .mp p => pair 0 (pair p tail)
  | .drop p => pair 1 (pair p tail)
  | .nip p => pair 2 (pair p tail)
  | .extra p => pair 3 (pair p tail)
  | .ax k p y f => pair (k + 4) (pair p (pair y (pair f tail)))

@[simp] theorem unpack_pack_command (command : Command) (tail : Nat) :
    unpackCommand (packCommand command tail) = (command, tail) := by
  cases command <;> simp [packCommand, unpackCommand, decode_pair]

private theorem decode_tail_le (x : Nat) : (decode x).2 ≤ x := by
  have h := decode_bounds x
  omega

theorem unpack_tail_le (payload : Nat) : (unpackCommand payload).2 ≤ payload := by
  let rest := (decode payload).2
  let suffix := (decode rest).2
  have short : suffix ≤ payload := Nat.le_trans (decode_tail_le rest) (decode_tail_le payload)
  have long : (decode (decode suffix).2).2 ≤ payload :=
    Nat.le_trans (decode_tail_le _) (Nat.le_trans (decode_tail_le suffix) short)
  unfold unpackCommand
  simp only
  generalize (decode payload).1 = k
  rcases k with _ | _ | _ | _ | m
  · exact short
  · exact short
  · exact short
  · exact short
  · exact long

def packQueued : List Command → Nat
  | [] => 0
  | command :: rest => packCommand command (packQueued rest) + 1

/-- A stored candidate word includes the one-unit delimiters between its
commands. The first read of a fresh candidate does not use a delimiter. -/
def packCandidate : List Command → Nat
  | [] => 0
  | command :: rest => packCommand command (packQueued rest)

/-- The numeric scheduler state, independently of the current proof store. -/
structure SearchState (Store : Type) where
  nextCandidate : Nat
  queued : Nat
  store : Store

abbrev CommandEval (Store : Type) := Command → Store → Option Store

def SearchState.step {Store : Type} (exec : CommandEval Store)
    (state : SearchState Store) : Option (SearchState Store) :=
  let loading := state.queued == 0
  let payload := if loading then state.nextCandidate else state.queued - 1
  let command := unpackCommand payload
  (exec command.1 state.store).map fun after =>
    ⟨if loading then state.nextCandidate + 1 else state.nextCandidate, command.2, after⟩

def SearchState.run {Store : Type} (exec : CommandEval Store) :
    Nat → SearchState Store → Option (SearchState Store)
  | 0, state => some state
  | n + 1, state => (state.step exec).bind (SearchState.run exec n)

def SearchHalts {Store : Type} (exec : CommandEval Store) (start : SearchState Store) : Prop :=
  ∃ n, start.run exec n = none

def SearchReaches {Store : Type} (exec : CommandEval Store)
    (start finish : SearchState Store) : Prop :=
  ∃ n, start.run exec n = some finish

private theorem search_run_add {Store : Type} (exec : CommandEval Store) (m n : Nat)
    (start : SearchState Store) :
    start.run exec (m + n) = (start.run exec m).bind (SearchState.run exec n) := by
  induction m generalizing start with
  | zero => simp [SearchState.run]
  | succ m ih =>
    rw [Nat.succ_add, SearchState.run, SearchState.run]
    cases start.step exec
    · rfl
    · next next => exact ih next

theorem SearchReaches.trans {Store : Type} {exec : CommandEval Store}
    {a b c : SearchState Store} (first : SearchReaches exec a b) (rest : SearchReaches exec b c) :
    SearchReaches exec a c := by
  obtain ⟨m, mRun⟩ := first
  obtain ⟨n, nRun⟩ := rest
  exact ⟨m + n, by rw [search_run_add, mRun]; exact nRun⟩

private theorem not_halts_of_reach {Store : Type} {exec : CommandEval Store}
    {a b : SearchState Store} (first : SearchReaches exec a b) (never : ¬ SearchHalts exec a) :
    ¬ SearchHalts exec b := by
  obtain ⟨m, mRun⟩ := first
  rintro ⟨n, nRun⟩
  exact never ⟨m + n, by rw [search_run_add, mRun]; exact nRun⟩

private theorem next_of_running {Store : Type} {exec : CommandEval Store} {s : SearchState Store}
    (never : ¬ SearchHalts exec s) : ∃ t, s.step exec = some t := by
  cases equation : s.step exec with
  | none => exact (never ⟨1, by simp [SearchState.run, equation]⟩).elim
  | some t => exact ⟨t, rfl⟩

private theorem empty_queue_reachable {Store : Type} {exec : CommandEval Store}
    (s : SearchState Store) (never : ¬ SearchHalts exec s) :
    ∃ store, SearchReaches exec s ⟨s.nextCandidate, 0, store⟩ := by
  generalize size : s.queued = fuel
  induction fuel using Nat.strongRecOn generalizing s with
  | ind fuel ih =>
    by_cases empty : s.queued = 0
    · refine ⟨s.store, 0, ?_⟩
      cases s
      simp_all [SearchState.run]
    · obtain ⟨t, next⟩ := next_of_running never
      have prior : SearchReaches exec s t := ⟨1, by simp [SearchState.run, next]⟩
      have trimmed : t.queued < fuel ∧ t.nextCandidate = s.nextCandidate := by
        unfold SearchState.step at next
        simp only [beq_iff_eq, ite_eq_right empty] at next
        cases result : exec (unpackCommand (s.queued - 1)).1 s.store with
        | none => simp [result] at next
        | some after =>
          simp only [result, Option.map_some, Option.some.injEq] at next
          subst t
          have bound := unpack_tail_le (s.queued - 1)
          exact ⟨by change (unpackCommand (s.queued - 1)).2 < fuel; omega, rfl⟩
      obtain ⟨store, reached⟩ := ih t.queued trimmed.1 t (not_halts_of_reach prior never) rfl
      rw [trimmed.2] at reached
      exact ⟨store, prior.trans reached⟩

/-- Unless the search halts earlier, it reaches the start of every later
candidate. The proof relies only on strict decrease of the queued tail. -/
theorem candidate_reachable {Store : Type} {exec : CommandEval Store}
    {start : SearchState Store} (never : ¬ SearchHalts exec start)
    {candidate : Nat} (later : start.nextCandidate ≤ candidate) :
    ∃ store, SearchReaches exec start ⟨candidate, 0, store⟩ := by
  obtain ⟨store, emptied⟩ := empty_queue_reachable start never
  let extra := candidate - start.nextCandidate
  have target : candidate = start.nextCandidate + extra := by dsimp [extra]; omega
  rw [target]
  have advance : ∀ (n k : Nat) (s : Store), ¬ SearchHalts exec ⟨k, 0, s⟩ →
      ∃ last, SearchReaches exec ⟨k, 0, s⟩ ⟨k + n, 0, last⟩ := by
    intro n
    induction n with
    | zero =>
      intro k s _
      exact ⟨s, 0, rfl⟩
    | succ n ih =>
      intro k s noStop
      let base : SearchState Store := ⟨k, 0, s⟩
      obtain ⟨t, moves⟩ := next_of_running (s := base) noStop
      have tick : SearchReaches exec base t := ⟨1, by simp [SearchState.run, moves]⟩
      have next : t.nextCandidate = k + 1 := by
        change ((exec (unpackCommand k).1 s).map fun after =>
          (⟨k + 1, (unpackCommand k).2, after⟩ : SearchState Store)) = some t at moves
        cases value : exec (unpackCommand k).1 s with
        | none => simp [value] at moves
        | some after =>
          simp only [value, Option.map_some, Option.some.injEq] at moves
          subst t
          rfl
      obtain ⟨mid, drains⟩ := empty_queue_reachable t (not_halts_of_reach tick noStop)
      rw [next] at drains
      have first := tick.trans drains
      obtain ⟨last, runs⟩ := ih (k + 1) mid (not_halts_of_reach first noStop)
      have count : k + 1 + n = k + (n + 1) := by omega
      rw [count] at runs
      exact ⟨last, first.trans runs⟩
  obtain ⟨last, finished⟩ := advance extra start.nextCandidate store
    (not_halts_of_reach emptied never)
  exact ⟨last, emptied.trans finished⟩

/-- The effect of a sequence of commands on an arbitrary proof store. -/
def executeCommands {α Store : Type} (exec : Command α → Store → Option Store) :
    List (Command α) → Store → Option Store
  | [], s => some s
  | c :: cs, s => (exec c s).bind (executeCommands exec cs)

theorem run_queued {Store : Type} (exec : CommandEval Store) (commands : List Command)
    (candidate : Nat) (store : Store) :
    SearchState.run exec commands.length ⟨candidate, packQueued commands, store⟩ =
      (executeCommands exec commands store).map fun after => ⟨candidate, 0, after⟩ := by
  induction commands generalizing store with
  | nil => rfl
  | cons c cs ih =>
    have positive : packCommand c (packQueued cs) + 1 ≠ 0 := Nat.succ_ne_zero _
    have head : SearchState.step exec ⟨candidate, packQueued (c :: cs), store⟩ =
        (exec c store).map (fun mid => ⟨candidate, packQueued cs, mid⟩) := by
      simp only [SearchState.step, packQueued, beq_iff_eq, ite_eq_right positive,
        Nat.add_sub_cancel, unpack_pack_command]
    simp only [List.length_cons, SearchState.run, head, executeCommands]
    cases run : exec c store with
    | none => rfl
    | some mid => exact ih mid

theorem run_candidate {Store : Type} (exec : CommandEval Store) (command : Command)
    (commands : List Command) (store : Store) :
    SearchState.run exec (commands.length + 1) ⟨packCandidate (command :: commands), 0, store⟩ =
      (executeCommands exec (command :: commands) store).map fun after =>
        ⟨packCandidate (command :: commands) + 1, 0, after⟩ := by
  have first : SearchState.step exec ⟨packCandidate (command :: commands), 0, store⟩ =
      (exec command store).map fun mid => ⟨packCandidate (command :: commands) + 1,
        packQueued commands, mid⟩ := by
    simp only [SearchState.step, packCandidate, beq_self_eq_true, ite_true, unpack_pack_command]
  simp only [SearchState.run, first, executeCommands]
  cases run : exec command store with
  | none => rfl
  | some mid => exact run_queued exec commands (packCandidate (command :: commands) + 1) mid

/-- A command word that halts on every incoming store forces the
enumerator to halt. This permits earlier candidates to leave arbitrary
stores at the command boundary. -/
theorem halts_of_command_word {Store : Type} {exec : CommandEval Store}
    {initial : SearchState Store} (command : Command) (commands : List Command)
    (later : initial.nextCandidate ≤ packCandidate (command :: commands))
    (works : ∀ store, executeCommands exec (command :: commands) store = none) :
    SearchHalts exec initial := by
  apply Classical.byContradiction
  intro never
  obtain ⟨store, reached⟩ := candidate_reachable never later
  have proof := run_candidate exec command commands store
  rw [works] at proof
  exact (not_halts_of_reach reached never) ⟨commands.length + 1, proof⟩

end I0451.Logic
