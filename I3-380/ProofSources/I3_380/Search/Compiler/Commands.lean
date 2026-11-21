module
public import I3_380.Search.Compiler.Source
public import I3_380.Search.Compiler.Optimization
@[expose] public section

namespace PalomarI3380.Compiler

theorem Executes.deterministic {p : Program} {s t u : Store} {out flow : Flow}
    (h : Executes p s out t) (k : Executes p s flow u) : out = flow ∧ t = u := by
  induction h generalizing flow u with
  | instruction op s =>
    cases k
    exact ⟨rfl, rfl⟩
  | leftExit first exit ih =>
    cases k with
    | leftExit next exit' =>
      obtain ⟨rfl, rfl⟩ := ih next
      rw [exit, Option.some.injEq] at exit'
      exact ⟨exit', rfl⟩
    | rightExit next _ _ | reenter next _ _ =>
      rw [(ih next).1] at exit
      contradiction
  | rightExit first second exit ihL ihR =>
    cases k with
    | leftExit next impossible =>
      rw [← (ihL next).1] at impossible
      contradiction
    | rightExit next right exit' =>
      obtain ⟨_, rfl⟩ := ihL next
      obtain ⟨rfl, rfl⟩ := ihR right
      rw [exit, Option.some.injEq] at exit'
      exact ⟨exit', rfl⟩
    | reenter next right _ =>
      obtain ⟨_, rfl⟩ := ihL next
      rw [(ihR right).1] at exit
      contradiction
  | reenter first second again ihL ihR ihAgain =>
    cases k with
    | leftExit next impossible =>
      rw [← (ihL next).1] at impossible
      contradiction
    | rightExit next right exit =>
      obtain ⟨_, rfl⟩ := ihL next
      rw [← (ihR right).1] at exit
      contradiction
    | reenter next right rest =>
      obtain ⟨_, rfl⟩ := ihL next
      obtain ⟨_, rfl⟩ := ihR right
      exact ihAgain rest

namespace Source

variable {s t after : Store} {r : Register} {body : Program} {out : Flow}

theorem dec_zero (h : s r = 0) : Executes (dec r) s (.escape 0) s := by
  simpa only [dec, Op.effect, h, ↓reduceIte] using Executes.instruction (.decNZ r) s

theorem dec_pos (h : s r ≠ 0) : Executes (dec r) s .normal (s.set r (s r - 1)) := by
  simpa only [dec, Op.effect, h, ↓reduceIte] using Executes.instruction (.decNZ r) s

theorem run_inc (r : Register) (s : Store) : Executes (inc r) s .normal (s.set r (s r + 1)) :=
  .instruction _ _

theorem run_break (n : Nat) (s : Store) :
    Executes (break_ (n + 1)) s (.escape n) s := .instruction _ _

theorem run_continue (n : Nat) (s : Store) :
    Executes (continue_ n) s (.repeatAt n) s := .instruction _ _

theorem run_halt (s : Store) : Executes halt s .halt s := .instruction _ _

theorem then_normal {p q : Program} (h : Executes p s .normal t) (k : Executes q t .normal after) :
    Executes (.seq p q) s .normal after := .rightExit h k rfl

theorem then_halt {p q : Program} (h : Executes p s .normal t) (k : Executes q t .halt after) :
    Executes (.seq p q) s .halt after := .rightExit h k rfl

theorem ifPositive_zero (h : s r = 0) : Executes (ifPositive r body) s .normal s :=
  .leftExit (dec_zero h) rfl

theorem ifPositive_pos_normal (h : s r ≠ 0) (run : Executes body (s.set r (s r - 1)) .normal t) :
    Executes (ifPositive r body) s .normal t :=
  then_normal (dec_pos h) run

theorem ifPositive_pos_halt (h : s r ≠ 0) (run : Executes body (s.set r (s r - 1)) .halt t) :
    Executes (ifPositive r body) s .halt t :=
  then_halt (dec_pos h) run

theorem ifZero_pos (h : s r ≠ 0) : Executes (ifZero r body) s .normal (s.set r (s r - 1)) :=
  .leftExit (.rightExit (dec_pos h) (run_break 0 _) rfl) rfl

theorem ifZero_zero_normal (h : s r = 0) (run : Executes body s .normal t) :
    Executes (ifZero r body) s .normal t :=
  then_normal (.leftExit (dec_zero h) rfl) run

theorem ifZero_zero_halt (h : s r = 0) (run : Executes body s .halt t) :
    Executes (ifZero r body) s .halt t :=
  then_halt (.leftExit (dec_zero h) rfl) run

theorem whilePositive_zero (h : s r = 0) : Executes (whilePositive r body) s .normal s :=
  .leftExit (dec_zero h) rfl

theorem whilePositive_pos (h : s r ≠ 0)
    (first : Executes body (s.set r (s r - 1)) .normal t) (rest : Executes (whilePositive r body) t out after) :
    Executes (whilePositive r body) s out after :=
  .reenter (dec_pos h) (.rightExit first (run_continue 1 _) rfl) rest

theorem run_clear (r : Register) (s : Store) : Executes (clear r) s .normal (s.set r 0) := by
  generalize h : s r = n
  induction n generalizing s with
  | zero =>
    change Executes (.seq (dec r) (continue_ 0)) s .normal (s.set r 0)
    rw [← h, Store.set_same]
    exact .leftExit (dec_zero h) rfl
  | succ n ih =>
    change Executes (.seq (dec r) (continue_ 0)) s .normal (s.set r 0)
    have next := ih (s.set r (s r - 1)) (by simp [h])
    rw [Store.set_set] at next
    exact .reenter (dec_pos (by omega)) (run_continue 0 _) next

/-- A list of normal command steps, before choosing the compiler's
binary association of the instructions. -/
inductive LineRuns : List Program → Store → Store → Prop where
  | nil {start : Store} : LineRuns [] start start
  | cons {p : Program} {ps : List Program} {start middle finish : Store} :
    Executes p start .normal middle → LineRuns ps middle finish → LineRuns (p :: ps) start finish

theorem LineRuns.block {ps : List Program} (runs : LineRuns ps s t) :
    Executes (Source.block ps) s .normal t := by
  induction runs with
  | nil => exact .instruction _ _
  | @cons p ps s next final first rest ih =>
    cases ps with
    | nil => cases rest; exact first
    | cons q qs => exact then_normal first ih

theorem LineRuns.append {xs ys : List Program} (h : LineRuns xs s t) (k : LineRuns ys t after) :
    LineRuns (xs ++ ys) s after := by
  induction h with
  | nil => exact k
  | cons run _ ih => exact .cons run (ih k)

end Source
end PalomarI3380.Compiler
