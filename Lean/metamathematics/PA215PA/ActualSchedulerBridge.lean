module

public import PA215PA.ActualCommandSemantics
public import PA215.Source.SchedulerSafety

@[expose] public section

/-! Explicit representation bridge from the core literal-source scheduler's
arithmetic store to the actual-profile PA interpreter. This discharges only
arithmetic schedule safety; literal macro transfer is a separate theorem. -/
namespace PA215.PA.ActualSchedulerBridge
open PA215.Source PA215.Source.Enumeration
open ActualCommandSemantics

def toState (s : CommandStore) : State := ⟨s.t,s.w,s.d,s.h⟩
def fromState (s : State) : CommandStore := ⟨s.t,s.w,s.d,s.h⟩

theorem from_to (s : CommandStore) : fromState (toState s) = s := rfl
theorem to_from (s : State) : toState (fromState s) = s := rfl

theorem eval_eq (c : Command) (s : CommandStore) :
    (commandEval c s).map toState = step c (toState s) := by
  cases c with
  | shift => simp only [commandEval,ActualCommandSemantics.step,CommandSemantics.step,toState]; split <;> simp_all only [ite_true,ite_false,Option.map_none,Option.map_some,toState]
  | mp x =>
    simp only [commandEval,ActualCommandSemantics.step,CommandSemantics.step,toState,
      AXCode.wim,NativeCalculus.wim]
    split <;> simp_all only [ite_true,ite_false,Option.map_none,Option.map_some,toState]
  | ax c x y => rfl

theorem runs_eq (cs : List Command) (s : CommandStore) :
    (commandsEval cs s).map toState = run cs (toState s) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    simp only [commandsEval,ActualCommandSemantics.run,← eval_eq]
    cases he : commandEval c s with
    | none => rfl
    | some out => simpa only [Option.bind_some,Option.map_some] using ih out

theorem initial_eq : toState commandInitial = initialState := rfl

theorem consistent_arithmeticSafe (hcons : PA215.PA.Consistent) :
    Scheduler.ArithmeticSafe := by
  intro n p rest hp hbad
  have h := runs_eq (schedule n ++ p) commandInitial
  rw [hbad,initial_eq] at h
  exact running_schedule_nonhalting hcons n p rest hp h.symm

#print axioms eval_eq
#print axioms runs_eq
#print axioms consistent_arithmeticSafe
end PA215.PA.ActualSchedulerBridge
