module
public import I3_380.Search.Compiler.SchedulerState
@[expose] public section

namespace PalomarI3380.Compiler.Source

def gateStore {V : Type} [OfNat V 0] (index pending mark : V) : Store V :=
  (SchedulerState.mk index pending 0).store.set gues mark

def remainingMarker {V : Type} [OfNat V 0] [DecidableEq V] (s : Store V) : V :=
  mark s (s fr = s lv)

set_option maxHeartbeats 4000000 in
theorem mainOutput_runs (s : Store) (ready : ClearScratch s) :
    LineRuns mainOutput s (gateStore (s np) (s pl) (remainingMarker s)) := by
  let s₁ := s.set sel 0
  let s₂ := (s₁.set fr 0).set exp (s fr)
  let s₃ := (s₂.set lv 0).set tok (s lv)
  let s₄ := ((s₃.set exp 0).set tok 0).set gues (remainingMarker s)
  have h₁ := run_clear sel s
  have h₂ : Executes (move fr exp) s₁ .normal s₂ := by
    have exp0 : s₁ exp = 0 := by simpa [s₁, Store.set, sel, exp] using ready.expZero
    have front : s₁ fr = s fr := by simp [s₁, Store.set, sel, fr]
    simpa only [exp0, front, Nat.zero_add, s₂] using run_move (a := fr) (b := exp) (by decide) s₁
  have h₃ : Executes (move lv tok) s₂ .normal s₃ := by
    have tok0 : s₂ tok = 0 := by simpa [s₂, s₁, Store.set, sel, fr, exp, tok] using ready.tokZero
    have back : s₂ lv = s lv := by simp [s₂, s₁, Store.set, sel, fr, exp, lv]
    simpa only [tok0, back, Nat.zero_add, s₃] using run_move (a := lv) (b := tok) (by decide) s₂
  have h₄ : Executes compare s₃ .normal s₄ := by
    have left : s₃ exp = s fr := by simp [s₃, s₂, Store.set, lv, tok, exp]
    have right : s₃ tok = s lv := Store.get_set _ _ _
    have candidate : s₃ gues = s gues := by simp [s₃, s₂, s₁, Store.set, sel, fr, exp, lv, tok, gues]
    simpa only [left, right, candidate, s₄, remainingMarker, mark] using run_compare s₃
  have h₅ := run_clear dc s₄
  have result : s₄.set dc 0 = gateStore (s np) (s pl) (remainingMarker s) := by
    apply store_ext <;>
      simp [s₄, s₃, s₂, s₁, gateStore, SchedulerState.store, emptyStore, Store.set,
        np, pl, sel, goal, fr, gues, lv, dc, tok, exp,
        show s 3 = 0 from ready.goalZero, show s 8 = 0 from ready.auxZero,
        show s 9 = 0 from ready.tempZero]
  rw [result] at h₅
  exact .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ (.cons h₅ .nil))))

theorem acceptance_halt (index pending : Nat) :
    Executes acceptGate (gateStore index pending 1) .halt (SchedulerState.mk index pending 0).store := by
  let state := gateStore index pending 1
  let next := (SchedulerState.mk index pending 0).store
  have marker : state gues = 1 := Store.get_set _ _ _
  have zero : next gues = 0 := by simp [next, SchedulerState.store, emptyStore, Store.set, gues, np, pl, goal]
  have counted : state.set gues (state gues - 1) = next := by
    rw [marker, Nat.sub_self]
    change (next.set gues 1).set gues 0 = next
    rw [Store.set_set]
    simpa only [zero] using Store.set_same next gues
  apply ifPositive_pos_halt (s := state) (by rw [marker]; decide)
  rw [counted]
  exact .leftExit (ifZero_zero_halt zero (run_halt next)) rfl

theorem acceptance_continue (index pending marker : Nat) (nonhalt : marker ≠ 1) :
    Executes acceptGate (gateStore index pending marker) .normal
      (SchedulerState.mk index pending marker).store := by
  let s := gateStore index pending marker
  let out := (SchedulerState.mk index pending marker).store
  have hs : s gues = marker := Store.get_set _ _ _
  by_cases dropped : marker = 0
  · have same : s = out := by
      have zero : out gues = 0 := by simp [out, SchedulerState.store, emptyStore, Store.set, gues, np, pl, goal]
      change ((SchedulerState.mk index pending 0).store.set gues marker) = out
      cases dropped
      simpa only [zero] using Store.set_same out gues
    change Executes acceptGate s .normal out
    exact same ▸ ifPositive_zero (body := block [ifZero gues halt, inc goal, inc goal, move gues goal]) (hs.trans dropped)
  · have positive : 2 ≤ marker := by omega
    let t := s.set gues (marker - 1)
    have markerT : t gues = marker - 1 := Store.get_set _ _ _
    let u₀ := t.set gues (marker - 2)
    have hGate : Executes (ifZero gues halt) t .normal u₀ := by
      have h := ifZero_pos (r := gues) (body := halt) (s := t) (by omega)
      simpa only [markerT, show marker - 1 - 1 = marker - 2 by omega, u₀] using h
    let v₁ := u₀.set goal 1
    let v₂ := v₁.set goal 2
    have goalU : u₀ goal = 0 := by
      simp [u₀, t, s, gateStore, SchedulerState.store, Store.set, goal, gues]
    have inc₁ : Executes (inc goal) u₀ .normal v₁ := by
      simpa only [v₁, goalU, Nat.zero_add] using run_inc goal u₀
    have inc₂ : Executes (inc goal) v₁ .normal v₂ := by
      simpa only [v₂, show v₁ goal = 1 from Store.get_set _ _ _] using run_inc goal v₁
    have final := run_move (a := gues) (b := goal) (by decide) v₂
    have markerV : v₂ gues = marker - 2 := by simp [v₂, v₁, u₀, Store.set, goal, gues]
    rw [show v₂ goal = 2 from Store.get_set _ _ _, markerV, show 2 + (marker - 2) = marker by omega] at final
    have finish : (v₂.set gues 0).set goal marker = out := by
      apply store_ext <;>
        simp [v₂, v₁, u₀, t, s, out, gateStore, SchedulerState.store, emptyStore,
          Store.set, np, pl, goal, gues]
    rw [finish] at final
    apply ifPositive_pos_normal (s := s) (by rwa [hs])
    rw [hs]
    exact then_normal hGate (then_normal inc₁ (then_normal inc₂ final))

theorem LineRuns.finish {ps : List Program} {s t : Store} (before : LineRuns ps s t)
    {p : Program} {out : Flow} {finish : Store} (after : Executes p t out finish)
    (proper : out.fromRight = some out) : Executes (Source.block (ps ++ [p])) s out finish := by
  induction before with
  | nil => exact after
  | @cons head ps start middle last h _ ih =>
    have tail := ih after
    cases shape : ps ++ [p] with
    | nil => simp at shape
    | cons next rest =>
      change Executes (Source.block (head :: (ps ++ [p]))) start out finish
      rw [shape]
      rw [shape] at tail
      exact .rightExit h tail proper

end PalomarI3380.Compiler.Source
