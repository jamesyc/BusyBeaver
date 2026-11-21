module
public import I3_380.Search.Compiler.SchedulerState
@[expose] public section

namespace PalomarI3380.Compiler.Source

set_option maxHeartbeats 5000000 in
theorem mainInput_runs (s : SchedulerState) :
    LineRuns mainInput s.store ((TrialInput.decode s.begin.pending).prepare s.begin) := by
  let a := s.begin
  let start := a.store
  let g := Cantor.unpair a.pending
  let p := Cantor.unpair g.2
  let o := Cantor.unpair p.2
  let d := Cantor.unpair o.2
  have boot : Executes (ifZero pl resetTask) s.store .normal start := s.begin_runs
  let loaded := (start.set pl g.2).set gues g.1
  have readGuess : Executes (read gues) start .normal loaded := by
    have tok0 : start tok = 0 := by simp [start, SchedulerState.store, emptyStore, Store.set, np, pl, goal, tok]
    have aux0 : start u = 0 := by simp [start, SchedulerState.store, emptyStore, Store.set, np, pl, goal, u]
    have pending : start pl = a.pending := by simp [start, SchedulerState.store, Store.set, pl, goal]
    have marker : start gues = 0 := by simp [start, SchedulerState.store, emptyStore, Store.set, np, pl, goal, gues]
    simpa only [pending, marker, Nat.zero_add, loaded, g] using
      run_read (dst := gues) (by decide) (by decide) start tok0 aux0
  let duplicate := loaded.set lv g.1
  have copyGuess : Executes (copy gues lv) loaded .normal duplicate := by
    have aux0 : loaded u = 0 := by
      simp [loaded, start, SchedulerState.store, emptyStore, Store.set, np, pl, goal, gues, u]
    have back0 : loaded lv = 0 := by
      simp [loaded, start, SchedulerState.store, emptyStore, Store.set, np, pl, goal, gues, lv]
    simpa only [back0, Nat.zero_add, show loaded gues = g.1 from Store.get_set _ _ _, duplicate] using
      run_copy (a := gues) (b := lv) (by decide) (by decide) (by decide) loaded aux0
  let transferred := (duplicate.set goal 0).set fr a.current
  have moveWord : Executes (move goal fr) duplicate .normal transferred := by
    have front0 : duplicate fr = 0 := by
      simp [duplicate, loaded, start, SchedulerState.store, emptyStore, Store.set, np, pl, goal, gues, lv, fr]
    have value : duplicate goal = a.current := by
      simp [duplicate, loaded, start, SchedulerState.store, Store.set, pl, goal, gues, lv]
    simpa only [front0, Nat.zero_add, value, transferred] using
      run_move (a := goal) (b := fr) (by decide) duplicate
  let beforeContext := (transferred.set pl p.2).set sel p.1
  have contextPos : Executes (read sel) transferred .normal beforeContext := by
    have tok0 : transferred tok = 0 := by
      simp [transferred, duplicate, loaded, start, SchedulerState.store, emptyStore, Store.set,
        np, pl, goal, gues, lv, fr, tok]
    have aux0 : transferred u = 0 := by
      simp [transferred, duplicate, loaded, start, SchedulerState.store, emptyStore, Store.set,
        np, pl, goal, gues, lv, fr, u]
    have pending : transferred pl = g.2 := by
      simp [transferred, duplicate, loaded, Store.set, pl, goal, gues, lv, fr]
    have selector0 : transferred sel = 0 := by
      simp [transferred, duplicate, loaded, start, SchedulerState.store, emptyStore, Store.set,
        np, pl, goal, gues, lv, fr, sel]
    simpa only [pending, selector0, Nat.zero_add, beforeContext, p] using
      run_read (dst := sel) (by decide) (by decide) transferred tok0 aux0
  let report := prefixSummary p.1 a.current g.1
  let afterContext := prefixEffect beforeContext report
  have context : Executes contextScan beforeContext .normal afterContext := by
    have exp0 : beforeContext exp = 0 := by
      simp [beforeContext, transferred, duplicate, loaded, start, SchedulerState.store, emptyStore,
        Store.set, np, pl, goal, gues, lv, fr, exp, sel]
    have tok0 : beforeContext tok = 0 := by
      simp [beforeContext, transferred, duplicate, loaded, start, SchedulerState.store, emptyStore,
        Store.set, np, pl, goal, gues, lv, fr, tok, sel]
    have aux0 : beforeContext u = 0 := by
      simp [beforeContext, transferred, duplicate, loaded, start, SchedulerState.store, emptyStore,
        Store.set, np, pl, goal, gues, lv, fr, u, sel]
    have front : beforeContext fr = a.current := by simp [beforeContext, transferred, Store.set, pl, sel, fr]
    have back : beforeContext lv = g.1 := by
      simp [beforeContext, transferred, duplicate, Store.set, pl, sel, fr, goal, lv]
    simpa only [show beforeContext sel = p.1 from Store.get_set _ _ _, front, back, afterContext, report] using
      run_contextScan beforeContext exp0 tok0 aux0
  let orientStore := (afterContext.set pl o.2).set sel o.1
  have readOrient : Executes (read sel) afterContext .normal orientStore := by
    have tok0 : afterContext tok = 0 := by
      simp [afterContext, prefixEffect, beforeContext, transferred, duplicate, loaded, start,
        SchedulerState.store, emptyStore, Store.set, np, pl, goal, gues, lv, fr, tok, sel]
    have aux0 : afterContext u = 0 := by
      simp [afterContext, prefixEffect, beforeContext, transferred, duplicate, loaded, start,
        SchedulerState.store, emptyStore, Store.set, np, pl, goal, gues, lv, fr, u, sel]
    have pending : afterContext pl = p.2 := by
      simp [afterContext, prefixEffect, beforeContext, Store.set, pl, sel, fr, lv, gues]
    have sel0 : afterContext sel = 0 := by
      simp [afterContext, prefixEffect, Store.set, sel, fr, lv, gues]
    simpa only [pending, sel0, Nat.zero_add, orientStore, o] using
      run_read (dst := sel) (by decide) (by decide) afterContext tok0 aux0
  let oriented := if o.1 = 0 then orientStore
    else let down := orientStore.set sel (o.1 - 1)
         (down.set fr (down lv)).set lv (down fr)
  have chooseSide : Executes (ifPositive sel side) orientStore .normal oriented := by
    have hSel : orientStore sel = o.1 := Store.get_set _ _ _
    by_cases direction : o.1 = 0
    · simpa only [oriented, direction, ↓reduceIte] using
        ifPositive_zero (body := side) (hSel.trans direction)
    · let next := orientStore.set sel (o.1 - 1)
      have temp0 : next tmp = 0 := by
        simp [next, orientStore, afterContext, prefixEffect, beforeContext, transferred, duplicate, loaded, start,
          SchedulerState.store, emptyStore, Store.set, np, pl, goal, gues, lv, fr, tmp, sel]
      have run := run_side next temp0
      have h : orientStore sel ≠ 0 := fun z => direction (hSel.symm.trans z)
      apply ifPositive_pos_normal h
      rw [hSel]
      simpa only [oriented, direction, ↓reduceIte] using run
  let afterSel := oriented.set sel 0
  have clearSel : Executes (clear sel) oriented .normal afterSel := run_clear sel oriented
  let outcome := (afterSel.set pl d.2).set dc d.1
  have readDict : Executes (read dc) afterSel .normal outcome := by
    have tok0 : afterSel tok = 0 := by
      by_cases direction : o.1 = 0 <;>
        simp [afterSel, oriented, direction, orientStore, afterContext, prefixEffect, beforeContext, transferred,
          duplicate, loaded, start, SchedulerState.store, emptyStore, Store.set, np, pl, goal, gues, lv, fr, tok, sel]
    have aux0 : afterSel u = 0 := by
      by_cases direction : o.1 = 0 <;>
        simp [afterSel, oriented, direction, orientStore, afterContext, prefixEffect, beforeContext, transferred,
          duplicate, loaded, start, SchedulerState.store, emptyStore, Store.set, np, pl, goal, gues, lv, fr, u, sel]
    have pending : afterSel pl = o.2 := by
      by_cases direction : o.1 = 0 <;>
        simp [afterSel, oriented, direction, orientStore, Store.set, pl, sel, lv, fr]
    have dict0 : afterSel dc = 0 := by
      by_cases direction : o.1 = 0 <;>
        simp [afterSel, oriented, direction, orientStore, afterContext, prefixEffect, beforeContext, transferred,
          duplicate, loaded, start, SchedulerState.store, emptyStore, Store.set, np, pl, goal, gues, lv, fr, dc, sel]
    simpa only [pending, dict0, Nat.zero_add, outcome, d] using
      run_read (dst := dc) (by decide) (by decide) afterSel tok0 aux0
  have exactStore : outcome = (TrialInput.decode a.pending).prepare a := by
    apply store_ext <;>
      by_cases direction : o.1 = 0 <;>
      simp [outcome, afterSel, oriented, direction, orientStore, afterContext, prefixEffect, beforeContext,
        transferred, duplicate, loaded, start, SchedulerState.store, emptyStore, Store.set, TrialInput.decode,
        TrialInput.prepare, TrialInput.prefix, stageStore, np, pl, goal, gues, lv, fr, dc, sel, mark,
        g, p, o, d, report] <;> rfl
  unfold mainInput
  rw [← exactStore]
  exact .cons boot (.cons readGuess (.cons copyGuess (.cons moveWord (.cons contextPos (.cons context
    (.cons readOrient (.cons chooseSide (.cons clearSel (.cons readDict .nil)))))))))

end PalomarI3380.Compiler.Source
