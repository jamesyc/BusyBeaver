module
public import I3_334.Search.SearchScan
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (whilePositive whilePositive_zero whilePositive_pos)
open Templates (Guarded)

structure MatchScan where
  valid : Bool
  rest : Nat

/-- The rest is advanced even after a mismatch, exactly like the
physical verifier with its cleared marker. -/
def scanMatch : List Token → Nat → MatchScan
  | [], front => ⟨true, front⟩
  | token :: rest, front =>
    let actual := rawFields front
    let next := scanMatch rest actual.rest
    ⟨decide (token.arity+1 = actual.arityField ∧ token.tag = actual.tag) && next.valid,
      next.rest⟩

theorem scanMatch_exact (tokens : List Token) (front : Nat) :
    matchTokens tokens front =
      if (scanMatch tokens front).valid then some (scanMatch tokens front).rest else none := by
  induction tokens generalizing front with
  | nil => rfl
  | cons token more ih =>
    let act := rawFields front
    by_cases field : token.arity+1 = act.arityField ∧ token.tag = act.tag
    · have frontEq : Cantor.pair (token.arity+1) (Cantor.pair token.tag act.rest) = front := by
        rw [field.1, field.2]
        exact rawFields_rebuild front
      have pop : readToken front = some (token,act.rest) := by
        exact (congrArg readToken frontEq.symm).trans (readToken_encode token act.rest)
      rw [matchTokens, pop]
      change (if token = token then matchTokens more act.rest else none) = _
      rw [ite_eq_left rfl]
      have hit : (scanMatch (token :: more) front).valid = (scanMatch more act.rest).valid := by
        change (decide (token.arity+1 = act.arityField ∧ token.tag = act.tag) &&
          (scanMatch more act.rest).valid) = _
        simp [field]
      rw [hit]
      exact ih act.rest
    · have failed : (scanMatch (token :: more) front).valid = false := by
        change (decide (token.arity+1 = act.arityField ∧ token.tag = act.tag) &&
          (scanMatch more act.rest).valid) = _
        simp [field]
      rw [failed]
      cases pop : readToken front with
      | none => simp [matchTokens,pop]
      | some data =>
        obtain ⟨other, tail⟩ := data
        have notToken : other ≠ token := by
          intro same
          subst other
          have fieldEq := readToken_sound pop
          have eq := congrArg rawFields fieldEq
          rw [rawFields_encode] at eq
          exact field ⟨congrArg RawFields.arityField eq, congrArg RawFields.tag eq⟩
        simp [matchTokens, pop, notToken]


def scanLoopEffect (slot : Fin 4) (s : Store) : Store :=
  let terms := scanRaw (bias slot) (s tmp) (s goal)
  let result := scanMatch terms.1 (s fr)
  (((s.set goal 0).set tmp terms.2).set fr result.rest).set gues (markedIf (s gues) (result.valid = true))

theorem scanBody_clean (slot : Fin 4) (s : Store) (clean : Scratch s) :
    Scratch (scanBodyEffect slot s) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [scanBodyEffect, Store.set, expected, tok, u, goal, tmp, fr, gues,
      clean.expectedEmpty, clean.tokenEmpty, clean.auxiliaryEmpty]

/-- The loop reads the entire finite prefix determined by its pending
arity count and compares both fields of every token. -/
theorem run_scanLoop (slot : Fin 4) (s : Store) (clean : Scratch s) :
    Executes (whilePositive goal (scanBody slot)) s .normal (scanLoopEffect slot s) := by
  induction size : s goal + s tmp using Nat.strongRecOn generalizing s with
  | ind measure ih =>
    cases pending : s goal with
    | zero =>
      have empty : scanRaw (bias slot) (s tmp) 0 = ([], s tmp) := by rw [scanRaw]
      simp only [scanLoopEffect, pending, empty, scanMatch, Prod.fst, Prod.snd, markedIf, ↓reduceIte]
      rw [← pending, Store.set_same, Store.set_same, Store.set_same, Store.set_same]
      exact whilePositive_zero pending
    | succ n =>
      let start := s.set goal n
      let next := scanBodyEffect slot start
      let d := readRaw (bias slot) (s tmp)
      let f := rawFields (s fr)
      let aligns := d.1.arity+1 = f.arityField ∧ d.1.tag = f.tag
      let scanned := scanRaw (bias slot) d.2 (n+d.1.arity)
      let result := scanMatch scanned.1 f.rest
      have ready : Scratch start := by
        exact ⟨by simpa [start,Store.set,goal,expected] using clean.expectedEmpty,
          by simpa [start,Store.set,goal,tok] using clean.tokenEmpty,
          by simpa [start,Store.set,goal,u] using clean.auxiliaryEmpty⟩
      have first := run_scanBody slot start ready
      have fields : next =
          (((s.set tmp d.2).set fr f.rest).set goal (n+d.1.arity)).set gues (markedIf (s gues) aligns) := by
        simp only [next,scanBodyEffect]
        funext i
        by_cases g : i = goal <;> by_cases dt : i = tmp <;> by_cases rt : i = fr <;>
          by_cases m : i = gues <;> simp [start,d,f,aligns,Store.set,goal,tmp,fr,gues,g,dt,rt,m]
      have left : next goal = n+d.1.arity := by simp [fields,Store.set,goal,tmp,fr,gues]
      have dict : next tmp = d.2 := by simp [fields,Store.set,goal,tmp,fr,gues]
      have target : next fr = f.rest := by simp [fields,Store.set,goal,tmp,fr,gues]
      have mark : next gues = markedIf (s gues) aligns := by rw [fields,Store.get_set]
      have smaller : next goal + next tmp < measure := by
        rw [left,dict]
        have budget := readRaw_budget (bias slot) (s tmp)
        dsimp only [d]
        omega
      have tail := ih _ smaller next (scanBody_clean slot start ready) rfl
      have finish : scanLoopEffect slot next = scanLoopEffect slot s := by
        have full : scanRaw (bias slot) (s tmp) (s goal) = (d.1 :: scanned.1, scanned.2) := by
          rw [pending, scanRaw_cons]
        simp only [scanLoopEffect,dict,left,target,mark,full,scanMatch,Prod.fst,Prod.snd,
          Bool.and_eq_true,decide_eq_true_eq,markedIf_and,aligns]
        funext i
        by_cases a : i = goal <;> by_cases b : i = tmp <;> by_cases c : i = fr <;>
          by_cases g : i = gues <;>
          simp [fields,Store.set,a,b,c,g,goal,tmp,fr,gues,scanned,result,aligns,f]
      rw [finish] at tail
      have decrement : s.set goal (s goal-1) = start := by simp [start,pending]
      have decremented : Executes (scanBody slot) (s.set goal (s goal-1)) .normal next := by
        rw [decrement]
        exact first
      exact whilePositive_pos (by omega) decremented tail

end PalomarI3334.SearchProgram
