module
public import I3_334.Search.SearchInstructions
public import I3_334Support.Search.Compiler.ContextScan
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (then_normal dec_zero dec_pos dec continue_ run_continue prefixSummary)

def contextFieldEffect (s : Store) : Store :=
  let front := Cantor.unpair (s fr)
  let back := Cantor.unpair (s lv)
  ((s.set fr front.2).set lv back.2).set gues (markedIf (s gues) (front.1 = back.1))

theorem run_contextField (s : Store) (clean : Scratch s) :
    Executes contextField s .normal (contextFieldEffect s) := by
  let back := Cantor.unpair (s lv)
  let middle := (s.set lv back.2).set expected back.1
  have pop := run_pop (source := lv) (target := expected) (by decide) (by decide) (by decide) s
    clean.expectedEmpty clean.auxiliaryEmpty
  have eat := run_eat middle
    (by simpa [middle,Store.set,lv,expected,tok] using clean.tokenEmpty)
    (by simpa [middle,Store.set,lv,expected,u] using clean.auxiliaryEmpty)
  have output : consumeField middle = contextFieldEffect s := by
    funext i
    by_cases a : i = fr <;> by_cases b : i = lv <;> by_cases c : i = gues <;>
      by_cases d : i = expected <;>
      simp [consumeField,contextFieldEffect,middle,back,Store.set,a,b,c,d,fr,lv,gues,
        expected,clean.expectedEmpty,eq_comm]
  change Executes _ _ _ (consumeField middle) at eat
  rw [output] at eat
  exact then_normal pop eat

theorem contextField_clean (s : Store) (clean : Scratch s) : Scratch (contextFieldEffect s) := by
  refine ⟨?_,?_,?_⟩ <;>
    simp [contextFieldEffect,Store.set,fr,lv,gues,tok,u,expected,clean.expectedEmpty,
      clean.tokenEmpty,clean.auxiliaryEmpty]

def contextTokenEffect (s : Store) : Store :=
  let x := rawFields (s fr)
  let y := rawFields (s lv)
  ((s.set fr x.rest).set lv y.rest).set gues
    (markedIf (s gues) (x.arityField = y.arityField ∧ x.tag = y.tag))

theorem run_contextToken (s : Store) (clean : Scratch s) :
    Executes (.seq contextField contextField) s .normal (contextTokenEffect s) := by
  have first := run_contextField s clean
  have second := run_contextField (contextFieldEffect s) (contextField_clean s clean)
  have facts : contextFieldEffect (contextFieldEffect s) = contextTokenEffect s := by
    funext i
    by_cases a : i = fr <;> by_cases b : i = lv <;> by_cases c : i = gues <;>
      simp [contextFieldEffect,contextTokenEffect,rawFields,Store.set,a,b,c,fr,lv,gues,markedIf_and] <;>
      rfl
  rw [facts] at second
  exact then_normal first second

def contextResult (n : Nat) (reverse : Bool) (s : Store) : Store :=
  let (ok,x,y) := prefixSummary n (s fr) (s lv)
  (((s.set goal 0).set fr (if reverse then y else x)).set lv (if reverse then x else y)).set gues
    (markedIf (s gues) (ok = true))

/-- The packed selector stores twice the context length plus the side
bit. At each pass two decrements pay for one actual token comparison. -/
theorem run_context (n : Nat) (reverse : Bool) (s : Store) (clean : Scratch s)
    (code : s goal = 2*n + reverse.toNat) :
    Executes contextScan s .normal (contextResult n reverse s) := by
  induction n generalizing s with
  | zero =>
    cases reverse with
    | false =>
      have stop : s goal = 0 := by simpa using code
      have result : contextResult 0 false s = s := by
        simp only [contextResult,prefixSummary,markedIf,Bool.false_eq_true,↓reduceIte,← stop,Store.set_same]
      rw [result]
      exact .leftExit (dec_zero stop) rfl
    | true =>
      have one : s goal = 1 := by simpa using code
      let middle := s.set goal 0
      have step := dec_pos (s := s) (r := goal) (by omega)
      have move : Executes (dec goal) s .normal middle := by
        simpa only [one,Nat.reduceSub,middle] using step
      have stop : middle goal = 0 := Store.get_set _ _ _
      have swap := run_exchange middle (by simpa [middle,Store.set,goal,u] using clean.auxiliaryEmpty)
      have eq : (middle.set fr (middle lv)).set lv (middle fr) = contextResult 0 true s := by
        funext i
        by_cases x : i = fr <;> by_cases y : i = lv <;> by_cases z : i = gues <;>
          simp [middle,contextResult,prefixSummary,Store.set,fr,lv,goal,gues,markedIf,x,y,z]
      rw [eq] at swap
      exact .rightExit move (then_normal (.leftExit (dec_zero stop) rfl) swap) rfl
  | succ n ih =>
    let one := s.set goal (s goal-1)
    let two := s.set goal (2*n+reverse.toNat)
    let after := contextTokenEffect two
    have next : one goal = s goal-1 := Store.get_set _ _ _
    have value : one.set goal (one goal-1) = two := by
      simp only [two,next,one,Store.set_set]
      congr 1
      omega
    have clean₂ : Scratch two := ⟨
      by simpa [two,Store.set,goal,expected] using clean.expectedEmpty,
      by simpa [two,Store.set,goal,tok] using clean.tokenEmpty,
      by simpa [two,Store.set,goal,u] using clean.auxiliaryEmpty⟩
    have step₁ : Executes (dec goal) s .normal one := dec_pos (by omega)
    have step₂ := dec_pos (s := one) (r := goal) (by omega)
    rw [value] at step₂
    have token := run_contextToken two clean₂
    have recur := run_continue 2 after
    have back : Executes
        (.seq (.seq (dec goal) (.seq (.seq contextField contextField) (continue_ 2))) exchange)
        one (.repeatAt 0) after :=
      .leftExit (.rightExit step₂ (.rightExit token recur rfl) rfl) rfl
    have afterClean : Scratch after := by
      refine ⟨?_,?_,?_⟩ <;>
        simp [after,contextTokenEffect,two,Store.set,fr,lv,gues,goal,expected,tok,u,
          clean.expectedEmpty,clean.tokenEmpty,clean.auxiliaryEmpty]
    have code' : after goal = 2*n+reverse.toNat := by
      simp [after,contextTokenEffect,two,Store.set,goal,fr,lv,gues]
    have finish := ih after afterClean code'
    have output : contextResult n reverse after = contextResult (n+1) reverse s := by
      funext i
      cases reverse <;> by_cases a : i = fr <;> by_cases b : i = lv <;>
        by_cases c : i = goal <;> by_cases d : i = gues <;>
        simp [contextResult,prefixSummary,after,contextTokenEffect,two,Store.set,a,b,c,d,fr,lv,goal,gues,
          markedIf_and, Bool.and_eq_true, beq_iff_eq, and_assoc] <;> rfl
    rw [output] at finish
    exact .reenter step₁ back finish

end PalomarI3334.SearchProgram
