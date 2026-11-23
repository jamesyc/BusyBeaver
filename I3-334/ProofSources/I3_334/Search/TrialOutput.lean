module
public import I3_334.Search.TrialInput
public import I3_334Support.Search.Compiler.Commands
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (LineRuns run_clear run_move run_inc run_halt then_normal then_halt
  ifPositive_zero ifPositive_pos_normal ifPositive_pos_halt ifZero_zero_halt ifZero_pos
  inc move clear)

def gateStore {V : Type} [OfNat V 0] (index pending marker scratchWord : V) : Store V :=
  (Scheduler.mk index pending 0 scratchWord).store.set gues marker

def finalMark {V : Type} [OfNat V 0] [DecidableEq V] (s : Store V) : V := markedIf (s gues) (s fr = s lv)

theorem run_output (s : Store) (ready : Scratch s) (unused : s 11 = 0) :
    LineRuns output s (gateStore (s np) (s pl) (finalMark s) (s tmp)) := by
  let cleared := s.set goal 0
  let withLeft := (cleared.set fr 0).set expected (s fr)
  let withRight := (withLeft.set lv 0).set tok (s lv)
  let checked := (((withRight.set tok 0).set expected 0).set gues (finalMark s))
  have shaped : Executes (move fr expected) cleared .normal withLeft := by
    have move := run_move (a := fr) (b := expected) (by decide) cleared
    simpa [cleared,withLeft,Store.set,goal,fr,expected,ready.expectedEmpty] using move
  have paired : Executes (move lv tok) withLeft .normal withRight := by
    have move := run_move (a := lv) (b := tok) (by decide) withLeft
    simpa [cleared,withLeft,withRight,Store.set,goal,fr,expected,lv,tok,ready.tokenEmpty] using move
  have compare : Executes SearchProgram.compare withRight .normal checked := by
    have compare := run_compare withRight
    simpa [checked,finalMark,markedIf,withRight,withLeft,cleared,Store.set,goal,fr,expected,lv,tok,gues]
      using compare
  have finish : checked.set dc 0 = gateStore (s np) (s pl) (finalMark s) (s tmp) := by
    funext i
    have finite : ∀ r : Register, r = np ∨ r = pl ∨ r = goal ∨ r = fr ∨ r = gues ∨
        r = lv ∨ r = dc ∨ r = u ∨ r = tmp ∨ r = tok ∨ r = expected ∨ r = 11 := by decide +kernel
    have slots := finite i
    rcases slots with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [checked,withRight,withLeft,cleared,gateStore,Scheduler.store,Store.set,
        np,pl,goal,fr,gues,lv,dc,u,tmp,tok,expected,ready.auxiliaryEmpty,unused]
  have clearDict := run_clear dc checked
  rw [finish] at clearDict
  exact .cons (run_clear goal s) (.cons shaped (.cons paired (.cons compare (.cons clearDict .nil))))

theorem run_accept_halt (index pending scratchWord : Nat) :
    Executes accept (gateStore index pending 1 scratchWord) .halt
      (Scheduler.mk index pending 0 scratchWord).store := by
  let start := gateStore index pending 1 scratchWord
  let target := (Scheduler.mk index pending 0 scratchWord).store
  have one : start gues = 1 := Store.get_set _ _ _
  have zero : target gues = 0 := by simp [target,Scheduler.store,Store.set,np,pl,fr,tmp,gues]
  have first : start.set gues (start gues-1) = target := by
    rw [one]
    change (target.set gues 1).set gues 0 = target
    rw [Store.set_set]
    simpa only [zero] using Store.set_same target gues
  have stop : Executes (Source.ifZero gues Source.halt) target .halt target :=
    ifZero_zero_halt zero (run_halt target)
  apply ifPositive_pos_halt (by omega : start gues ≠ 0)
  rw [first]
  exact then_halt_prefix stop
where
  then_halt_prefix {p q : Program} {s t : Store} (done : Executes p s .halt t) :
      Executes (.seq p q) s .halt t := .leftExit done rfl

theorem run_accept_continue (index pending marker scratchWord : Nat) (keepGoing : marker ≠ 1) :
    Executes accept (gateStore index pending marker scratchWord) .normal
      (Scheduler.mk index pending marker scratchWord).store := by
  let start := gateStore index pending marker scratchWord
  let result := (Scheduler.mk index pending marker scratchWord).store
  have value : start gues = marker := Store.get_set _ _ _
  by_cases none : marker = 0
  · have same : start = result := by
      simp only [start,result,gateStore,none]
      have guesZero : (Scheduler.mk index pending 0 scratchWord).store gues = 0 := by
        simp [Scheduler.store,Store.set,np,pl,fr,tmp,gues]
      simpa only [guesZero] using Store.set_same (Scheduler.mk index pending 0 scratchWord).store gues
    have run := ifPositive_zero
      (body := Source.block [Source.ifZero gues Source.halt,inc fr,inc fr,move gues fr])
      (value.trans none)
    change Executes accept start .normal start at run
    rw [same] at run
    change Executes accept start .normal result
    exact same.symm ▸ run
  · let after₁ := start.set gues (marker - 1)
    let after₂ := after₁.set gues (marker - 2)
    let after₃ := after₂.set fr 1
    let after₄ := after₃.set fr 2
    have one : after₁ gues = marker-1 := Store.get_set _ _ _
    have nonzero : after₁ gues ≠ 0 := by rw [one]; omega
    have test := ifZero_pos (s := after₁) (r := gues) (body := Source.halt) nonzero
    have exact₂ : after₁.set gues (after₁ gues-1) = after₂ := by
      rw [one]
      rfl
    rw [exact₂] at test
    have add₁ : Executes (inc fr) after₂ .normal after₃ := by
      have value : after₂ fr = 0 := by simp [after₂,after₁,start,gateStore,Scheduler.store,Store.set,
        np,pl,fr,gues,tmp]
      simpa only [after₃,value,Nat.zero_add] using run_inc fr after₂
    have add₂ : Executes (inc fr) after₃ .normal after₄ := by
      have value : after₃ fr = 1 := Store.get_set _ _ _
      simpa only [after₄,value,Nat.reduceAdd] using run_inc fr after₃
    have finish := run_move (a := gues) (b := fr) (by decide) after₄
    have exact₄ : (after₄.set gues 0).set fr (after₄ fr+after₄ gues) = result := by
      funext i
      by_cases a : i = np <;> by_cases b : i = pl <;> by_cases c : i = fr <;>
        by_cases d : i = gues <;> by_cases e : i = tmp <;>
        simp [after₄,after₃,after₂,after₁,start,result,gateStore,Scheduler.store,Store.set,
          a,b,c,d,e,np,pl,fr,gues,tmp] <;> omega
    rw [exact₄] at finish
    have body : Executes (Source.block [Source.ifZero gues Source.halt,inc fr,inc fr,move gues fr])
        after₁ .normal result :=
      (LineRuns.cons test (.cons add₁ (.cons add₂ (.cons finish .nil)))).block
    have positive : start gues ≠ 0 := by rwa [value]
    change Executes accept start .normal result
    exact ifPositive_pos_normal positive (by simpa only [after₁,value] using body)

end PalomarI3334.SearchProgram
