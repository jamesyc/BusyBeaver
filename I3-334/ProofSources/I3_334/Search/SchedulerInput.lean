module
public import I3_334.Search.PackedContext
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (inc move clear dec LineRuns run_clear run_inc run_increments
  then_normal whilePositive whilePositive_zero whilePositive_pos ifZero_zero_normal ifZero_pos)

structure Scheduler (V : Type := Nat) where
  index : V
  pending : V
  incumbent : V
  scratchWord : V

def Scheduler.store {V : Type} [OfNat V 0] (s : Scheduler V) : Store V :=
  let initial : Store V := fun _ => 0
  (((initial.set np s.index).set pl s.pending).set fr s.incumbent).set tmp s.scratchWord

def Scheduler.initial : Scheduler := ⟨0,0,0,0⟩

theorem Scheduler.store_initial : Scheduler.initial.store = fun _ => 0 := by
  simp [Scheduler.initial,Scheduler.store,Store.set_same]

def Scheduler.begin {V : Type} [OfNat V 0] [OfNat V 1] [OfNat V 4]
    [DecidableEq V] [Add V] [Sub V] (s : Scheduler V) : Scheduler V :=
  if s.pending = 0 then ⟨s.index+1,s.index,4,s.scratchWord⟩
  else ⟨s.index,s.pending-1,s.incumbent,s.scratchWord⟩

def Scheduler.scratch (s : Scheduler) : Scratch s.store := by
  refine ⟨?_,?_,?_⟩ <;> simp [Scheduler.store,Store.set,np,pl,fr,tmp,expected,tok,u]

theorem run_restart (s : Scheduler) (empty : s.pending = 0) :
    Executes restart s.store .normal (Scheduler.mk (s.index+1) s.index 4 s.scratchWord).store := by
  let copied := s.store.set pl (s.store pl + s.store np)
  let advanced := copied.set np (copied np + 1)
  let cleared := advanced.set fr 0
  have first : Executes (copy np pl) s.store .normal copied :=
    run_copy (by decide) (by decide) (by decide) s.store s.scratch.auxiliaryEmpty
  have sequence : LineRuns [copy np pl, inc np, clear fr] s.store cleared :=
    .cons first (.cons (run_inc np copied) (.cons (run_clear fr advanced) .nil))
  have raised := run_increments fr 4 cleared
  have result : cleared.set fr (cleared fr+4) =
      (Scheduler.mk (s.index+1) s.index 4 s.scratchWord).store := by
    funext r
    by_cases a : r = np <;> by_cases b : r = pl <;> by_cases c : r = fr <;>
      by_cases d : r = tmp <;>
      simp [cleared,advanced,copied,Scheduler.store,Store.set,a,b,c,d,np,pl,fr,tmp,empty]
  rw [result] at raised
  exact (sequence.append raised).block

theorem run_begin (s : Scheduler) :
    Executes (Source.ifZero pl restart) s.store .normal s.begin.store := by
  have queue : s.store pl = s.pending := by simp [Scheduler.store,Store.set,pl,tmp,fr,np]
  by_cases empty : s.pending = 0
  · simpa only [Scheduler.begin,empty,↓reduceIte] using
      ifZero_zero_normal (queue.trans empty) (run_restart s empty)
  · have run := ifZero_pos (s := s.store) (r := pl) (body := restart) (by rwa [queue])
    have out : s.store.set pl (s.store pl-1) = s.begin.store := by
      funext r
      by_cases a : r = np <;> by_cases b : r = pl <;> by_cases c : r = fr <;>
        by_cases d : r = tmp <;> simp [Scheduler.begin,empty,Scheduler.store,Store.set,
          a,b,c,d,np,pl,fr,tmp,queue]
    rwa [out] at run

/-- The producer clones a positive proposal into both the candidate
marker and its actual term front, with no scratch value left over. -/
theorem run_fill_proposal (s : Store) :
    Executes (whilePositive tok (.seq (inc gues) (inc lv))) s .normal
      (((s.set tok 0).set gues (s gues+s tok)).set lv (s lv+s tok)) := by
  generalize input : s tok = n
  induction n generalizing s with
  | zero =>
    simp only [Nat.add_zero]
    rw [← input,Store.set_same,Store.set_same,Store.set_same]
    exact whilePositive_zero input
  | succ n ih =>
    let w := s.set tok n
    let after := (w.set gues (s gues+1)).set lv (s lv+1)
    have decEq : s.set tok (s tok-1) = w := by simp [w,input]
    have first : Executes (.seq (inc gues) (inc lv)) (s.set tok (s tok-1)) .normal after := by
      have g := run_inc gues w
      have l := run_inc lv (w.set gues (s gues+1))
      have value : w gues = s gues := by simp [w,Store.set,tok,gues]
      have other : ((w.set gues (s gues+1)) lv) = s lv := by simp [w,Store.set,tok,gues,lv]
      rw [value] at g
      rw [other] at l
      rw [decEq]
      exact then_normal g l
    have decreased : after tok = n := by simp [after,w,Store.set,tok,gues,lv]
    have rest := ih after decreased
    have result : (((after.set tok 0).set gues (after gues+n)).set lv (after lv+n)) =
        (((s.set tok 0).set gues (s gues+(n+1))).set lv (s lv+(n+1))) := by
      funext r
      by_cases a : r = tok <;> by_cases b : r = lv <;> by_cases c : r = gues <;>
        simp [after,w,Store.set,a,b,c,tok,lv,gues] <;> omega
    rw [result] at rest
    exact whilePositive_pos (by omega) first rest

def produceEffect (s : Store) : Store :=
  let fields := Cantor.unpair (s pl)
  ((s.set pl fields.2).set gues fields.1).set lv fields.1

theorem run_produce (s : Store) (clean : Scratch s) (zeroGuess : s gues = 0) (zeroBack : s lv = 0) :
    Executes produce s .normal (produceEffect s) := by
  let fields := Cantor.unpair (s pl)
  let middle := (s.set pl fields.2).set tok fields.1
  have read : Executes (pop pl tok) s .normal middle :=
    run_pop (by decide) (by decide) (by decide) s clean.tokenEmpty clean.auxiliaryEmpty
  have rest := run_fill_proposal middle
  have same : (((middle.set tok 0).set gues (middle gues + middle tok)).set lv (middle lv+middle tok)) =
      produceEffect s := by
    funext i
    by_cases a : i = pl <;> by_cases b : i = tok <;> by_cases c : i = gues <;>
      by_cases d : i = lv <;>
      simp [produceEffect,middle,fields,Store.set,a,b,c,d,pl,tok,gues,lv,zeroGuess,zeroBack,clean.tokenEmpty]
  rw [same] at rest
  exact then_normal read rest

end PalomarI3334.SearchProgram
