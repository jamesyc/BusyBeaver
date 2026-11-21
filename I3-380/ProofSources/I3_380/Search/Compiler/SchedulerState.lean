module
public import I3_380.Search.Compiler.MatchEquation
public import I3_380.Search.Compiler.ContextScan
@[expose] public section

namespace PalomarI3380.Compiler.Source

structure SchedulerState (V : Type := Nat) where
  nextWord : V
  pending : V
  current : V
  deriving DecidableEq

def emptyStore {V : Type} [OfNat V 0] : Store V := fun _ => 0

def SchedulerState.store {V : Type} [OfNat V 0] (s : SchedulerState V) : Store V :=
  ((emptyStore.set np s.nextWord).set pl s.pending).set goal s.current

theorem SchedulerState.store_initial : (SchedulerState.mk 0 0 0).store = fun _ => 0 := by
  unfold SchedulerState.store
  exact (Store.set_same ((emptyStore.set np 0).set pl 0) goal).trans
    ((Store.set_same (emptyStore.set np 0) pl).trans (Store.set_same _ np))

def SchedulerState.begin {V : Type} [DecidableEq V] [OfNat V 0] [OfNat V 1] [OfNat V 4]
    [Add V] [Sub V] (s : SchedulerState V) : SchedulerState V :=
  if s.pending = 0 then ⟨s.nextWord + 1, s.nextWord, 4⟩
  else ⟨s.nextWord, s.pending - 1, s.current⟩

theorem run_resetTask (s : Store) (tmpZ : s u = 0) (pendingZ : s pl = 0) :
    Executes resetTask s .normal (((s.set pl (s np)).set np (s np + 1)).set goal 4) := by
  let first := s.set pl (s np)
  have h₁ := run_copy (a := np) (b := pl) (by decide) (by decide) (by decide) s tmpZ
  rw [pendingZ, Nat.zero_add] at h₁
  let second := first.set np (s np + 1)
  have h₂ := run_inc np first
  rw [show first np = s np from Store.get_set_other _ _ _ _ (by decide)] at h₂
  let mid := second.set goal 0
  have h₃ := run_clear goal second
  have h₄ := (run_increments goal 4 mid).block
  rw [show mid goal = 0 from Store.get_set _ _ _, Nat.zero_add] at h₄
  change Executes (block (List.replicate 4 (inc goal))) mid .normal
    ((second.set goal 0).set goal 4) at h₄
  rw [Store.set_set] at h₄
  exact then_normal h₁ (then_normal h₂ (then_normal h₃ h₄))

theorem SchedulerState.begin_runs (s : SchedulerState) :
    Executes (ifZero pl resetTask) s.store .normal s.begin.store := by
  have hPL : s.store pl = s.pending := by simp [SchedulerState.store, Store.set, pl, goal]
  by_cases h : s.pending = 0
  · have pending := hPL.trans h
    have aux : s.store u = 0 := by simp [SchedulerState.store, emptyStore, Store.set, np, pl, goal, u]
    have reset := run_resetTask s.store aux pending
    have index : s.store np = s.nextWord := by
      simp [SchedulerState.store, Store.set, np, pl, goal]
    rw [index] at reset
    have state : (((s.store.set pl s.nextWord).set np (s.nextWord + 1)).set goal 4) = s.begin.store := by
      funext i
      by_cases h₁ : i = (0 : Register) <;> by_cases h₂ : i = (1 : Register) <;>
        by_cases h₃ : i = (3 : Register) <;>
        simp [SchedulerState.store, emptyStore, SchedulerState.begin, Store.set, h, np, pl, goal, h₁, h₂, h₃]
    rw [state] at reset
    exact ifZero_zero_normal pending reset
  · have run := ifZero_pos (r := pl) (body := resetTask) (s := s.store) (by rwa [hPL])
    rw [hPL] at run
    have state : s.store.set pl (s.pending - 1) = s.begin.store := by
      simp only [SchedulerState.begin, h, ↓reduceIte, SchedulerState.store]
      rw [Store.set_comm _ (by decide : goal ≠ pl), Store.set_set]
    rw [state] at run
    exact run

def stageStore {V : Type} [OfNat V 0] (s : SchedulerState V)
    (pending front back guess dictionary : V) : Store V :=
  ((((⟨s.nextWord, pending, 0⟩ : SchedulerState V).store.set fr front).set lv back).set gues guess).set dc dictionary

theorem stageStore_scratch {V : Type} [OfNat V 0] (s : SchedulerState V)
    (pending front back guess dictionary : V) :
    ClearScratch (stageStore s pending front back guess dictionary) := by
  constructor <;>
    simp [stageStore, emptyStore, SchedulerState.store, Store.set, np, pl, goal, fr, lv, gues, dc, exp, tok, u, tmp]

/-- The four data fields before trie branching. Selector reads are
parsed by the trie because the number of such reads varies by row. -/
structure TrialInput (V : Type := Nat) where
  proposal : V
  position : V
  orientation : V
  dictionary : V
  pending : V
  deriving DecidableEq

def TrialInput.decode (word : Nat) : TrialInput :=
  let g := Cantor.unpair word
  let p := Cantor.unpair g.2
  let o := Cantor.unpair p.2
  let d := Cantor.unpair o.2
  ⟨g.1, p.1, o.1, d.1, d.2⟩

def TrialInput.encode (c : TrialInput) : Nat :=
  encodeFields [c.proposal, c.position, c.orientation, c.dictionary] c.pending

theorem TrialInput.decode_encode (c : TrialInput) : decode c.encode = c := by
  cases c
  simp only [decode, encode, encodeFields, Cantor.unpair_pair]

def TrialInput.prefix (c : TrialInput) (current : Nat) : Bool × (Nat × Nat) :=
  prefixSummary c.position current c.proposal

def TrialInput.prepare (c : TrialInput) (s : SchedulerState) : Store :=
  let trial := c.prefix s.current
  let (x, y) := if c.orientation = 0 then trial.2 else (trial.2.2, trial.2.1)
  stageStore s c.pending x y (if trial.1 then c.proposal else 0) c.dictionary

theorem TrialInput.prepare_scratch (c : TrialInput) (s : SchedulerState) :
    ClearScratch (c.prepare s) := by
  unfold prepare
  split <;> apply stageStore_scratch

theorem TrialInput.prepare_selector (c : TrialInput) (s : SchedulerState) : c.prepare s sel = 0 := by
  unfold prepare
  split <;> simp [stageStore, emptyStore, SchedulerState.store, Store.set, sel, np, pl, goal, fr, lv, gues, dc]

theorem store_ext {V : Type} (s t : Store V)
    (h0 : s 0 = t 0) (h1 : s 1 = t 1) (h2 : s 2 = t 2) (h3 : s 3 = t 3)
    (h4 : s 4 = t 4) (h5 : s 5 = t 5) (h6 : s 6 = t 6) (h7 : s 7 = t 7)
    (h8 : s 8 = t 8) (h9 : s 9 = t 9) (h10 : s 10 = t 10) (h11 : s 11 = t 11) : s = t := by
  funext i
  have b := i.isLt
  rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨
      i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨
      i.val = 9 ∨ i.val = 10 ∨ i.val = 11 by omega) with
    h | h | h | h | h | h | h | h | h | h | h | h
  · exact (show (0 : Register) = i from (show i = (0 : Register) from Fin.ext h).symm) ▸ h0
  · exact (show (1 : Register) = i from (show i = (1 : Register) from Fin.ext h).symm) ▸ h1
  · exact (show (2 : Register) = i from (show i = (2 : Register) from Fin.ext h).symm) ▸ h2
  · exact (show (3 : Register) = i from (show i = (3 : Register) from Fin.ext h).symm) ▸ h3
  · exact (show (4 : Register) = i from (show i = (4 : Register) from Fin.ext h).symm) ▸ h4
  · exact (show (5 : Register) = i from (show i = (5 : Register) from Fin.ext h).symm) ▸ h5
  · exact (show (6 : Register) = i from (show i = (6 : Register) from Fin.ext h).symm) ▸ h6
  · exact (show (7 : Register) = i from (show i = (7 : Register) from Fin.ext h).symm) ▸ h7
  · exact (show (8 : Register) = i from (show i = (8 : Register) from Fin.ext h).symm) ▸ h8
  · exact (show (9 : Register) = i from (show i = (9 : Register) from Fin.ext h).symm) ▸ h9
  · exact (show (10 : Register) = i from (show i = (10 : Register) from Fin.ext h).symm) ▸ h10
  · exact (show (11 : Register) = i from (show i = (11 : Register) from Fin.ext h).symm) ▸ h11

end PalomarI3380.Compiler.Source
