module
public import I3_380.Search.Compiler.ScanExecution
public import I3_380.Search.RewriteVerifier
@[expose] public section

namespace PalomarI3380.Compiler.Source

def dictionaryTail : Nat → Nat → Nat
  | 0, code => code
  | n + 1, code => dictionaryTail n (Cantor.unpair code).2

def coordinate (code : Nat) (index : Fin 3) : Nat :=
  (Cantor.unpair (dictionaryTail index.val code)).1

def encodeDictionary (entries : Fin 3 → Nat) : Nat :=
  Cantor.pair (entries 0) (Cantor.pair (entries 1) (Cantor.pair (entries 2) 0))

theorem coordinate_encode (entries : Fin 3 → Nat) (index : Fin 3) :
    coordinate (encodeDictionary entries) index = entries index := by
  have bound := index.isLt
  have which : index = 0 ∨ index = 1 ∨ index = 2 := by
    rcases (show index.val = 0 ∨ index.val = 1 ∨ index.val = 2 by omega) with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  rcases which with rfl | rfl | rfl <;> simp [coordinate, encodeDictionary, dictionaryTail, Cantor.unpair_pair]

private theorem finish_field (s : Store) {keep discard : Register}
    (keepTmp : keep ≠ tmp) (discardTmp : discard ≠ tmp) (keepDisc : keep ≠ discard)
    (keepZero : s keep = 0) (discZero : s discard = 0) (x y : Nat) :
    Executes (.seq (clear discard) (move keep tmp))
      (((s.set tmp 0).set keep x).set discard y) .normal (s.set tmp x) := by
  let first := ((s.set tmp 0).set keep x).set discard y
  let middle := first.set discard 0
  have clearRun : Executes (clear discard) first .normal middle := run_clear discard first
  have moveRun := run_move keepTmp middle
  have value : middle keep = x := by simp [middle, first, Store.set, keepDisc]
  have dest : middle tmp = 0 := by simp [middle, first, Store.set, keepTmp.symm, discardTmp.symm]
  rw [value, dest, Nat.zero_add] at moveRun
  have state : (middle.set keep 0).set tmp x = s.set tmp x := by
    funext i
    by_cases h₁ : i = tmp <;> by_cases h₂ : i = keep <;> by_cases h₃ : i = discard <;>
      simp [middle, first, Store.set, h₁, h₂, h₃, keepTmp, discardTmp,
        keepZero, discZero]
  rw [state] at moveRun
  exact then_normal clearRun moveRun

theorem run_dropField (s : Store) (e : s exp = 0) (a : s u = 0) :
    Executes dropField s .normal (s.set tmp (Cantor.unpair (s tmp)).2) := by
  let fields := Cantor.unpair (s tmp)
  have next := run_unpair (a := exp) (b := u) (input := tmp) (by decide) (by decide) (by decide) s e a
  dsimp only at next
  have rest := finish_field (keep := u) (discard := exp) s (by decide) (by decide) (by decide) a e fields.2 fields.1
  have commuted : ((s.set tmp 0).set exp fields.1).set u fields.2 =
      ((s.set tmp 0).set u fields.2).set exp fields.1 :=
    Store.set_comm _ (by decide) _ _
  exact then_normal next (commuted.symm ▸ rest)

theorem run_grabField (s : Store) (e : s exp = 0) (a : s u = 0) :
    Executes grabField s .normal (s.set tmp (Cantor.unpair (s tmp)).1) := by
  let fields := Cantor.unpair (s tmp)
  have next := run_unpair (a := exp) (b := u) (input := tmp) (by decide) (by decide) (by decide) s e a
  dsimp only at next
  have rest := finish_field (keep := exp) (discard := u) s (by decide) (by decide) (by decide) e a fields.1 fields.2
  exact then_normal next rest

theorem run_dropFields (n : Nat) (s : Store) (e : s exp = 0) (a : s u = 0) :
    LineRuns (List.replicate n dropField) s (s.set tmp (dictionaryTail n (s tmp))) := by
  induction n generalizing s with
  | zero =>
    rw [dictionaryTail, Store.set_same]
    exact .nil
  | succ n ih =>
    let next := s.set tmp (Cantor.unpair (s tmp)).2
    have eNext : next exp = 0 := by simpa [next, Store.set, exp, tmp] using e
    have aNext : next u = 0 := by simpa [next, Store.set, u, tmp] using a
    have rest := ih next eNext aNext
    change LineRuns _ next ((s.set tmp _).set tmp (dictionaryTail n (next tmp))) at rest
    rw [show next tmp = (Cantor.unpair (s tmp)).2 from Store.get_set _ _ _, Store.set_set] at rest
    exact .cons (run_dropField s e a) rest

def dictionaryEffect (s : Store) (index : Fin 3) : Store :=
  let result := scanLoop 1 (coordinate (s dc) index) (s fr)
  (s.set fr result.frontRest).set gues (mark s (result.valid = true))

set_option maxHeartbeats 4000000 in
theorem run_scan (s : Store) (index : Fin 3) (clear : ClearScratch s) :
    Executes (scan index) s .normal (dictionaryEffect s index) := by
  let copied := s.set tmp (s dc)
  have copyRun := run_copy (a := dc) (b := tmp) (by decide) (by decide) (by decide) s clear.auxZero
  rw [clear.tempZero, Nat.zero_add] at copyRun
  have cExp : copied exp = 0 := by simpa [copied, Store.set, exp, tmp] using clear.expZero
  have cAux : copied u = 0 := by simpa [copied, Store.set, u, tmp] using clear.auxZero
  have drop := run_dropFields index.val copied cExp cAux
  let remaining := dictionaryTail index.val (s dc)
  let dropped := s.set tmp remaining
  have vCopy : copied tmp = s dc := Store.get_set _ _ _
  change LineRuns _ copied ((s.set tmp _).set tmp (dictionaryTail index.val (copied tmp))) at drop
  rw [vCopy, Store.set_set] at drop
  have dExp : dropped exp = 0 := by simpa [dropped, Store.set, exp, tmp] using clear.expZero
  have dAux : dropped u = 0 := by simpa [dropped, Store.set, u, tmp] using clear.auxZero
  have grab := run_grabField dropped dExp dAux
  let code := coordinate (s dc) index
  let grabbed := s.set tmp code
  change Executes (grabField) dropped .normal ((s.set tmp _).set tmp (Cantor.unpair (dropped tmp)).1) at grab
  rw [show dropped tmp = remaining from Store.get_set _ _ _, Store.set_set] at grab
  have gGoal : grabbed goal = 0 := by simpa [grabbed, Store.set, goal, tmp] using clear.goalZero
  have incRun := run_inc goal grabbed
  rw [gGoal, Nat.zero_add] at incRun
  let start := grabbed.set goal 1
  have iE : start exp = 0 := by simpa [start, grabbed, Store.set, exp, tmp, goal] using clear.expZero
  have iT : start tok = 0 := by simpa [start, grabbed, Store.set, tok, tmp, goal] using clear.tokZero
  have iA : start u = 0 := by simpa [start, grabbed, Store.set, u, tmp, goal] using clear.auxZero
  have hNeed : start goal = 1 := Store.get_set _ _ _
  have hCode : start tmp = code := by simp [start, grabbed, Store.set, tmp, goal]
  have hFront : start fr = s fr := by simp [start, grabbed, Store.set, tmp, fr, goal]
  have hMark : start gues = s gues := by simp [start, grabbed, Store.set, tmp, gues, goal]
  let result := scanLoop 1 code (s fr)
  have loop := run_scanLoop start iE iT iA
  rw [hNeed, hCode, hFront] at loop
  let next := scanEffect start result
  have cleaning := run_clear tmp next
  have finish : next.set tmp 0 = dictionaryEffect s index := by
    funext i
    by_cases h₁ : i = (3 : Register) <;> by_cases h₂ : i = (9 : Register) <;>
      by_cases h₃ : i = (4 : Register) <;> by_cases h₄ : i = (5 : Register) <;>
      simp [next, scanEffect, dictionaryEffect, Store.set, goal, tmp, fr, gues, start, grabbed,
        mark, result, code, h₁, h₂, h₃, h₄, show s 3 = 0 from clear.goalZero,
        show s 9 = 0 from clear.tempZero] <;> rfl
  rw [finish] at cleaning
  apply LineRuns.block
  change LineRuns ([copy dc tmp] ++ List.replicate index.val dropField ++
    [grabField, inc goal, whilePositive goal scanBody, Source.clear tmp]) s (dictionaryEffect s index)
  rw [List.append_assoc]
  exact .cons copyRun (drop.append (.cons grab (.cons incRun (.cons loop (.cons cleaning .nil)))))

end PalomarI3380.Compiler.Source
