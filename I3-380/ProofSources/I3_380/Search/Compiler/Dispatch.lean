module
public import I3_380.Search.Compiler.Dictionary
@[expose] public section

namespace PalomarI3380.Compiler.Source

/-- Saturating dispatch. A selector above the final index arrives at
the final branch with a nonzero residual in the selector register. -/
def selectBranch {α : Type} : List α → Nat → Option (α × Nat)
  | [], _ => none
  | [p], n => some (p, n)
  | p :: _ :: _, 0 => some (p, 0)
  | _ :: q :: qs, n + 1 => selectBranch (q :: qs) n

theorem selectBranch_exists {α : Type} (ps : List α) (n : Nat) (hn : ps ≠ []) :
    ∃ p r, selectBranch ps n = some (p, r) := by
  induction ps generalizing n with
  | nil => exact (hn rfl).elim
  | cons p ps ih =>
    cases ps with
    | nil => exact ⟨p, n, rfl⟩
    | cons q qs =>
      cases n with
      | zero => exact ⟨p, 0, rfl⟩
      | succ n => exact ih n (by simp)

theorem selectBranch_mem {α : Type} {ps : List α} {n : Nat} {p : α} {r : Nat}
    (chosen : selectBranch ps n = some (p, r)) : p ∈ ps := by
  induction ps generalizing n with
  | nil => simp [selectBranch] at chosen
  | cons h rest ih =>
    cases rest with
    | nil => simp_all [selectBranch]
    | cons g gs =>
      cases n with
      | zero => simp_all [selectBranch]
      | succ n => exact List.mem_cons_of_mem _ (ih chosen)

theorem selectBranch_map {α β : Type} (f : α → β) (ps : List α) (n : Nat) :
    selectBranch (ps.map f) n =
      (selectBranch ps n).map (fun (p, r) => (f p, r)) := by
  induction ps generalizing n with
  | nil => rfl
  | cons p ps ih =>
    cases ps with
    | nil => rfl
    | cons q qs => cases n <;> first | rfl | exact ih _

theorem selectBranch_exact {α : Type} (ps : List α) (n : Nat) (hn : n < ps.length) :
    selectBranch ps n = some (ps[n], 0) := by
  induction ps generalizing n with
  | nil => simp at hn
  | cons p ps ih =>
    cases ps with
    | nil =>
      have eq : n = 0 := by simpa using hn
      subst n
      rfl
    | cons q qs =>
      cases n with
      | zero => rfl
      | succ n => exact ih n (by simpa using hn)

theorem run_dispatch (ps : List Program) (s : Store) {p : Program} {r : Nat} {t : Store}
    (selEq : selectBranch ps (s sel) = some (p, r))
    (run : Executes p (s.set sel r) .normal t) :
    Executes (dispatch ps) s .normal t := by
  induction ps generalizing s t p r with
  | nil => simp [selectBranch] at selEq
  | cons head ps ih =>
    cases ps with
    | nil =>
      simp only [selectBranch, Option.some.injEq, Prod.mk.injEq] at selEq
      obtain ⟨rfl, rfl⟩ := selEq
      rw [Store.set_same] at run
      exact run
    | cons next rest =>
      cases value : s sel with
      | zero =>
        simp only [value, selectBranch, Option.some.injEq, Prod.mk.injEq] at selEq
        obtain ⟨rfl, rfl⟩ := selEq
        rw [← value, Store.set_same] at run
        exact then_normal (.leftExit (dec_zero value) rfl) run
      | succ n =>
        let state := s.set sel (s sel - 1)
        have hState : state sel = n := by simp [state, value]
        have selected : selectBranch (next :: rest) (state sel) = some (p, r) := by
          rw [hState]
          simpa only [value, selectBranch] using selEq
        have branch : Executes p (state.set sel r) .normal t := by
          simpa only [state, Store.set_set] using run
        have restRun := ih state selected branch
        exact .leftExit (.rightExit (dec_pos (by omega))
          (.rightExit restRun (run_break 0 _) rfl) rfl) rfl

def Pattern.effect (p : Pattern) (s : Store) : Store :=
  match p with
  | .variable index => dictionaryEffect s index
  | .literal token => tokenEffect s token
  | .side => (s.set fr (s lv)).set lv (s fr)

theorem Pattern.run (p : Pattern) (s : Store) (ready : ClearScratch s) :
    Executes p.compile s .normal (p.effect s) := by
  cases p with
  | «variable» i => exact run_scan s i ready
  | literal t => exact run_eatLiteral s t ready.expZero ready.tokZero ready.auxZero
  | side => exact run_side s ready.tempZero

theorem Pattern.frame (p : Pattern) (s : Store) (r : Register)
    (f : r ≠ fr) (l : r ≠ lv) (g : r ≠ gues) : p.effect s r = s r := by
  cases p <;> simp [Pattern.effect, dictionaryEffect, tokenEffect, Store.set, f, l, g]

theorem Pattern.ready (p : Pattern) {s : Store} (ready : ClearScratch s) : ClearScratch (p.effect s) where
  expZero := (p.frame s exp (by decide) (by decide) (by decide)).trans ready.expZero
  tokZero := (p.frame s tok (by decide) (by decide) (by decide)).trans ready.tokZero
  auxZero := (p.frame s u (by decide) (by decide) (by decide)).trans ready.auxZero
  tempZero := (p.frame s tmp (by decide) (by decide) (by decide)).trans ready.tempZero
  goalZero := (p.frame s goal (by decide) (by decide) (by decide)).trans ready.goalZero

theorem ClearScratch.setPL {V : Type} [OfNat V 0] {s : Store V} (ready : ClearScratch s) (n : V) : ClearScratch (s.set pl n) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := ready
  exact ⟨by simpa [Store.set, exp, pl] using h₁, by simpa [Store.set, tok, pl] using h₂,
    by simpa [Store.set, u, pl] using h₃, by simpa [Store.set, tmp, pl] using h₄,
    by simpa [Store.set, goal, pl] using h₅⟩

theorem ClearScratch.setSel {V : Type} [OfNat V 0] {s : Store V} (ready : ClearScratch s) (n : V) : ClearScratch (s.set sel n) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := ready
  exact ⟨by simpa [Store.set, exp, sel] using h₁, by simpa [Store.set, tok, sel] using h₂,
    by simpa [Store.set, u, sel] using h₃, by simpa [Store.set, tmp, sel] using h₄,
    by simpa [Store.set, goal, sel] using h₅⟩

def runPattern : List Pattern → Store → Store
  | [], s => s
  | p :: ps, s => runPattern ps (p.effect s)

theorem runPattern_compiled (ps : List Pattern) (s : Store) (h : ClearScratch s) :
    LineRuns (ps.map Pattern.compile) s (runPattern ps s) := by
  induction ps generalizing s with
  | nil => exact .nil
  | cons p ps ih => exact .cons (p.run s h) (ih _ (p.ready h))

theorem runPattern_append (xs ys : List Pattern) (s : Store) :
    runPattern (xs ++ ys) s = runPattern ys (runPattern xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (x.effect s)

/-- Control fields commute with word matching. The matcher only reads
the two words and the dictionary, and updates those words and the marker. -/
theorem Pattern.set_control (p : Pattern) (s : Store) (r : Register) (v : Nat)
    (f : r ≠ fr) (l : r ≠ lv) (g : r ≠ gues) (d : r ≠ dc) :
    p.effect (s.set r v) = (p.effect s).set r v := by
  cases p with
  | «variable» i =>
    simp only [Pattern.effect, dictionaryEffect, Store.get_set_other _ _ _ _ d.symm,
      Store.get_set_other _ _ _ _ f.symm, Store.get_set_other _ _ _ _ g.symm, mark]
    rw [Store.set_comm s f, Store.set_comm (s.set fr _) g]
  | literal t =>
    simp only [Pattern.effect, tokenEffect, Store.get_set_other _ _ _ _ f.symm,
      Store.get_set_other _ _ _ _ g.symm, mark]
    rw [Store.set_comm s f, Store.set_comm (s.set fr _) g]
  | side =>
    simp only [Pattern.effect, Store.get_set_other _ _ _ _ f.symm, Store.get_set_other _ _ _ _ l.symm]
    rw [Store.set_comm s f, Store.set_comm (s.set fr _) l]

theorem runPattern_control (ps : List Pattern) (s : Store) (r : Register) (v : Nat)
    (f : r ≠ fr) (l : r ≠ lv) (g : r ≠ gues) (d : r ≠ dc) :
    runPattern ps (s.set r v) = (runPattern ps s).set r v := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simp only [runPattern, Pattern.set_control p s r v f l g d, ih]

end PalomarI3380.Compiler.Source
