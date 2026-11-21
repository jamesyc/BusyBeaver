module
public import I3_380.Search.Compiler.MatchFields
@[expose] public section

namespace PalomarI3380.Compiler.Source

def mark {V : Type} [OfNat V 0] (s : Store V) (condition : Prop) [Decidable condition] : V :=
  if condition then s gues else 0

theorem mark_compose (s : Store) (a b : Prop) [Decidable a] [Decidable b] :
    (if b then mark s a else 0) = mark s (a ∧ b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp [mark, ha, hb]

def eatField (s : Store) (expected : Nat) : Store :=
  let actual := Cantor.unpair (s fr)
  (s.set fr actual.2).set gues (mark s (expected = actual.1))

theorem run_eat_expected (s : Store) (n : Nat) (clearExp : s exp = 0)
    (clearToken : s tok = 0) (clearAux : s u = 0) :
    LineRuns (List.replicate n (inc exp) ++ [eat]) s (eatField s n) := by
  have increments := run_increments exp n s
  rw [clearExp, Nat.zero_add] at increments
  let mid := s.set exp n
  have token : mid tok = 0 :=
    (Store.get_set_other _ _ _ _ (by decide : tok ≠ exp)).trans clearToken
  have aux : mid u = 0 :=
    (Store.get_set_other _ _ _ _ (by decide : u ≠ exp)).trans clearAux
  have eating := run_eat mid token aux
  dsimp only at eating
  have front : mid fr = s fr := Store.get_set_other _ _ _ _ (by decide : fr ≠ exp)
  have marker : mid gues = s gues := Store.get_set_other _ _ _ _ (by decide : gues ≠ exp)
  simp only [front, marker, show mid exp = n from Store.get_set _ _ _] at eating
  have stateEq : (mid.set fr (Cantor.unpair (s fr)).2).set exp 0 =
      s.set fr (Cantor.unpair (s fr)).2 := by
    change ((s.set exp n).set fr _).set exp 0 = _
    rw [Store.set_comm s (by decide : exp ≠ fr), Store.set_set,
      Store.set_comm s (by decide : fr ≠ exp), ← clearExp, Store.set_same]
  rw [stateEq] at eating
  exact increments.append (.cons eating .nil)

def tokenEffect (s : Store) (token : Token) : Store :=
  let fields := rawFields (s fr)
  (s.set fr fields.rest).set gues
    (mark s (token.arity + 1 = fields.arityField ∧ token.tag = fields.tag))

theorem run_eatLiteral (s : Store) (t : Token) (clearExp : s exp = 0)
    (clearTok : s tok = 0) (clearAux : s u = 0) :
    Executes (eatLiteral t) s .normal (tokenEffect s t) := by
  have first := run_eat_expected s (t.arity + 1) clearExp clearTok clearAux
  let next := eatField s (t.arity + 1)
  have expNext : next exp = 0 := by simpa [next, eatField, Store.set, exp, fr, gues] using clearExp
  have tokNext : next tok = 0 := by simpa [next, eatField, Store.set, tok, fr, gues] using clearTok
  have auxNext : next u = 0 := by simpa [next, eatField, Store.set, u, fr, gues] using clearAux
  have second := run_eat_expected next t.tag expNext tokNext auxNext
  have composed := (first.append second).block
  rw [List.append_assoc] at composed
  have value : eatField next t.tag = tokenEffect s t := by
    let h := Cantor.unpair (s fr)
    let k := Cantor.unpair h.2
    have hFront : next fr = h.2 := by simp [next, eatField, Store.set, h, fr, gues]
    have hCurrent : next gues = mark s (t.arity + 1 = h.1) := Store.get_set _ _ _
    change (next.set fr (Cantor.unpair (next fr)).2).set gues
      (mark next (t.tag = (Cantor.unpair (next fr)).1)) = _
    rw [hFront]
    have marked : mark next (t.tag = k.1) = mark s (t.arity + 1 = h.1 ∧ t.tag = k.1) := by
      unfold mark
      rw [hCurrent]
      exact mark_compose s _ _
    change (next.set fr k.2).set gues (mark next (t.tag = k.1)) = _
    rw [marked]
    change (((s.set fr h.2).set gues _).set fr k.2).set gues _ = (s.set fr k.2).set gues _
    rw [Store.set_comm (s.set fr h.2) (by decide : gues ≠ fr), Store.set_set, Store.set_set]
    rfl
  rw [value] at composed
  simpa only [eatLiteral, ← List.append_assoc] using composed

def contextFieldEffect (s : Store) : Store :=
  let a := Cantor.unpair (s lv)
  let b := Cantor.unpair (s fr)
  ((s.set lv a.2).set fr b.2).set gues (mark s (a.1 = b.1))

theorem run_contextField (s : Store) (clearExp : s exp = 0) (clearTok : s tok = 0) (clearAux : s u = 0) :
    Executes contextField s .normal (contextFieldEffect s) := by
  let a := Cantor.unpair (s lv)
  let b := Cantor.unpair (s fr)
  let mid := (s.set lv a.2).set exp a.1
  have h₁ : Executes (pop lv exp) s .normal mid :=
    run_pop (by decide) (by decide) (by decide) s clearExp clearAux
  have tokMid : mid tok = 0 := by simpa [mid, Store.set, lv, exp, tok] using clearTok
  have auxMid : mid u = 0 := by simpa [mid, Store.set, lv, exp, u] using clearAux
  have h₂ := run_eat mid tokMid auxMid
  dsimp only at h₂
  have hp : mid exp = a.1 := Store.get_set _ _ _
  have hFront : mid fr = s fr := by simp [mid, Store.set, lv, exp, fr]
  have hMark : mid gues = s gues := by simp [mid, Store.set, lv, exp, gues]
  rw [hp, hFront, hMark] at h₂
  have final :
      ((mid.set fr b.2).set exp 0).set gues (mark s (a.1 = b.1)) = contextFieldEffect s := by
    change ((((s.set lv a.2).set exp a.1).set fr b.2).set exp 0).set gues _ = _
    rw [Store.set_comm (s.set lv a.2) (by decide : exp ≠ fr), Store.set_set]
    have reset : ((s.set lv a.2).set fr b.2).set exp 0 = (s.set lv a.2).set fr b.2 := by
      have clear : (s.set lv a.2).set fr b.2 exp = 0 := by
        simpa [Store.set, lv, fr, exp] using clearExp
      simpa only [clear] using Store.set_same ((s.set lv a.2).set fr b.2) exp
    rw [reset]
    rfl
  change Executes eat mid .normal (((mid.set fr b.2).set exp 0).set gues (mark s (a.1 = b.1))) at h₂
  rw [final] at h₂
  exact then_normal h₁ h₂

end PalomarI3380.Compiler.Source
