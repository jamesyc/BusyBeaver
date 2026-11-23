module
public import I3_334Support.SetTheory.Classes.LocalFormulas
@[expose] public section

namespace PalomarI3334.Disjoint

open PalomarI3380.Logic
open LocalFormula (bindValue)

variable {V W : Type} (R : V → V → Prop) (S : W → W → Prop)

/-- A disjoint sum of two binary relational structures. -/
def relation : Sum V W → Sum V W → Prop
  | .inl x, .inl y => R x y
  | .inr x, .inr y => S x y
  | _, _ => False

def assignment (side : Fin 3 → Bool) (left : Fin 3 → V) (right : Fin 3 → W) :
    Fin 3 → Sum V W :=
  fun i => if side i then .inr (right i) else .inl (left i)

abbrev tautology : LocalFormula := .equal 0 0

abbrev Pieces := List (LocalFormula × LocalFormula)

def realizes (pieces : Pieces) (left : Fin 3 → V) (right : Fin 3 → W) : Prop :=
  ∃ terms ∈ pieces, LocalFormula.eval R (fun _ => True) terms.1 left ∧ LocalFormula.eval S (fun _ => True) terms.2 right

def meet (p q : Pieces) : Pieces :=
  p.flatMap fun a => q.map fun b => (.conj a.1 b.1, .conj a.2 b.2)

def complement : Pieces → Pieces
  | [] => [(tautology, tautology)]
  | (p, q) :: rest => meet [(LocalFormula.neg p, tautology), (tautology, LocalFormula.neg q)] (complement rest)

theorem realizes_append {p q : Pieces} {l : Fin 3 → V} {r : Fin 3 → W} :
    realizes R S (p ++ q) l r ↔ realizes R S p l r ∨ realizes R S q l r := by
  simp only [realizes, List.mem_append]
  constructor
  · rintro ⟨pieces, h | h, evals⟩
    · exact Or.inl ⟨pieces, h, evals⟩
    · exact Or.inr ⟨pieces, h, evals⟩
  · rintro (⟨pieces, mem, evals⟩ | ⟨pieces, mem, evals⟩)
    · exact ⟨pieces, Or.inl mem, evals⟩
    · exact ⟨pieces, Or.inr mem, evals⟩

theorem realizes_meet {p q : Pieces} {l : Fin 3 → V} {r : Fin 3 → W} :
    realizes R S (meet p q) l r ↔ realizes R S p l r ∧ realizes R S q l r := by
  constructor
  · rintro ⟨_, mem, left, right⟩
    simp only [meet, List.mem_flatMap, List.mem_map] at mem
    obtain ⟨a, ha, b, hb, rfl⟩ := mem
    exact ⟨⟨a, ha, left.1, right.1⟩, ⟨b, hb, left.2, right.2⟩⟩
  · rintro ⟨⟨a, ha, al, ar⟩, ⟨b, hb, bl, br⟩⟩
    refine ⟨(.conj a.1 b.1, .conj a.2 b.2), ?_, ⟨al, bl⟩, ⟨ar, br⟩⟩
    simp only [meet, List.mem_flatMap, List.mem_map]
    exact ⟨a, ha, b, hb, rfl⟩

private theorem realizes_cons (head : LocalFormula × LocalFormula) (tail : Pieces)
    (l : Fin 3 → V) (r : Fin 3 → W) :
    realizes R S (head :: tail) l r ↔
      (LocalFormula.eval R (fun _ => True) head.1 l ∧
        LocalFormula.eval S (fun _ => True) head.2 r) ∨ realizes R S tail l r := by
  constructor
  · rintro ⟨p, mem, h⟩
    rcases List.mem_cons.mp mem with rfl | ht
    · exact .inl h
    · exact .inr ⟨p, ht, h⟩
  · rintro (h | ⟨p, mem, h⟩)
    · exact ⟨head, List.mem_cons_self, h⟩
    · exact ⟨p, List.mem_cons_of_mem _ mem, h⟩

theorem realizes_complement (p : Pieces) (l : Fin 3 → V) (r : Fin 3 → W) :
    realizes R S (complement p) l r ↔ ¬ realizes R S p l r := by
  classical
  induction p with
  | nil => simp [complement, realizes, LocalFormula.eval]
  | cons head tail ih =>
    obtain ⟨a,b⟩ := head
    rw [complement, realizes_meet, ih, realizes_cons, realizes_cons, realizes_cons]
    simp only [realizes, List.not_mem_nil, false_and, exists_false, or_false,
      LocalFormula.eval, and_true, true_and]
    grind

private theorem bind_left (side : Fin 3 → Bool) (l : Fin 3 → V) (r : Fin 3 → W) (i : Fin 3) (x : V) :
    assignment (bindValue side i false) (bindValue l i x) r =
      bindValue (assignment side l r) i (.inl x) := by
  funext j
  by_cases h : j = i <;> simp [assignment, bindValue, h]

private theorem bind_right (side : Fin 3 → Bool) (l : Fin 3 → V) (r : Fin 3 → W) (i : Fin 3) (y : W) :
    assignment (bindValue side i true) l (bindValue r i y) =
      bindValue (assignment side l r) i (.inr y) := by
  funext j
  by_cases h : j = i <;> simp [assignment, bindValue, h]

def existsLeft (index : Fin 3) (pieces : Pieces) : Pieces :=
  pieces.map fun q => (.bind index q.1, q.2)

def existsRight (index : Fin 3) (pieces : Pieces) : Pieces :=
  pieces.map fun q => (q.1, .bind index q.2)

theorem realizes_existsLeft (i : Fin 3) (p : Pieces) (l : Fin 3 → V) (r : Fin 3 → W) :
    realizes R S (existsLeft i p) l r ↔ ∃ x, realizes R S p (bindValue l i x) r := by
  constructor
  · rintro ⟨q, mem, ex, rest⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp mem
    obtain ⟨x, _, hx⟩ := ex
    exact ⟨x, q, hq, hx, rest⟩
  · rintro ⟨x, q, mem, first, second⟩
    exact ⟨_, List.mem_map.mpr ⟨q, mem, rfl⟩, ⟨x, trivial, first⟩, second⟩

theorem realizes_existsRight (i : Fin 3) (p : Pieces) (l : Fin 3 → V) (r : Fin 3 → W) :
    realizes R S (existsRight i p) l r ↔ ∃ y, realizes R S p l (bindValue r i y) := by
  constructor
  · rintro ⟨q, mem, rest, ex⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp mem
    obtain ⟨x, _, hx⟩ := ex
    exact ⟨x, q, hq, rest, hx⟩
  · rintro ⟨y, q, mem, first, second⟩
    exact ⟨_, List.mem_map.mpr ⟨q, mem, rfl⟩, first, ⟨y, trivial, second⟩⟩

def extractAtom (p : LocalFormula) (x y : Bool) : Pieces :=
  match x,y with
  | false,false => [(p, tautology)]
  | true,true => [(tautology, p)]
  | _,_ => []

/-- A finite disjunction of pairs of formulas, one for each component. The
assignment records to which component each free variable belongs. -/
def split : LocalFormula → (Fin 3 → Bool) → Pieces
  | .member i j, s => extractAtom (.member i j) (s i) (s j)
  | .equal i j, s => extractAtom (.equal i j) (s i) (s j)
  | .conj p q, s => meet (split p s) (split q s)
  | .neg p, s => complement (split p s)
  | .bind i p, s =>
      existsLeft i (split p (bindValue s i false)) ++ existsRight i (split p (bindValue s i true))

theorem eval_split (p : LocalFormula) (s : Fin 3 → Bool) (l : Fin 3 → V) (r : Fin 3 → W) :
    LocalFormula.eval (relation R S) (fun _ => True) p (assignment s l r) ↔
      realizes R S (split p s) l r := by
  classical
  induction p generalizing s l r with
  | member i j => cases si : s i <;> cases sj : s j <;>
      simp [split, extractAtom, LocalFormula.eval, assignment, relation, realizes, si, sj]
  | equal i j => cases si : s i <;> cases sj : s j <;>
      simp [split, extractAtom, LocalFormula.eval, assignment, realizes, si, sj]
  | conj p q ip iq => simp only [LocalFormula.eval, split, realizes_meet, ip, iq]
  | neg p ih => simp only [LocalFormula.eval, split, realizes_complement, ih]
  | bind i p ih =>
    simp only [LocalFormula.eval, true_and, split, realizes_append, realizes_existsLeft,
      realizes_existsRight, ← ih, bind_left, bind_right]
    constructor
    · rintro ⟨x, hx⟩
      cases x with
      | inl x => exact .inl ⟨x, hx⟩
      | inr y => exact .inr ⟨y, hx⟩
    · intro h
      exact h.elim (fun ⟨x, hx⟩ => ⟨.inl x, hx⟩) (fun ⟨y, hy⟩ => ⟨.inr y, hy⟩)

/-- An elementary self-map on one component extends by the identity on
the other component to an elementary self-map of the full disjoint sum. -/
theorem elementary (j : V → V) (defaultLeft : V) (defaultRight : W)
    (elem : ∀ p env, LocalFormula.eval R (fun _ => True) p env ↔ LocalFormula.eval R (fun _ => True) p (j ∘ env))
    (p : LocalFormula) (env : Fin 3 → Sum V W) :
    LocalFormula.eval (relation R S) (fun _ => True) p env ↔ LocalFormula.eval (relation R S) (fun _ => True) p (Sum.map j id ∘ env) := by
  let l : Fin 3 → V := fun i => (env i).elim id (fun _ => defaultLeft)
  let r : Fin 3 → W := fun i => (env i).elim (fun _ => defaultRight) id
  let s : Fin 3 → Bool := fun i => (env i).elim (fun _ => false) (fun _ => true)
  have h : assignment s l r = env := by
    funext i
    cases hi : env i <;> simp [assignment, s, l, r, hi]
  have hj : assignment s (j ∘ l) r = Sum.map j id ∘ env := by
    funext i
    cases hi : env i <;> simp [assignment, s, l, r, hi]
  calc
    _ ↔ realizes R S (split p s) l r := h ▸ eval_split R S p s l r
    _ ↔ realizes R S (split p s) (j ∘ l) r :=
      ⟨fun ⟨q, hq, first, second⟩ => ⟨q, hq, (elem _ _).mp first, second⟩,
        fun ⟨q, hq, first, second⟩ => ⟨q, hq, (elem _ _).mpr first, second⟩⟩
    _ ↔ _ := hj ▸ (eval_split R S p s (j ∘ l) r).symm

end PalomarI3334.Disjoint
