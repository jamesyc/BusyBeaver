module
public import I3_380.ActiveDomain
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic

variable {A V : Type} {M : Algebra A} {S : SquareRepresentation M V}

/-- A predicate given by a fixed first-order formula in membership and
finitely many represented relation symbols. Assignments use de Bruijn
indices, with the first two free positions reserved for image graphs. -/
def Definable (S : SquareRepresentation M V) (arity : Nat) (P : (Nat → V) → Prop) : Prop :=
  ∃ f : RelationFormula A, f.Bound arity ∧ ∀ s, RelationFormula.eval S f s ↔ P s

namespace RelationFormula

def reindex (map : Nat → Nat) : RelationFormula A → RelationFormula A
  | .bot => .bot
  | .eq x y => .eq (map x) (map y)
  | .atom r x y => .atom r (map x) (map y)
  | .and p q => .and (reindex map p) (reindex map q)
  | .or p q => .or (reindex map p) (reindex map q)
  | .imp p q => .imp (reindex map p) (reindex map q)
  | .all p => .all (reindex (lift map) p)
  | .ex p => .ex (reindex (lift map) p)

theorem reindex_bound (p : RelationFormula A) {map : Nat → Nat} {n m : Nat}
    (bounded : p.Bound n) (within : ∀ i, i < n → map i < m) : (p.reindex map).Bound m := by
  induction p generalizing map n m with
  | bot => trivial
  | eq x y | atom _ x y => exact ⟨within x bounded.1, within y bounded.2⟩
  | and p q ip iq | or p q ip iq | imp p q ip iq =>
    exact ⟨ip bounded.1 within, iq bounded.2 within⟩
  | all p ih | ex p ih =>
    apply ih bounded
    intro i inside
    cases i with
    | zero => exact Nat.zero_lt_succ _
    | succ i => exact Nat.succ_lt_succ (within i (by omega))

theorem reindex_eval (S : SquareRepresentation M V) (p : RelationFormula A)
    (map : Nat → Nat) (s : Nat → V) : eval S (p.reindex map) s ↔ eval S p (s ∘ map) := by
  have binder (s : Nat → V) (map : Nat → Nat) (x : V) :
      pushValue s x ∘ lift map = pushValue (s ∘ map) x := by
    funext i
    cases i <;> rfl
  induction p generalizing s map <;> simp only [reindex, eval, Function.comp_apply, *]

end RelationFormula

namespace Definable

variable {n : Nat} {p q : (Nat → V) → Prop}

theorem congr (h : S.Definable n p) (equivalent : ∀ s, p s ↔ q s) : S.Definable n q := by
  obtain ⟨f, bound, same⟩ := h
  exact ⟨f, bound, fun s => (same s).trans (equivalent s)⟩

theorem atom (r : A) {i j : Nat} (hi : i < n) (hj : j < n) :
    S.Definable n (fun s => S.rel r (s i) (s j)) :=
  ⟨.atom r i j, ⟨hi, hj⟩, fun _ => Iff.rfl⟩

theorem eq {i j : Nat} (hi : i < n) (hj : j < n) :
    S.Definable n (fun s => s i = s j) :=
  ⟨.eq i j, ⟨hi, hj⟩, fun _ => Iff.rfl⟩

theorem and (hp : S.Definable n p) (hq : S.Definable n q) :
    S.Definable n (fun s => p s ∧ q s) := by
  obtain ⟨f, bf, hf⟩ := hp
  obtain ⟨g, bg, hg⟩ := hq
  exact ⟨.and f g, ⟨bf, bg⟩, fun s => and_congr (hf s) (hg s)⟩

theorem or (hp : S.Definable n p) (hq : S.Definable n q) :
    S.Definable n (fun s => p s ∨ q s) := by
  obtain ⟨f, bf, hf⟩ := hp
  obtain ⟨g, bg, hg⟩ := hq
  exact ⟨.or f g, ⟨bf, bg⟩, fun s => or_congr (hf s) (hg s)⟩

theorem implies (hp : S.Definable n p) (hq : S.Definable n q) :
    S.Definable n (fun s => p s → q s) := by
  obtain ⟨f, bf, hf⟩ := hp
  obtain ⟨g, bg, hg⟩ := hq
  exact ⟨.imp f g, ⟨bf, bg⟩, fun s => imp_congr (hf s) (hg s)⟩

theorem not (h : S.Definable n p) : S.Definable n (fun s => ¬p s) := by
  obtain ⟨f, bound, h⟩ := h
  exact ⟨.imp f .bot, ⟨bound, trivial⟩, fun s => not_congr (h s)⟩

theorem iff (hp : S.Definable n p) (hq : S.Definable n q) :
    S.Definable n (fun s => p s ↔ q s) :=
  ((hp.implies hq).and (hq.implies hp)).congr fun _ => ⟨fun ⟨p, q⟩ => ⟨p, q⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem all (h : S.Definable (n + 1) p) :
    S.Definable n (fun s => ∀ x, p (pushValue s x)) := by
  obtain ⟨f, bound, h⟩ := h
  exact ⟨.all f, bound, fun s => forall_congr' fun x => h (pushValue s x)⟩

theorem ex (h : S.Definable (n + 1) p) :
    S.Definable n (fun s => ∃ x, p (pushValue s x)) := by
  obtain ⟨f, bound, h⟩ := h
  exact ⟨.ex f, bound, fun s => exists_congr fun x => h (pushValue s x)⟩

theorem boundedAll {i : Nat} (hi : i < n) (p : (Nat → V) → Prop)
    (h : S.Definable (n + 1) p) :
    S.Definable n (fun s => ∀ x, S.rel (M.constant .E) x (s i) → p (pushValue s x)) :=
  Definable.all ((Definable.atom (S := S) (n := n + 1) (M.constant .E) (i := 0) (j := i + 1) (by omega) (by omega)).implies h)

theorem boundedEx {i : Nat} (hi : i < n) (p : (Nat → V) → Prop)
    (h : S.Definable (n + 1) p) :
    S.Definable n (fun s => ∃ x, S.rel (M.constant .E) x (s i) ∧ p (pushValue s x)) :=
  Definable.ex ((Definable.atom (S := S) (n := n + 1) (M.constant .E) (i := 0) (j := i + 1) (by omega) (by omega)).and h)

theorem lift_set_formula (formula : Formula) (closed : Bound formula n)
    (defines : ∀ s, eval (S.rel (M.constant .E)) formula s ↔ p s) : S.Definable n p :=
  ⟨RelationFormula.liftMembership (M.constant .E) formula,
    (RelationFormula.liftMembership_bound _ _ _).mpr closed,
    fun s => (RelationFormula.liftMembership_eval _ _ s).trans (defines s)⟩

theorem reindex (h : S.Definable n p) {m : Nat} (map : Nat → Nat)
    (within : ∀ i, i < n → map i < m) :
    S.Definable m (fun s => p (s ∘ map)) := by
  obtain ⟨f, bound, agrees⟩ := h
  exact ⟨f.reindex map, f.reindex_bound bound within,
    fun s => (RelationFormula.reindex_eval S f map s).trans (agrees (s ∘ map))⟩

/-- Reuse a set-builder formula with its established meaning, while
keeping arbitrary represented predicates available in outer formulas. -/
theorem of_levels {body : SetFormula} (scope : SetFormula.Scoped n body)
    (signature : ∀ env default, SetFormula.holds (S.rel (M.constant .E)) body n env default ↔ p env) :
    S.Definable n (fun s => p fun i => s (n - (i + 1))) := by
  apply lift_set_formula (body n) scope
  intro s
  exact (SetFormula.eval_levels (default := s 0) body scope).trans (signature _ _)

end Definable

namespace SetContext

variable (N : SetContext M V)

abbrev mem (x set : V) : Prop := N.square.rel (M.constant .E) x set

theorem image (params : List V) {R : (Nat → V) → Prop}
    (described : N.square.Definable (params.length + 2) R)
    (functional : ∀ x y z, R (parameterEnv params x y) → R (parameterEnv params x z) → y = z)
    (source : V) :
    ∃ target, ∀ y, N.mem y target ↔ ∃ x, N.mem x source ∧ R (parameterEnv params x y) := by
  obtain ⟨f, bound, h⟩ := described
  obtain ⟨target, spec⟩ := N.replaces params f bound
    (fun x y z hy hz => functional x y z ((h _).mp hy) ((h _).mp hz)) source
  exact ⟨target, fun y => (spec y).trans (exists_congr fun x => and_congr_right fun _ => h _)⟩

theorem separate (params : List V) {P : (Nat → V) → Prop}
    (described : N.square.Definable (params.length + 2) P) (source anchor : V) :
    ∃ target, ∀ x, N.mem x target ↔ N.mem x source ∧ P (parameterEnv params x anchor) := by
  obtain ⟨f, bound, h⟩ := described
  obtain ⟨target, spec⟩ := N.separates params f bound source anchor
  exact ⟨target, fun x => (spec x).trans (and_congr_right fun _ => h _)⟩

end SetContext
end PalomarI3380.SquareRepresentation
