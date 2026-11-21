module
public import M6.Source.Cantor
public import I0451.Identity

/-! Formula syntax and numeric constructors of the literal proof search.
The zero code is truth. Code one is `v₀ ∈ v₀`, and hence is false in
every irreflexive membership structure. -/
@[expose] public section
namespace I0451.Logic

open M6.Source.Cantor

theorem triangle_ge (n : Nat) : n ≤ triangle n := by
  induction n with
  | zero => decide
  | succ n ih => simp only [triangle]; omega

theorem pair_ge (x y : Nat) : x + y ≤ pair x y := by
  have h := triangle_ge (x + y)
  unfold pair
  omega

theorem decode_bounds (code : Nat) : (decode code).1 + (decode code).2 ≤ code := by
  have h := pair_ge (decode code).1 (decode code).2
  rwa [pair_decode] at h

/-- The four tagged constructors use the same Cantor pairing as the
register stack. The universal code stores its variable first. -/
def imp (a b : Nat) : Nat := 4 * pair a b
def mem (a b : Nat) : Nat := 4 * pair a b + 1
def all (a b : Nat) : Nat := 4 * pair a b + 2
def equal (a b : Nat) : Nat := 4 * pair a b + 3

def neg (a : Nat) : Nat := imp a 1
def ex (a b : Nat) : Nat := neg (all a (neg b))
def and (a b : Nat) : Nat := neg (imp a (neg b))
def iff (a b : Nat) : Nat := and (imp a b) (imp b a)
def or (a b : Nat) : Nat := imp (neg a) b

/-- Named first-order syntax for the same language. -/
inductive Formula where
  | truth
  | imp (antecedent consequent : Formula)
  | mem (left right : Nat)
  | all (label : Nat) (body : Formula)
  | equal (left right : Nat)
  deriving DecidableEq, Repr

def Formula.code : Formula → Nat
  | .truth => 0
  | .imp a b => Logic.imp a.code b.code
  | .mem a b => Logic.mem a b
  | .all a b => Logic.all a b.code
  | .equal a b => Logic.equal a b

/-- Decode every numeric formula, identifying the redundant zero code
for truth implies truth with truth. -/
def Formula.decode (code : Nat) : Formula :=
  if _h : code = 0 then .truth
  else
    let xy := M6.Source.Cantor.decode (code / 4)
    match code % 4 with
    | 0 => .imp (Formula.decode xy.1) (Formula.decode xy.2)
    | 1 => .mem xy.1 xy.2
    | 2 => .all xy.1 (Formula.decode xy.2)
    | _ => .equal xy.1 xy.2
termination_by code
decreasing_by
  all_goals
    have bounds := decode_bounds (code / 4)
    omega

def assign {V : Type} (values : Nat → V) (x : Nat) (v : V) : Nat → V :=
  fun y => if y = x then v else values y

def Formula.eval {V : Type} (E : V → V → Prop) (values : Nat → V) : Formula → Prop
  | .truth => True
  | .imp a b => a.eval E values → b.eval E values
  | .mem a b => E (values a) (values b)
  | .all x formula => ∀ v, formula.eval E (assign values x v)
  | .equal a b => values a = values b

def Eval {V : Type} (E : V → V → Prop) (values : Nat → V) (code : Nat) : Prop :=
  (Formula.decode code).eval E values

private theorem splitCode (tag : Nat) (bound : tag < 4) (a b : Nat) :
    M6.Source.Cantor.decode ((4 * pair a b + tag) / 4) = (a, b) ∧
      (4 * pair a b + tag) % 4 = tag := by
  have quotient : (4 * pair a b + tag) / 4 = pair a b := by omega
  exact ⟨by rw [quotient, decode_pair], by omega⟩

theorem eval_zero {V : Type} (E : V → V → Prop) (values : Nat → V) : Eval E values 0 := by
  rw [Eval, Formula.decode]
  simp [Formula.eval]

theorem eval_imp {V : Type} (E : V → V → Prop) (values : Nat → V) (a b : Nat) :
    Eval E values (imp a b) ↔ (Eval E values a → Eval E values b) := by
  have field := splitCode 0 (by decide) a b
  simp only [Nat.add_zero] at field
  by_cases zero : imp a b = 0
  · have bounded := pair_ge a b
    unfold imp at zero
    have both : a = 0 ∧ b = 0 := by omega
    obtain ⟨rfl, rfl⟩ := both
    exact ⟨fun _ _ => eval_zero E values, fun _ => eval_zero E values⟩
  · unfold Eval
    rw [Formula.decode, dite_eq_right zero]
    simp only [imp, field.1, field.2, Formula.eval]

theorem eval_mem {V : Type} (E : V → V → Prop) (values : Nat → V) (a b : Nat) :
    Eval E values (mem a b) ↔ E (values a) (values b) := by
  have field := splitCode 1 (by decide) a b
  have positive : mem a b ≠ 0 := by unfold mem; omega
  unfold Eval
  rw [Formula.decode, dite_eq_right positive]
  simp only [mem, field.1, field.2, Formula.eval]

theorem eval_all {V : Type} (E : V → V → Prop) (values : Nat → V) (a b : Nat) :
    Eval E values (all a b) ↔ ∀ v, Eval E (assign values a v) b := by
  have field := splitCode 2 (by decide) a b
  have positive : all a b ≠ 0 := by unfold all; omega
  unfold Eval
  rw [Formula.decode, dite_eq_right positive]
  simp only [all, field.1, field.2, Formula.eval]

theorem eval_equal {V : Type} (E : V → V → Prop) (values : Nat → V) (a b : Nat) :
    Eval E values (equal a b) ↔ values a = values b := by
  have field := splitCode 3 (by decide) a b
  have positive : equal a b ≠ 0 := by unfold equal; omega
  unfold Eval
  rw [Formula.decode, dite_eq_right positive]
  simp only [equal, field.1, field.2, Formula.eval]

theorem eval_formula {V : Type} (E : V → V → Prop) (f : Formula) (s : Nat → V) :
    Eval E s f.code ↔ f.eval E s := by
  induction f generalizing s with
  | truth => exact ⟨fun _ => trivial, fun _ => eval_zero E s⟩
  | imp a b left right => simp only [Formula.code, Formula.eval, eval_imp, left, right]
  | mem a b => exact eval_mem E s a b
  | all a b ih => simp only [Formula.code, Formula.eval, eval_all, ih]
  | equal a b => exact eval_equal E s a b

theorem eval_neg {V : Type} {E : V → V → Prop} (irrefl : ∀ x, ¬ E x x)
    (s : Nat → V) (code : Nat) : Eval E s (neg code) ↔ ¬ Eval E s code := by
  unfold neg
  rw [eval_imp, show (1 : Nat) = mem 0 0 by decide, eval_mem]
  exact ⟨fun h valid => irrefl _ (h valid), fun h valid => (h valid).elim⟩

theorem eval_false {V : Type} {E : V → V → Prop} (s : Nat → V)
    (irrefl : ∀ x, ¬ E x x) : ¬ Eval E s 1 := by
  rw [show (1 : Nat) = mem 0 0 by decide, eval_mem]
  exact irrefl _

theorem eval_and {V : Type} {E : V → V → Prop} (s : Nat → V)
    (irrefl : ∀ x, ¬ E x x) (a b : Nat) :
    Eval E s (and a b) ↔ Eval E s a ∧ Eval E s b := by
  unfold and
  rw [eval_neg irrefl, eval_imp, eval_neg irrefl]
  constructor
  · intro h
    exact ⟨Classical.byContradiction (fun na => h (fun a => (na a).elim)),
      Classical.byContradiction (fun nb => h (fun _ => nb))⟩
  · rintro ⟨ha, hb⟩ h
    exact h ha hb

theorem eval_iff {V : Type} {E : V → V → Prop} (s : Nat → V)
    (irrefl : ∀ x, ¬ E x x) (a b : Nat) :
    Eval E s (iff a b) ↔ (Eval E s a ↔ Eval E s b) := by
  unfold iff
  rw [eval_and s irrefl, eval_imp, eval_imp]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem eval_ex {V : Type} {E : V → V → Prop} (s : Nat → V)
    (irrefl : ∀ x, ¬ E x x) (a b : Nat) :
    Eval E s (ex a b) ↔ ∃ v, Eval E (assign s a v) b := by
  unfold ex
  rw [eval_neg irrefl, eval_all]
  simp only [eval_neg irrefl, Classical.not_forall, Classical.not_not]

/-- Every syntactic variable and bound label is less than the code.
This lets a numeric operand serve as a fresh label for its own formula. -/
def Formula.LabelsBelow : Formula → Nat → Prop
  | .truth, _ => True
  | .imp a b, n => a.LabelsBelow n ∧ b.LabelsBelow n
  | .all x b, n => x < n ∧ b.LabelsBelow n
  | .mem a b, n | .equal a b, n => a < n ∧ b < n

theorem Formula.LabelsBelow.mono {f : Formula} {n m : Nat}
    (h : f.LabelsBelow n) (bound : n ≤ m) : f.LabelsBelow m := by
  induction f with
  | truth => trivial
  | imp a b ha hb => exact ⟨ha h.1, hb h.2⟩
  | all x b ih => exact ⟨Nat.lt_of_lt_of_le h.1 bound, ih h.2⟩
  | mem a b | equal a b => exact ⟨Nat.lt_of_lt_of_le h.1 bound, Nat.lt_of_lt_of_le h.2 bound⟩

theorem decoded_labels (code : Nat) : (Formula.decode code).LabelsBelow code := by
  induction code using Nat.strongRecOn with
  | ind code ih =>
    rw [Formula.decode]
    split
    · trivial
    · rename_i nonzero
      have field := decode_bounds (code / 4)
      have left : (decode (code / 4)).1 < code := by omega
      have right : (decode (code / 4)).2 < code := by omega
      split
      · exact ⟨(ih _ left).mono (Nat.le_of_lt left), (ih _ right).mono (Nat.le_of_lt right)⟩
      · exact ⟨left, right⟩
      · exact ⟨left, (ih _ right).mono (Nat.le_of_lt right)⟩
      · exact ⟨left, right⟩

theorem assign_distinct {V : Type} (s : Nat → V) (x y : Nat) (different : x ≠ y)
    (v w : V) : assign (assign s x v) y w = assign (assign s y w) x v := by
  funext z
  by_cases zx : z = x
  · subst z
    simp [assign, different]
  · by_cases zy : z = y
    · subst z
      simp [assign, zx]
    · simp [assign, zx, zy]

theorem Formula.eval_fresh {V : Type} (E : V → V → Prop) (f : Formula)
    {n : Nat} (below : f.LabelsBelow n) (s : Nat → V) (v : V) :
    f.eval E (assign s n v) ↔ f.eval E s := by
  induction f generalizing s with
  | truth => rfl
  | imp a b ha hb => simp only [Formula.eval, ha below.1, hb below.2]
  | mem a b =>
    simp only [Formula.eval, assign, ite_eq_right (Nat.ne_of_lt below.1),
      ite_eq_right (Nat.ne_of_lt below.2)]
  | equal a b =>
    simp only [Formula.eval, assign, ite_eq_right (Nat.ne_of_lt below.1),
      ite_eq_right (Nat.ne_of_lt below.2)]
  | all x b ih =>
    simp only [Formula.eval]
    apply forall_congr'
    intro w
    rw [assign_distinct s n x (Nat.ne_of_lt below.1).symm v w]
    exact ih below.2 _

theorem eval_fresh {V : Type} (E : V → V → Prop) (code label : Nat) (enough : code ≤ label)
    (s : Nat → V) (v : V) :
    Eval E (assign s label v) code ↔ Eval E s code :=
  (Formula.decode code).eval_fresh E ((decoded_labels code).mono enough) s v

end I0451.Logic
