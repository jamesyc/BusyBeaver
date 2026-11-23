module
public import I3_334Support.Logic.SetFormulas
@[expose] public section

namespace PalomarI3380.Logic

universe u

theorem eval_congr_bound {V : Type u} {E : V → V → Prop} (p : Formula) {n : Nat}
    (hp : Bound p n) {s t : Nat → V} (h : ∀ i, i < n → s i = t i) :
    eval E p s ↔ eval E p t := by
  induction p generalizing n s t with
  | bot => rfl
  | mem i j | eq i j => simp only [eval, h i hp.1, h j hp.2]
  | and p q ihp ihq => simp only [eval, ihp hp.1 h, ihq hp.2 h]
  | or p q ihp ihq => simp only [eval, ihp hp.1 h, ihq hp.2 h]
  | imp p q ihp ihq => simp only [eval, ihp hp.1 h, ihq hp.2 h]
  | all p ih =>
    change (∀ x, eval E p (pushValue s x)) ↔ ∀ x, eval E p (pushValue t x)
    apply forall_congr'
    intro x
    apply ih hp
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact h i (by omega)
  | ex p ih =>
    change (∃ x, eval E p (pushValue s x)) ↔ ∃ x, eval E p (pushValue t x)
    apply exists_congr
    intro x
    apply ih hp
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact h i (by omega)

end PalomarI3380.Logic

namespace PalomarI3380.Logic.SetFormula

universe u

/-- Read an assignment by binder level in a de Bruijn context. Values
outside that context use a fixed default. -/
def assignment {V : Type u} (depth : Nat) (env : Nat → V) (default : V) : Nat → V :=
  fun i => if i < depth then env (depth - (i + 1)) else default

def assign {V : Type u} (env : Nat → V) (level : Nat) (value : V) : Nat → V :=
  fun i => if i = level then value else env i

theorem assignment_extend {V : Type u} (d : Nat) (env : Nat → V) (default value : V) :
    assignment (d + 1) (assign env d value) default =
      pushValue (assignment d env default) value := by
  funext i
  cases i with
  | zero =>
    simp only [assignment, pushValue, show 0 < d + 1 by omega, ↓reduceIte,
      show d + 1 - (0 + 1) = d by omega, assign]
  | succ n =>
    by_cases inScope : n < d
    · have hNew : n + 1 < d + 1 := by omega
      have hIndex : d + 1 - (n + 1 + 1) = d - (n + 1) := by omega
      have hOther : d - (n + 1) ≠ d := by omega
      simp only [assignment, pushValue, hNew, inScope, ↓reduceIte, hIndex, assign, hOther]
    · have hNew : ¬n + 1 < d + 1 := by omega
      simp only [assignment, pushValue, hNew, inScope, ↓reduceIte]

theorem assignment_level {V : Type u} (d x : Nat) (env : Nat → V) (default : V) (hx : x < d) :
    assignment d env default (d - (x + 1)) = env x := by
  have hIndex : d - (x + 1) < d := by omega
  have hRepeated : d - (d - (x + 1) + 1) = x := by omega
  simp only [assignment, hIndex, ↓reduceIte, hRepeated]

def holds {V : Type u} (E : V → V → Prop) (p : SetFormula) (d : Nat)
    (env : Nat → V) (default : V) : Prop :=
  eval E (p d) (assignment d env default)

@[simp] theorem holds_eq {V : Type u} (E : V → V → Prop) (d x y : Nat)
    (env : Nat → V) (default : V) (hx : x < d) (hy : y < d) :
    holds E (eq x y) d env default ↔ env x = env y := by
  simp only [holds, eq, eval, assignment_level d x env default hx, assignment_level d y env default hy]

@[simp] theorem holds_mem {V : Type u} (E : V → V → Prop) (d x y : Nat)
    (env : Nat → V) (default : V) (hx : x < d) (hy : y < d) :
    holds E (mem x y) d env default ↔ E (env x) (env y) := by
  simp only [holds, mem, eval, assignment_level d x env default hx, assignment_level d y env default hy]

@[simp] theorem holds_every {V : Type u} (E : V → V → Prop) (body : Nat → SetFormula)
    (d : Nat) (env : Nat → V) (default : V) :
    holds E (every body) d env default ↔ ∀ x, holds E (body d) (d + 1) (assign env d x) default := by
  simp only [holds, every, eval, assignment_extend]

@[simp] theorem holds_someSet {V : Type u} (E : V → V → Prop) (body : Nat → SetFormula)
    (d : Nat) (env : Nat → V) (default : V) :
    holds E (someSet body) d env default ↔ ∃ x, holds E (body d) (d + 1) (assign env d x) default := by
  simp only [holds, someSet, eval, assignment_extend]

@[simp] theorem assign_here {V : Type u} (env : Nat → V) (d : Nat) (value : V) :
    assign env d value d = value := by simp [assign]

@[simp] theorem assign_earlier {V : Type u} (env : Nat → V) (d i : Nat) (value : V)
    (hi : i < d) : assign env d value i = env i := by
  simp [assign, Nat.ne_of_lt hi]

variable {V : Type u} {E : V → V → Prop} {d : Nat} {env : Nat → V} {default : V}

theorem holds_falsity : holds E falsity d env default ↔ False := Iff.rfl
theorem holds_both (p q : SetFormula) :
    holds E (both p q) d env default ↔ holds E p d env default ∧ holds E q d env default := Iff.rfl
theorem holds_either (p q : SetFormula) :
    holds E (either p q) d env default ↔ holds E p d env default ∨ holds E q d env default := Iff.rfl
theorem holds_implies (p q : SetFormula) :
    holds E (implies p q) d env default ↔ (holds E p d env default → holds E q d env default) := Iff.rfl
theorem holds_neg (p : SetFormula) :
    holds E (neg p) d env default ↔ ¬holds E p d env default := Iff.rfl
theorem holds_iff (p q : SetFormula) :
    holds E (iff p q) d env default ↔ (holds E p d env default ↔ holds E q d env default) :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem holds_allOf (ps : List SetFormula) :
    holds E (allOf ps) d env default ↔ ∀ p ∈ ps, holds E p d env default := by
  induction ps with
  | nil => simp [allOf, holds_neg, holds_falsity]
  | cons p ps ih => simp [allOf, holds_both, ih]

theorem holds_anyOf (ps : List SetFormula) :
    holds E (anyOf ps) d env default ↔ ∃ p ∈ ps, holds E p d env default := by
  induction ps with
  | nil => simp [anyOf, holds_falsity]
  | cons p ps ih => simp [anyOf, holds_either, ih]

theorem holds_eachIn (domain : Nat) (body : Nat → SetFormula) (hd : domain < d) :
    holds E (eachIn domain body) d env default ↔
      ∀ x, E x (env domain) → holds E (body d) (d + 1) (assign env d x) default := by
  simp (disch := omega) only [eachIn, holds_every, holds_implies, holds_mem, assign_here, assign_earlier]

theorem holds_someIn (domain : Nat) (body : Nat → SetFormula) (hd : domain < d) :
    holds E (someIn domain body) d env default ↔
      ∃ x, E x (env domain) ∧ holds E (body d) (d + 1) (assign env d x) default := by
  simp (disch := omega) only [someIn, holds_someSet, holds_both, holds_mem, assign_here, assign_earlier]

/-- Reuse builder semantics with an ordinary de Bruijn assignment. -/
theorem eval_levels (p : SetFormula) (h : Bound (p d) d) :
    eval E (p d) env ↔ holds E p d (fun i => env (d - (i + 1))) default := by
  apply eval_congr_bound (p d) h
  intro i hi
  simp only [assignment, hi, ↓reduceIte, show d - (d - (i + 1) + 1) = i by omega]

end PalomarI3380.Logic.SetFormula
