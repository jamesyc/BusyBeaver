module
public import I0451.Logic.NamedSemantics
public import I0451.Logic.SourceSetModel
public import I0451.Logic.BerkeleyTheory

/-! Reuse the AX templates to read their source-calculus consequences
as ordinary first-order sentences. Formula operands and variable labels
are represented separately while constructing the named syntax. -/
@[expose] public section
namespace I0451.Logic.NamedFormula

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory FFL.FirstOrder.Arithmetic
open I0451.Arithmetization I0451.Runtime I0451.Omega
open ZF207.CKernel.Generic

def not (f : NamedFormula) : NamedFormula := .imp f .falsity
def and (p q : NamedFormula) : NamedFormula := (p.imp q.not).not
def or (p q : NamedFormula) : NamedFormula := p.not.imp q
def existsAt (i : Nat) (p : NamedFormula) : NamedFormula := (NamedFormula.all i p.not).not

@[simp] theorem eval_not {V : Type} [Tarski.Structure ℒₛₑₜ V] (s : Nat → V) (f : NamedFormula) :
    f.not.eval s ↔ ¬ f.eval s := Iff.rfl

@[simp] theorem eval_and {V : Type} [Tarski.Structure ℒₛₑₜ V] (s : Nat → V) (p q : NamedFormula) :
    (p.and q).eval s ↔ p.eval s ∧ q.eval s := by
  classical
  simp [and, not, eval]

@[simp] theorem eval_or {V : Type} [Tarski.Structure ℒₛₑₜ V] (s : Nat → V) (p q : NamedFormula) :
    (p.or q).eval s ↔ p.eval s ∨ q.eval s := by
  classical
  by_cases h : p.eval s <;> simp [or, not, eval, h]

@[simp] theorem eval_existsAt {V : Type} [Tarski.Structure ℒₛₑₜ V] (s : Nat → V) (i : Nat) (p : NamedFormula) :
    (existsAt i p).eval s ↔ ∃ v : V, p.eval (assign s i v) := by
  classical
  simp [existsAt, not, eval]

def subset (bound a b : Nat) : NamedFormula :=
  cxvg_subset%(NamedFormula.all, NamedFormula.imp, NamedFormula.mem, bound, a, b)

def container (a b c : Nat) : NamedFormula :=
  cxvg_containerCode%(existsAt, and, NamedFormula.all, NamedFormula.imp, NamedFormula.mem, subset, a, b, c)

def extensionality (a b c : Nat) : NamedFormula :=
  cxvg_extensionalityCode%(NamedFormula.imp, subset, NamedFormula.equal, a, b, c)

noncomputable def collection (a b : Nat) (f : NamedFormula) : NamedFormula :=
  cxvg_collectionCode%(existsAt, and, NamedFormula.all, NamedFormula.imp, NamedFormula.mem, a, b, f.code, f)

theorem container_provable {a b c : Nat} (left : c ≠ a) (right : c ≠ b) :
    NativeDerivable (container a b c).code := by
  have bundled : calculus.Ctx [] (modelEncoding.bundle a b c) := .thm (NativeDerivable.bundle left right)
  exact bundled.andLeft.empty

theorem extensionality_provable {a b c : Nat} (left : c ≠ a) (right : c ≠ b) :
    NativeDerivable (extensionality a b c).code := by
  have bundled : calculus.Ctx [] (modelEncoding.bundle a b c) := .thm (NativeDerivable.bundle left right)
  exact bundled.andRight.andLeft.empty

theorem collection_provable {a b : Nat} (f : NamedFormula) (left : f.code ≠ a) (right : f.code ≠ b) :
    NativeDerivable (collection a b f).code := by
  have bundled : calculus.Ctx [] (modelEncoding.bundle a b f.code) := .thm (NativeDerivable.bundle left right)
  exact bundled.andRight.andRight.andRight.empty

variable {V : Type} [SetStructure V]

@[simp] theorem membership_rel (a b : V) :
    Tarski.Structure.rel (L := ℒₛₑₜ) Language.Set.Rel.mem ![a,b] ↔ a ∈ b := Iff.rfl

@[simp] theorem equality_rel (a b : V) :
    Tarski.Structure.rel (L := ℒₛₑₜ) Language.Set.Rel.eq ![a,b] ↔ a = b := Iff.rfl

theorem subset_eval (s : Nat → V) {a b c : Nat} (ca : a ≠ c) (cb : b ≠ c) :
    (subset c a b).eval s ↔ s a ⊆ s b := by
  simp [subset, eval, assign, ca, cb] <;> rfl

theorem container_eval (s : Nat → V) :
    (container 1 2 3).eval s ↔ ∃ d : V, s 3 ∈ d ∧ ∀ x ∈ d,
      (∃ w ∈ d, ∀ y : V, y ⊆ x → y ∈ w) ∧ x ⊆ d := by
  simp only [container, eval_existsAt, eval_and, eval, subset_eval _ (by decide : (1 : Nat) ≠ 3)
    (by decide : (2 : Nat) ≠ 3), subset_eval _ (by decide : (2 : Nat) ≠ 3)
    (by decide : (1 : Nat) ≠ 3), assign]
  simp
  constructor
  · rintro ⟨d, props, marker⟩
    exact ⟨d, marker, fun x xd => ⟨by
      obtain ⟨w, power, belongs⟩ := (props x xd).1
      exact ⟨w, belongs, power⟩, (props x xd).2⟩⟩
  · rintro ⟨d, marker, props⟩
    exact ⟨d, fun x xd => ⟨by
      obtain ⟨w, belongs, power⟩ := (props x xd).1
      exact ⟨w, power, belongs⟩, (props x xd).2⟩, marker⟩

theorem extensionality_eval (s : Nat → V) :
    (extensionality 1 2 3).eval s ↔ (s 1 ⊆ s 2 → s 2 ⊆ s 1 → s 1 = s 2) := by
  simp only [extensionality, eval, subset_eval _ (by decide : (1 : Nat) ≠ 3)
    (by decide : (2 : Nat) ≠ 3), subset_eval _ (by decide : (2 : Nat) ≠ 3)
    (by decide : (1 : Nat) ≠ 3), equality_rel]

theorem eval_freshLabel (f : NamedFormula) (s : Nat → V) {x : Nat} (fresh : x ∉ f.labels) (v : V) :
    f.eval (assign s x v) ↔ f.eval s :=
  f.eval_depends fun i used => by
    have noEq : i ≠ x := fun same => fresh (same ▸ freeLabel_is_label used)
    simp [assign,noEq]

theorem collection_eval (s : Nat → V) (f : NamedFormula)
    (left : f.code ≠ 1) (right : f.code ≠ 2) (fresh : f.code ∉ f.labels) :
    (collection 1 2 f).eval s ↔
      ∃ d : V,
        (∀ x ∈ s 2, (∃ y : V, f.eval (assign (assign s 1 x) 2 y)) →
          ∃ z ∈ d, f.eval (assign (assign s 1 x) 2 z)) ∧
        (∀ y ∈ d, ∃ x : V, f.eval (assign (assign s 1 x) 2 y)) := by
  let c := f.code
  have unchanged (cover x y : V) :
      f.eval (assign (assign (assign s c cover) 1 x) 2 y) ↔
        f.eval (assign (assign s 1 x) 2 y) := by
    rw [assign_distinct s c 1 left, assign_distinct (assign s 1 x) c 2 right]
    exact f.eval_freshLabel _ fresh _
  have backwards (cover x y : V) :
      f.eval (assign (assign (assign s c cover) 2 y) 1 x) ↔
        f.eval (assign (assign s 1 x) 2 y) := by
    rw [assign_distinct _ 2 1 (by decide)]
    exact unchanged cover x y
  simp only [collection, eval_existsAt, eval_and, eval]
  change (∃ cover : V,
    (∀ x : V, _ → ∀ y : V, _ → ∃ z, _ ∧ _) ∧ (∀ y : V, _ → ∃ x, _)) ↔ _
  simp only [assign_same, unchanged, backwards]
  have one : (1 : Nat) ≠ c := Ne.symm left
  have two : (2 : Nat) ≠ c := Ne.symm right
  simp [assign,two,left,right,c,and_comm]
  simp only [c] at unchanged backwards
  simp only [unchanged, backwards]

end I0451.Logic.NamedFormula
