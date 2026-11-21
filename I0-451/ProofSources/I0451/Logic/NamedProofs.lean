module
public import I0451.ArithmeticNativeLogic
public import I0451.Logic.SetSyntax

/-! Named logical formulas used to normalize the standard axioms before
they are handed to the internal compiler. Falsity is a logical constant
whose numeric representation is the machine's code one. -/
@[expose] public section
namespace I0451.Logic

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open I0451.Arithmetization I0451.Runtime
open ZF207.CKernel.Generic

inductive NamedFormula where
  | truth
  | falsity
  | mem (x y : Nat)
  | equal (x y : Nat)
  | imp (left right : NamedFormula)
  | all (label : Nat) (body : NamedFormula)
  deriving DecidableEq

namespace NamedFormula

noncomputable def code : NamedFormula → Nat
  | .truth => 0
  | .falsity => 1
  | .mem x y => modelTag 1 x y
  | .equal x y => modelTag 3 x y
  | .imp a b => modelImp a.code b.code
  | .all x a => modelTag 2 x a.code

def labels : NamedFormula → List Nat
  | .truth | .falsity => []
  | .mem x y | .equal x y => [x,y]
  | .imp p q => p.labels ++ q.labels
  | .all x p => x :: p.labels

def changeFree (before after : Nat) : NamedFormula → NamedFormula
  | .truth => .truth
  | .falsity => .falsity
  | .mem x y => .mem (if x = before then after else x) (if y = before then after else y)
  | .equal x y => .equal (if x = before then after else x) (if y = before then after else y)
  | .imp p q => .imp (changeFree before after p) (changeFree before after q)
  | .all x p => if x = before then .all x p else .all x (changeFree before after p)

noncomputable def calculus : EqLogic Nat := NativeDerivable.equality (fun _ => True)

@[simp] theorem calculus_all (x body : Nat) : calculus.all x body = modelTag 2 x body := rfl

local notation "NATIVE" => calculus
local notation "K" => calculus.toLogic

theorem irrelevant {x : Nat} (f : NamedFormula) (absent : x ∉ f.labels) :
    (K).Prov ((K).imp f.code ((K).all x f.code)) := by
  induction f with
  | truth =>
    have h : (K).Prov (0 : Nat) := NativeDerivable.truth
    exact (K).mp ((K).gen x h) ((K).k _ _)
  | falsity => exact (K).botVacuity x
  | mem a b =>
    simp only [labels, List.mem_cons, List.not_mem_nil, or_false, not_or] at absent
    exact (NATIVE).memVac a b x absent.1 absent.2
  | equal a b =>
    simp only [labels, List.mem_cons, List.not_mem_nil, or_false, not_or] at absent
    exact (NATIVE).eVac a b x absent.1 absent.2 trivial trivial trivial
  | imp a b ihA ihB =>
    simp only [labels, List.mem_append, not_or] at absent
    exact (K).implicationVacuity x _ _ (ihA absent.1) (ihB absent.2)
  | all y f ih =>
    simp only [labels, List.mem_cons, not_or] at absent
    exact (K).universalVacuity x y _ (ih absent.2)

private theorem equalityContext {x y : Nat} :
    (K).Ctx [(NATIVE).E x y] ((NATIVE).E x y) := .head

private theorem leftMember {x y a b z : Nat} (same : a = b ∨ (a = x ∧ b = y)) :
    (K).Ctx [(NATIVE).E x y] ((K).iff ((K).mem a z) ((K).mem b z)) := by
  rcases same with rfl | ⟨sameA,sameB⟩
  · exact .iffRefl _
  · subst a
    subst b
    have symmetry : (K).Ctx [(NATIVE).E x y] ((NATIVE).E y x) :=
      .mp equalityContext (.thm ((NATIVE).eSymm x y trivial trivial))
    exact Logic.Ctx.iffIntro
      (.mp .head (.mp (equalityContext.up _) (.thm (NativeDerivable.native_mem_left x y z))))
      (.mp .head (.mp (symmetry.up _) (.thm (NativeDerivable.native_mem_left y x z))))

private theorem rightMember {x y a b z : Nat} (same : a = b ∨ (a = x ∧ b = y)) :
    (K).Ctx [(NATIVE).E x y] ((K).iff ((K).mem z a) ((K).mem z b)) := by
  rcases same with rfl | ⟨sameA,sameB⟩
  · exact .iffRefl _
  · subst a
    subst b
    have symmetry : (K).Ctx [(NATIVE).E x y] ((NATIVE).E y x) :=
      .mp equalityContext (.thm ((NATIVE).eSymm x y trivial trivial))
    exact Logic.Ctx.iffIntro
      (.mp .head (.mp (equalityContext.up _) (.thm (NativeDerivable.native_mem_right x y z))))
      (.mp .head (.mp (symmetry.up _) (.thm (NativeDerivable.native_mem_right y x z))))

private theorem changesLabel (x y k : Nat) :
    k = (if k = x then y else k) ∨ (k = x ∧ (if k = x then y else k) = y) := by
  by_cases h : k = x <;> simp [h]

private theorem leftEquality {x y a b z : Nat} (same : a = b ∨ (a = x ∧ b = y)) :
    (K).Ctx [(NATIVE).E x y] ((K).iff ((NATIVE).E a z) ((NATIVE).E b z)) := by
  rcases same with rfl | ⟨sameA,sameB⟩
  · exact .iffRefl _
  · subst a
    subst b
    exact .mp equalityContext (.thm ((NATIVE).eLeftIff trivial trivial trivial))

private theorem rightEquality {x y a b z : Nat} (same : a = b ∨ (a = x ∧ b = y)) :
    (K).Ctx [(NATIVE).E x y] ((K).iff ((NATIVE).E z a) ((NATIVE).E z b)) := by
  rcases same with rfl | ⟨sameA,sameB⟩
  · exact .iffRefl _
  · subst a
    subst b
    exact .mp equalityContext (.thm ((NATIVE).eRightIff trivial trivial trivial))

theorem changeFree_context {x y : Nat} (f : NamedFormula) (fresh : y ∉ f.labels) :
    (K).Ctx [(NATIVE).E x y] ((K).iff f.code (f.changeFree x y).code) := by
  induction f with
  | truth => exact .iffRefl _
  | falsity => exact .iffRefl _
  | mem a b =>
    exact (leftMember (z := b) (changesLabel x y a)).iffTrans
      (rightMember (z := if a = x then y else a) (changesLabel x y b))
  | equal a b =>
    exact (leftEquality (z := b) (changesLabel x y a)).iffTrans
      (rightEquality (z := if a = x then y else a) (changesLabel x y b))
  | imp p q left right =>
    simp only [labels, List.mem_append, not_or] at fresh
    exact (left fresh.1).impCongr (right fresh.2)
  | all a p ih =>
    simp only [labels, List.mem_cons, not_or] at fresh
    by_cases same : a = x
    · rw [changeFree, if_pos same]
      exact Logic.Ctx.iffRefl _
    · simp only [changeFree, same, ite_false, code]
      exact Logic.Ctx.allCongr a (fun h member => by
        rw [List.mem_singleton.mp member]
        exact (NATIVE).eVac x y a same (Ne.symm fresh.1) trivial trivial trivial) (ih fresh.2)

def binders : NamedFormula → List Nat
  | .truth | .falsity | .mem _ _ | .equal _ _ => []
  | .imp p q => p.binders ++ q.binders
  | .all x p => x :: p.binders

theorem changeFree_binders (f : NamedFormula) (x y : Nat) :
    (f.changeFree x y).binders = f.binders := by
  induction f with
  | imp p q hp hq => simp [changeFree, binders, hp, hq]
  | all a p ih => by_cases h : a = x <;> simp [changeFree, binders, h, ih]
  | _ => rfl

theorem mem_labels_changeFree {f : NamedFormula} {x y a : Nat} :
    a ∈ (f.changeFree x y).labels → a ∈ f.labels ∨ a = y := by
  induction f with
  | truth | falsity => simp [changeFree, labels]
  | mem u v | equal u v =>
    simp [changeFree, labels]
    by_cases hu : u = x <;> by_cases hv : v = x <;> simp [hu, hv] <;> omega
  | imp p q hp hq =>
    simp only [changeFree, labels, List.mem_append]
    rintro (left | right)
    · exact (hp left).elim (fun h => .inl (.inl h)) Or.inr
    · exact (hq right).elim (fun h => .inl (.inr h)) Or.inr
  | all u p ih =>
    by_cases h : u = x
    · simp only [changeFree, h, ite_true]
      exact Or.inl
    · simp only [changeFree, h, ite_false, labels, List.mem_cons]
      rintro (rfl | inBody)
      · exact .inl (.inl rfl)
      · exact (ih inBody).elim (fun found => .inl (.inr found)) Or.inr

theorem changeFree_removes {x y : Nat} (f : NamedFormula) (different : x ≠ y) (noBinder : x ∉ f.binders) :
    x ∉ (f.changeFree x y).labels := by
  induction f with
  | truth | falsity => simp [changeFree, labels]
  | mem a b | equal a b =>
    simp [changeFree, labels]
    by_cases ha : a = x <;> by_cases hb : b = x <;> simp [ha, hb, different] <;> omega
  | imp p q hp hq =>
    simp only [binders, List.mem_append, not_or] at noBinder
    simp [changeFree, labels, hp noBinder.1, hq noBinder.2]
  | all a p ih =>
    simp only [binders, List.mem_cons, not_or] at noBinder
    simp [changeFree, labels, (Ne.symm noBinder.1), noBinder.1, ih noBinder.2]

attribute [local irreducible] modelTag modelImp

set_option maxHeartbeats 1400000 in
/-- Capture-avoiding substitution changes a binder after its old
label has been removed from the nested binders. -/
theorem renameBinder {x y : Nat} (f : NamedFormula) (different : x ≠ y)
    (fresh : y ∉ f.labels) (noBinder : x ∉ f.binders) :
    (K).Prov ((K).iff (.all x f : NamedFormula).code (.all y (f.changeFree x y) : NamedFormula).code) := by
  let changed := f.changeFree x y
  have absent := f.changeFree_removes different noBinder
  have forwardCtx : (K).Ctx [(NATIVE).E y x] ((K).iff f.code changed.code) := by
    apply (f.changeFree_context fresh).cut
    intro h mem
    rw [List.mem_singleton.mp mem]
    exact .mp .head (.thm ((NATIVE).eSymm y x trivial trivial))
  have specializeForward : (K).Prov ((K).imp ((K).all x f.code) changed.code) :=
    (NATIVE).specialize different trivial trivial forwardCtx.andLeft.deduction.empty (changed.irrelevant absent)
  have specializeBack : (K).Prov ((K).imp ((K).all y changed.code) f.code) :=
    (NATIVE).specialize different.symm trivial trivial
      (f.changeFree_context fresh).andRight.deduction.empty (f.irrelevant fresh)
  apply Logic.Ctx.empty
  apply Logic.Ctx.iffIntro
  · have step : (K).Ctx [(.all x f : NamedFormula).code] changed.code := .mp .head (.thm specializeForward)
    exact step.generalize y fun h mem => by
      rw [List.mem_singleton.mp mem]
      exact (.all x f : NamedFormula).irrelevant (by simp [labels, fresh, different.symm])
  · have step : (K).Ctx [(.all y changed : NamedFormula).code] f.code := .mp .head (.thm specializeBack)
    exact step.generalize x fun h mem => by
      rw [List.mem_singleton.mp mem]
      exact (.all y changed : NamedFormula).irrelevant (fun mem => by
      rcases (List.mem_cons.mp mem) with eq | appears
      · exact different eq
      · exact absent appears)

/-- Give each binder at a given depth the same fresh name. Binders on
separate branches can share a label because their scopes are disjoint. -/
def standardize (names : Nat → Nat) (depth : Nat) : NamedFormula → NamedFormula
  | .imp p q => .imp (standardize names depth p) (standardize names depth q)
  | .all x p => .all (names depth) ((standardize names (depth + 1) p).changeFree x (names depth))
  | p => p

theorem standardized_binders {f : NamedFormula} {names : Nat → Nat} {depth a : Nat}
    (member : a ∈ (f.standardize names depth).binders) :
    ∃ i ≥ depth, a = names i := by
  induction f generalizing depth with
  | imp p q ihP ihQ =>
    rcases List.mem_append.mp member with left | right
    · exact ihP left
    · exact ihQ right
  | all x p ih =>
    simp only [standardize, binders, changeFree_binders, List.mem_cons] at member
    rcases member with here | later
    · exact ⟨depth, le_rfl, here⟩
    · obtain ⟨i, le, eq⟩ := ih later
      exact ⟨i, by omega, eq⟩
  | _ => simp [standardize, binders] at member

theorem standardized_labels {f : NamedFormula} {names : Nat → Nat} {depth a : Nat}
    (member : a ∈ (f.standardize names depth).labels) :
    a ∈ f.labels ∨ ∃ i ≥ depth, a = names i := by
  induction f generalizing depth with
  | imp p q ihP ihQ =>
    rcases List.mem_append.mp member with left | right
    · exact (ihP left).elim (fun h => .inl (List.mem_append_left _ h)) Or.inr
    · exact (ihQ right).elim (fun h => .inl (List.mem_append_right _ h)) Or.inr
  | all x p ih =>
    simp only [standardize, labels, List.mem_cons] at member
    rcases member with here | later
    · exact .inr ⟨depth,le_rfl,here⟩
    · rcases mem_labels_changeFree later with smaller | here
      · rcases ih smaller with old | ⟨i,deep,eq⟩
        · exact .inl (List.mem_cons_of_mem _ old)
        · exact .inr ⟨i,by omega,eq⟩
      · exact .inr ⟨depth,le_rfl,here⟩
  | _ => exact .inl member

set_option maxHeartbeats 1400000 in
theorem standardize_provable (f : NamedFormula) (names : Nat → Nat) (depth : Nat)
    (distinct : Function.Injective names) (fresh : ∀ i, names i ∉ f.labels) :
    (K).Prov ((K).iff f.code (f.standardize names depth).code) := by
  induction f generalizing depth with
  | imp p q ihP ihQ =>
    have newP := ihP depth fun i h => fresh i (List.mem_append_left _ h)
    have newQ := ihQ depth fun i h => fresh i (List.mem_append_right _ h)
    exact (Logic.Ctx.impCongr (.thm newP) (.thm newQ)).empty
  | all x p ih =>
    let body := p.standardize names (depth+1)
    have compiled := ih (depth+1) fun i h => fresh i (List.mem_cons_of_mem _ h)
    have oldNotBound : x ∉ body.binders := by
      intro used
      obtain ⟨i,_,eq⟩ := standardized_binders used
      exact fresh i (eq ▸ List.mem_cons_self)
    have newFresh : names depth ∉ body.labels := by
      intro used
      rcases standardized_labels used with old | ⟨i, deep, same⟩
      · exact fresh depth (List.mem_cons_of_mem _ old)
      · have atDepth := distinct same
        omega
    have oldNeNew : x ≠ names depth := fun eq => fresh depth (eq ▸ List.mem_cons_self)
    have preserves : (K).Ctx [] ((K).iff (.all x p : NamedFormula).code (.all x body : NamedFormula).code) :=
      Logic.Ctx.allCongr x (fun _ h => (List.not_mem_nil h).elim) (.thm compiled)
    exact (preserves.iffTrans (.thm (body.renameBinder oldNeNew newFresh oldNotBound))).empty
  | _ => exact (Logic.Ctx.iffRefl _).empty

/-- Read free names through an environment and choose binder names by depth. -/
def relabel (names : Nat → Nat) (depth : Nat) (env : Nat → Nat) : NamedFormula → NamedFormula
  | .truth => .truth
  | .falsity => .falsity
  | .mem x y => .mem (env x) (env y)
  | .equal x y => .equal (env x) (env y)
  | .imp p q => .imp (relabel names depth env p) (relabel names depth env q)
  | .all x p => .all (names depth) (relabel names (depth+1) (assign env x (names depth)) p)

theorem relabel_congr {names : Nat → Nat} {d : Nat} {s t : Nat → Nat} (f : NamedFormula)
    (agrees : ∀ i ∈ f.labels, s i = t i) : f.relabel names d s = f.relabel names d t := by
  induction f generalizing d s t with
  | truth | falsity => rfl
  | mem x y | equal x y =>
    simp only [relabel]
    rw [agrees x (by simp [labels]), agrees y (by simp [labels])]
  | imp p q ihP ihQ =>
    simp only [relabel]
    rw [ihP (fun i h => agrees i (List.mem_append_left _ h)),
      ihQ (fun i h => agrees i (List.mem_append_right _ h))]
  | all x p ih =>
    simp only [relabel]
    apply congrArg (NamedFormula.all (names d))
    apply ih
    intro i h
    have before := agrees i (List.mem_cons_of_mem _ h)
    unfold assign
    rw [before]

theorem relay_changeFree {names env : Nat → Nat} {d x y : Nat}
    (different : ∀ i ≥ d, names i ≠ x) (f : NamedFormula) :
    (f.relabel names d env).changeFree x y =
      f.relabel names d (fun i => if env i = x then y else env i) := by
  induction f generalizing d env with
  | imp p q ihP ihQ => simp [relabel, changeFree, ihP different, ihQ different]
  | all a p ih =>
    have apart := different d le_rfl
    have deep : ∀ i ≥ d+1, names i ≠ x := fun i hi => different i (by omega)
    simp only [relabel, changeFree, apart, ite_false]
    rw [ih deep]
    congr 2
    funext b
    by_cases tagged : b = a <;> simp [assign, tagged, apart]
  | _ => rfl

theorem standardize_eq_relabel (f : NamedFormula) (names : Nat → Nat) (d : Nat)
    (fresh : ∀ i, names i ∉ f.labels) :
    f.standardize names d = f.relabel names d id := by
  induction f generalizing d with
  | imp p q ihP ihQ =>
    simp only [standardize, relabel]
    rw [ihP _ (fun i h => fresh i (List.mem_append_left _ h)),
      ihQ _ (fun i h => fresh i (List.mem_append_right _ h))]
  | all x p ih =>
    have differs (i : Nat) : names i ≠ x := fun eq => fresh i (eq ▸ List.mem_cons_self)
    simp only [standardize, relabel]
    rw [ih _ (fun i h => fresh i (List.mem_cons_of_mem _ h)),
      relay_changeFree (fun i _ => differs i)]
    rfl
  | _ => rfl

end NamedFormula
end I0451.Logic
