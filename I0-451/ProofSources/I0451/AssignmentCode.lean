module
public import I0451.Identity

/-! The set-coded assignments in the compressed Berkeley sentence.
These lemmas use extensionality, unordered pairing, and the finite-update
instance of Separation and Union. -/

@[expose] public section
namespace I0451.AssignmentCode

variable {V : Type}

/-- The set of all subsets of `{x,y}` containing `x`, the Kuratowski pair. -/
def Pair (E : V → V → Prop) (p x y : V) : Prop :=
  ∀ s, E s p ↔ E x s ∧ ∀ z, E z s → z = x ∨ z = y

/-- The evaluation relation ignores members which are not pair codes. -/
def At (E : V → V → Prop) (g x y : V) : Prop :=
  ∃ p, E p g ∧ Pair E p x y

/-- The graph object lies in the power set of the power set of the power
set of the domain. -/
def Bounded (E : V → V → Prop) (g domain : V) : Prop :=
  ∀ p, E p g → ∀ a, E a p → ∀ x, E x a → E x domain

/-- The asymmetric agreement test used by the emitted formula. -/
def Agree (E : V → V → Prop) (i g h : V) : Prop :=
  ∀ p, E p g → ¬ E p h → ∀ a, E a p → E i a

/-- Set operations needed for assignment codes. The update law is for
one specific definable predicate. -/
structure SetOperations (E : V → V → Prop) : Prop where
  extensionality : ∀ a b, (∀ x, E x a ↔ E x b) → a = b
  unorderedPair : ∀ x y, ∃ a, ∀ z, E z a ↔ z = x ∨ z = y
  update : ∀ g old new, ∃ h, ∀ p, E p h ↔ (E p g ∧ p ≠ old) ∨ p = new

theorem SetOperations.pair_exists {E : V → V → Prop} (ops : SetOperations E)
    (x y : V) : ∃ p, Pair E p x y := by
  classical
  obtain ⟨s, hs⟩ := ops.unorderedPair x x
  obtain ⟨a, ha⟩ := ops.unorderedPair x y
  obtain ⟨p, hp⟩ := ops.unorderedPair s a
  refine ⟨p, fun t => ?_⟩
  rw [hp]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨(hs x).2 (Or.inl rfl), fun z zmem => Or.inl (((hs z).1 zmem).elim id id)⟩
    · exact ⟨(ha x).2 (Or.inl rfl), fun z => (ha z).1⟩
  · rintro ⟨xmem, bound⟩
    by_cases ymem : E y t
    · right
      apply ops.extensionality
      intro z
      rw [ha]
      exact ⟨bound z, fun h => h.elim (fun e => e ▸ xmem) (fun e => e ▸ ymem)⟩
    · left
      apply ops.extensionality
      intro z
      rw [hs]
      exact ⟨fun zmem => Or.inl ((bound z zmem).resolve_right (fun e => ymem (e ▸ zmem))),
        fun h => h.elim (fun e => e ▸ xmem) (fun e => e ▸ xmem)⟩

theorem Pair.key {E : V → V → Prop} (ops : SetOperations E)
    {p x y a b : V} (left : Pair E p x y) (right : Pair E p a b) : x = a := by
  obtain ⟨s, hs⟩ := ops.unorderedPair x x
  have sx : E s p :=
    (left s).2 ⟨(hs x).2 (Or.inl rfl), fun z zm => Or.inl (((hs z).1 zm).elim id id)⟩
  exact (((hs a).1 ((right s).1 sx).1).elim id id).symm

theorem Pair.components {E : V → V → Prop} (ops : SetOperations E)
    {p x y a b : V} (left : Pair E p x y) (right : Pair E p a b) : x = a ∧ y = b := by
  have key := left.key ops right
  subst a
  obtain ⟨s, hs⟩ := ops.unorderedPair x y
  have sPair := (left s).2 ⟨(hs x).2 (Or.inl rfl), fun z => (hs z).1⟩
  have ycases := ((right s).1 sPair).2 y ((hs y).2 (Or.inr rfl))
  rcases ycases with yx | yb
  · obtain ⟨t, ht⟩ := ops.unorderedPair x b
    have tPair := (right t).2 ⟨(ht x).2 (Or.inl rfl), fun z => (ht z).1⟩
    have bcases := ((left t).1 tPair).2 b ((ht b).2 (Or.inr rfl))
    exact ⟨rfl, bcases.elim (fun bx => yx.trans bx.symm) Eq.symm⟩
  · exact ⟨rfl, yb⟩

theorem Pair.unique {E : V → V → Prop} (ops : SetOperations E)
    {p q x y : V} (left : Pair E p x y) (right : Pair E q x y) : p = q :=
  ops.extensionality p q (fun s => (left s).trans (right s).symm)

theorem Pair.in_domain {E : V → V → Prop} (ops : SetOperations E)
    {p x y g d : V} (pair : Pair E p x y) (member : E p g) (bound : Bounded E g d) :
    E x d ∧ E y d := by
  obtain ⟨a, ha⟩ := ops.unorderedPair x y
  have belongs := (pair a).2 ⟨(ha x).2 (Or.inl rfl), fun z => (ha z).1⟩
  exact ⟨bound p member a belongs x ((ha x).2 (Or.inl rfl)),
    bound p member a belongs y ((ha y).2 (Or.inr rfl))⟩

abbrev Domain (E : V → V → Prop) (d : V) := {x : V // E x d}

/-- A bounded object encodes the given total function on the domain. -/
structure Encodes (E : V → V → Prop) (d g : V)
    (f : Domain E d → Domain E d) : Prop where
  bounded : Bounded E g d
  at_iff : ∀ x : Domain E d, ∀ y : V, At E g x.val y ↔ (f x).val = y

theorem Agree.preserves {E : V → V → Prop} {d g h : V}
    (ops : SetOperations E) {f k : Domain E d → Domain E d}
    (fCode : Encodes E d g f) (kCode : Encodes E d h k)
    {i x : Domain E d} (agree : Agree E i.val g h) (other : x ≠ i) :
    k x = f x := by
  obtain ⟨p, belongs, pair⟩ := (fCode.at_iff x (f x).val).2 rfl
  have kept : E p h := by
    apply Classical.byContradiction
    intro gone
    obtain ⟨s, hs⟩ := ops.unorderedPair x.val x.val
    have inside := (pair s).2 ⟨(hs x.val).2 (Or.inl rfl),
      fun z zm => Or.inl (((hs z).1 zm).elim id id)⟩
    have key := (hs i.val).1 (agree p belongs gone s inside)
    exact other (Subtype.ext (key.elim Eq.symm Eq.symm))
  exact Subtype.ext ((kCode.at_iff x (f x).val).1 ⟨p, kept, pair⟩)

/-- Changing a coordinate replaces exactly the corresponding canonical
pair. All other objects, including non-pair members, can be retained. -/
theorem Encodes.replace [DecidableEq V] {E : V → V → Prop} {d g : V}
    (ops : SetOperations E) {f : Domain E d → Domain E d} (old : Encodes E d g f)
    (i y : Domain E d) :
    ∃ h, Encodes E d h (Identity.replace f i y) ∧ Agree E i.val g h := by
  classical
  obtain ⟨p, belongs, pair⟩ := (old.at_iff i (f i).val).2 rfl
  obtain ⟨new, newPair⟩ := ops.pair_exists i.val y.val
  obtain ⟨h, hh⟩ := ops.update g p new
  refine ⟨h, ⟨?_, ?_⟩, ?_⟩
  · intro code member a am z zm
    rcases (hh code).1 member with ⟨kept, _⟩ | same
    · exact old.bounded code kept a am z zm
    · subst code
      exact (((newPair a).1 am).2 z zm).elim
        (fun eq => eq ▸ i.property) (fun eq => eq ▸ y.property)
  · intro x v
    by_cases same : x = i
    · subst x
      simp only [Identity.replace]
      constructor
      · rintro ⟨code, member, qPair⟩
        rcases (hh code).1 member with ⟨kept, different⟩ | isNew
        · have equal := (old.at_iff i v).1 ⟨code, kept, qPair⟩
          subst v
          exact False.elim (different (qPair.unique ops pair))
        · subst code
          exact (newPair.components ops qPair).2
      · intro eq
        subst v
        exact ⟨new, (hh new).2 (Or.inr rfl), newPair⟩
    · simp only [Identity.replace, ite_eq_right same]
      constructor
      · rintro ⟨code, member, qPair⟩
        rcases (hh code).1 member with ⟨kept, _⟩ | isNew
        · exact (old.at_iff x v).1 ⟨code, kept, qPair⟩
        · subst code
          exact False.elim (same (Subtype.ext (qPair.key ops newPair)))
      · intro holds
        obtain ⟨code, kept, qPair⟩ := (old.at_iff x v).2 holds
        have different : code ≠ p := by
          intro eq
          subst code
          exact same (Subtype.ext (qPair.key ops pair))
        exact ⟨code, (hh code).2 (Or.inl ⟨kept, different⟩), qPair⟩
  · intro code member missing a am
    have erased : code = p := by
      apply Classical.byContradiction
      intro different
      exact missing ((hh code).2 (Or.inl ⟨member, different⟩))
    subst code
    exact ((pair a).1 am).1

/-- The formula's bounded totality and uniqueness assertion. -/
def IsMap (E : V → V → Prop) (d g : V) : Prop :=
  Bounded E g d ∧ ∀ x : Domain E d, ∃ y, At E g x.val y ∧
    ∀ z, At E g x.val z → z = y

theorem is_map_iff_encodes {E : V → V → Prop} {d g : V} (ops : SetOperations E) :
    IsMap E d g ↔ ∃ f, Encodes E d g f := by
  constructor
  · rintro ⟨bound, total⟩
    let value (x : Domain E d) : V := Classical.choose (total x)
    have atValue (x : Domain E d) : At E g x.val (value x) :=
      (Classical.choose_spec (total x)).1
    have inDomain (x : Domain E d) : E (value x) d := by
      obtain ⟨p, member, pair⟩ := atValue x
      exact (pair.in_domain ops member bound).2
    refine ⟨fun x => ⟨value x, inDomain x⟩, bound, fun x y => ?_⟩
    exact ⟨fun hy => ((Classical.choose_spec (total x)).2 y hy).symm,
      fun hy => hy ▸ atValue x⟩
  · rintro ⟨f, code⟩
    exact ⟨code.bounded, fun x => ⟨(f x).val, (code.at_iff x _).2 rfl,
      fun z hz => ((code.at_iff x z).1 hz).symm⟩⟩

/-- The relative truth-set closure clauses of the compressed formula.
Relations in the family are measured on the permitted codes in `U`. -/
structure TruthSets (E : V → V → Prop) (d U C : V) : Prop where
  codes : ∀ g, E g U ↔ IsMap E d g
  atom : ∀ i k : Domain E d, ∃ R, E R C ∧ ∀ g, E g U →
    (E g R ↔ ∀ x y, At E g i.val x → At E g k.val y → E x y)
  close : ∀ (i : Domain E d) R S, E R C → E S C →
    ∃ W, E W C ∧ ∀ g, E g U →
      (E g W ↔ ∃ u, E u U ∧ (E u R → E u S) ∧ Agree E i.val g u)

end I0451.AssignmentCode
