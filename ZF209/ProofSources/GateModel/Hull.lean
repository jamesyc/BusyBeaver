module
public import Foundation.FirstOrder.SetTheory.Basic.Model
@[expose] public section
/-! # Structures satisfying the machine's gate

The machine's calculus has a single set-theoretic axiom schema, the pointed
gate. In a structure, its instances say that every definable relation has a
pointed Scott hull. This file states that property and derives the literal
constructions used by the marked interpretation. No ZF axiom is assumed. -/
namespace ZF209.GateModel
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V]

/-- `C` is a pointed hull of `R` started at `(u₀, v₀)`: it contains `v₀` when
`R u₀ v₀`, every member has an `R`-predecessor, and every subset of a member
that has an `R`-witness has one inside `C`. -/
def IsHull (R : V → V → Prop) (u₀ v₀ C : V) : Prop :=
  (R u₀ v₀ → v₀ ∈ C) ∧
    ∀ z ∈ C, (∃ p, R p z) ∧ ∀ u, u ⊆ z → (∃ v, R u v) → ∃ w ∈ C, R u w

variable (V) in
/-- Every relation definable with parameters has pointed hulls. -/
class GateHull : Prop where
  hull : ∀ R : V → V → Prop, (ℒₛₑₜ-relation R) → ∀ u₀ v₀ : V, ∃ C, IsHull R u₀ v₀ C

lemma IsHull.start {R : V → V → Prop} {u₀ v₀ C : V} (h : IsHull R u₀ v₀ C)
    (hr : R u₀ v₀) : v₀ ∈ C := h.1 hr

lemma IsHull.pred {R : V → V → Prop} {u₀ v₀ C : V} (h : IsHull R u₀ v₀ C)
    {z : V} (hz : z ∈ C) : ∃ p, R p z := (h.2 z hz).1

lemma IsHull.cover {R : V → V → Prop} {u₀ v₀ C : V} (h : IsHull R u₀ v₀ C)
    {z u : V} (hz : z ∈ C) (hu : u ⊆ z) {v : V} (hv : R u v) : ∃ w ∈ C, R u w :=
  (h.2 z hz).2 u hu ⟨v, hv⟩

/-- `s` is a literal singleton of `w`. -/
def IsSingletonOf (s w : V) : Prop := ∀ y, y ∈ s ↔ y = w

instance IsSingletonOf.definable : ℒₛₑₜ-relation (IsSingletonOf (V := V)) := by
  unfold IsSingletonOf; definability

lemma IsSingletonOf.mem_self {s w : V} (h : IsSingletonOf s w) : w ∈ s := (h w).mpr rfl

lemma IsSingletonOf.eq {s w y : V} (h : IsSingletonOf s w) (hy : y ∈ s) : y = w := (h y).mp hy

variable [Nonempty V] [GateHull V]

/-- An object with no members. -/
lemma exists_isEmpty : ∃ e : V, SetTheory.IsEmpty e := by
  obtain ⟨C, hC⟩ := GateHull.hull (fun _ _ : V => False) (by definability)
    (Classical.arbitrary V) (Classical.arbitrary V)
  exact ⟨C, fun z hz => (hC.pred hz).elim fun _ h => h⟩

omit [Nonempty V] in
/-- Literal singletons. -/
lemma exists_singleton (a : V) : ∃ s : V, IsSingletonOf s a := by
  obtain ⟨C, hC⟩ := GateHull.hull (fun _ v : V => v = a) (by definability) a a
  refine ⟨C, fun x => ⟨fun hx => ?_, fun hx => hx ▸ hC.start rfl⟩⟩
  obtain ⟨_, hp⟩ := hC.pred hx
  exact hp

/-- Literal unordered pairs. The empty object lies below `a`, which forces `b`. -/
lemma exists_pair (a b : V) : ∃ s : V, ∀ x, x ∈ s ↔ x = a ∨ x = b := by
  obtain ⟨e, he⟩ := exists_isEmpty (V := V)
  obtain ⟨sa, hsa⟩ := exists_singleton a
  let R : V → V → Prop :=
    fun u v => (¬SetTheory.IsEmpty u ∧ v = a) ∨ (SetTheory.IsEmpty u ∧ v = b)
  have hsa' : ¬SetTheory.IsEmpty sa := fun h => h a hsa.mem_self
  obtain ⟨C, hC⟩ := GateHull.hull R (by definability) sa a
  have ha : a ∈ C := hC.start (Or.inl ⟨hsa', rfl⟩)
  have heu : e ⊆ a := fun x hx => (he x hx).elim
  refine ⟨C, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨_, hp | hp⟩ := hC.pred hx
    · exact Or.inl hp.2
    · exact Or.inr hp.2
  · rintro (rfl | rfl)
    · exact ha
    · obtain ⟨w, hw, hw' | hw'⟩ := hC.cover ha heu (v := x) (Or.inr ⟨he, rfl⟩)
      · exact (hw'.1 he).elim
      · exact hw'.2 ▸ hw

section Marked
variable {e : V} (he : SetTheory.IsEmpty e)
include he

omit [Nonempty V] in
/-- A literal enumerator of the members of `x`: an object not containing `e` that
holds a singleton of every member of `x`. Its subsets `{{w}}` index the members. -/
lemma exists_enumerator (x : V) :
    ∃ D : V, e ∉ D ∧ ∀ w ∈ x, ∃ s ∈ D, IsSingletonOf s w := by
  by_cases hx : x = e
  · refine ⟨x, hx ▸ he e, fun w hw => (he w (hx ▸ hw)).elim⟩
  let R : V → V → Prop := fun u v =>
    (u = x ∧ v = x) ∨ ∃ w ∈ x, IsSingletonOf u w ∧ IsSingletonOf v w
  obtain ⟨C, hC⟩ := GateHull.hull R (by definability) x x
  have hxC : x ∈ C := hC.start (Or.inl ⟨rfl, rfl⟩)
  refine ⟨C, fun heC => ?_, fun w hw => ?_⟩
  · obtain ⟨p, hp⟩ := hC.pred heC
    rcases hp with h | ⟨w, _, _, hs⟩
    · exact hx h.2.symm
    · exact he w hs.mem_self
  · obtain ⟨s, hs⟩ := exists_singleton w
    have hsx : s ⊆ x := fun y hy => (hs.eq hy) ▸ hw
    obtain ⟨v, hv, hR⟩ := hC.cover hxC hsx (v := s) (Or.inr ⟨w, hw, hs, hs⟩)
    rcases hR with h | ⟨w', _, hsw', hvw'⟩
    · exact ⟨v, hv, h.2 ▸ h.1 ▸ hs⟩
    · have hww : w = w' := hsw'.eq hs.mem_self
      exact ⟨v, hv, hww ▸ hvw'⟩

omit [Nonempty V] in
/-- Marked collection through a given enumerator `D` of `z₀`. The result is
marked; besides `D` and `e`, its members are marked `P`-witnesses for members of
`z₀`, and every member of `z₀` with a marked witness has one in it. -/
lemma collect_with (z₀ D : V) (heD : e ∉ D) (hD : ∀ w ∈ z₀, ∃ s ∈ D, IsSingletonOf s w)
    (P : V → V → Prop) (hP : ℒₛₑₜ-relation P) :
    ∃ C : V, e ∈ C ∧ (∀ v ∈ C, v = D ∨ v = e ∨ (e ∈ v ∧ ∃ w ∈ z₀, P w v)) ∧
      ∀ w ∈ z₀, (∃ v, e ∈ v ∧ P w v) → ∃ v ∈ C, e ∈ v ∧ P w v := by
  obtain ⟨u₀, hu₀⟩ := exists_singleton e
  let R : V → V → Prop := fun u v =>
    (u = u₀ ∧ v = D) ∨ (SetTheory.IsEmpty u ∧ v = e) ∨
      ∃ w ∈ z₀, (∃ s, IsSingletonOf u s ∧ IsSingletonOf s w) ∧ e ∈ v ∧ P w v
  obtain ⟨C, hC⟩ := GateHull.hull R (by definability) u₀ D
  have hDC : D ∈ C := hC.start (Or.inl ⟨rfl, rfl⟩)
  have hu₀ne : ¬SetTheory.IsEmpty u₀ := fun h => h e hu₀.mem_self
  have heD' : e ⊆ D := fun y hy => (he y hy).elim
  refine ⟨C, ?_, fun v hv => ?_, fun w hw hex => ?_⟩
  · obtain ⟨w, hw, hR⟩ := hC.cover hDC heD' (v := e) (Or.inr (Or.inl ⟨he, rfl⟩))
    rcases hR with h | h | ⟨_, _, ⟨s, hs, _⟩, _⟩
    · exact absurd (h.1 ▸ he) hu₀ne
    · exact h.2 ▸ hw
    · exact (he s hs.mem_self).elim
  · obtain ⟨p, hR⟩ := hC.pred hv
    rcases hR with h | h | ⟨w, hw, _, hev, hp⟩
    · exact Or.inl h.2
    · exact Or.inr (Or.inl h.2)
    · exact Or.inr (Or.inr ⟨hev, w, hw, hp⟩)
  · obtain ⟨v, hev, hp⟩ := hex
    obtain ⟨s, hsD, hs⟩ := hD w hw
    obtain ⟨u, hu⟩ := exists_singleton s
    have huD : u ⊆ D := fun y hy => (hu.eq hy) ▸ hsD
    obtain ⟨v', hv', hR⟩ :=
      hC.cover hDC huD (v := v) (Or.inr (Or.inr ⟨w, hw, ⟨s, hu, hs⟩, hev, hp⟩))
    rcases hR with h | h | ⟨w', _, ⟨s', hus', hs'w'⟩, hev', hp'⟩
    · -- `u = u₀` would make `s = e`, but `e` is empty and `s` is not
      have hse : s = e := hu₀.eq (h.1 ▸ hu.mem_self)
      exact (he w (hse ▸ hs.mem_self)).elim
    · exact (h.1 s hu.mem_self).elim
    · have hss' : s = s' := hus'.eq hu.mem_self
      have hww' : w = w' := hs'w'.eq (hss' ▸ hs.mem_self)
      exact ⟨v', hv', hev', hww' ▸ hp'⟩

omit [Nonempty V] in
/-- Marked collection. For a definable `P`, there is a marked object whose marked
members are `P`-witnesses for members of `z₀`, containing a marked witness for
every member of `z₀` that has one. Its other members do not contain `e`. -/
lemma collect (z₀ : V) (P : V → V → Prop) (hP : ℒₛₑₜ-relation P) :
    ∃ C : V, e ∈ C ∧ (∀ v ∈ C, e ∈ v → ∃ w ∈ z₀, P w v) ∧
      ∀ w ∈ z₀, (∃ v, e ∈ v ∧ P w v) → ∃ v ∈ C, e ∈ v ∧ P w v := by
  obtain ⟨D, heD, hD⟩ := exists_enumerator he z₀
  obtain ⟨C, heC, hb, hc⟩ := collect_with he z₀ D heD hD P hP
  refine ⟨C, heC, fun v hv hev => ?_, hc⟩
  rcases hb v hv with rfl | rfl | ⟨_, h⟩
  · exact (heD hev).elim
  · exact (he v hev).elim
  · exact h

omit [Nonempty V] in
/-- `x` together with `e` and `D`, literally. -/
lemma exists_plus (x D : V) (hD : ∀ w ∈ x, ∃ s ∈ D, IsSingletonOf s w) :
    ∃ X : V, D ∈ X ∧ e ∈ X ∧ (∀ w ∈ x, w ∈ X) ∧ ∀ v ∈ X, v = D ∨ v = e ∨ v ∈ x := by
  obtain ⟨u₀, hu₀⟩ := exists_singleton e
  let R : V → V → Prop := fun u v =>
    (u = u₀ ∧ v = D) ∨ (SetTheory.IsEmpty u ∧ v = e) ∨
      ((∃ s, IsSingletonOf u s ∧ IsSingletonOf s v) ∧ v ∈ x)
  obtain ⟨C, hC⟩ := GateHull.hull R (by definability) u₀ D
  have hDC : D ∈ C := hC.start (Or.inl ⟨rfl, rfl⟩)
  have hu₀ne : ¬SetTheory.IsEmpty u₀ := fun h => h e hu₀.mem_self
  have heD' : e ⊆ D := fun y hy => (he y hy).elim
  refine ⟨C, hDC, ?_, fun w hw => ?_, fun v hv => ?_⟩
  · obtain ⟨w, hw, hR⟩ := hC.cover hDC heD' (v := e) (Or.inr (Or.inl ⟨he, rfl⟩))
    rcases hR with h | h | ⟨⟨s, hs, _⟩, _⟩
    · exact absurd (h.1 ▸ he) hu₀ne
    · exact h.2 ▸ hw
    · exact (he s hs.mem_self).elim
  · obtain ⟨s, hsD, hs⟩ := hD w hw
    obtain ⟨u, hu⟩ := exists_singleton s
    have huD : u ⊆ D := fun y hy => (hu.eq hy) ▸ hsD
    obtain ⟨v', hv', hR⟩ := hC.cover hDC huD (v := w) (Or.inr (Or.inr ⟨⟨s, hu, hs⟩, hw⟩))
    rcases hR with h | h | ⟨⟨s', hus', hs'v'⟩, _⟩
    · have hse : s = e := hu₀.eq (h.1 ▸ hu.mem_self)
      exact (he w (hse ▸ hs.mem_self)).elim
    · exact (h.1 s hu.mem_self).elim
    · have hss' : s = s' := hus'.eq hu.mem_self
      have : w = v' := (hs'v'.eq (hss' ▸ hs.mem_self))
      exact this ▸ hv'
  · obtain ⟨p, hR⟩ := hC.pred hv
    rcases hR with h | h | ⟨_, hvx⟩
    · exact Or.inl h.2
    · exact Or.inr (Or.inl h.2)
    · exact Or.inr (Or.inr hvx)

omit [Nonempty V] in
/-- A literal power object: it contains every subset of `X` that exists. -/
lemma exists_powerset (X : V) : ∃ P : V, ∀ u, u ⊆ X → u ∈ P := by
  obtain ⟨C, hC⟩ := GateHull.hull (fun u v : V => v = u ∧ u ⊆ X) (by definability) X X
  have hXC : X ∈ C := hC.start ⟨rfl, subset_refl X⟩
  refine ⟨C, fun u hu => ?_⟩
  obtain ⟨w, hw, rfl, _⟩ := hC.cover hXC hu (v := u) ⟨rfl, hu⟩
  exact hw

omit [Nonempty V] in
/-- A transitive object containing `x`. Each singleton below a member forces its
element, so the hull is closed under members. -/
lemma exists_transitive_superset (x : V) :
    ∃ T : V, x ∈ T ∧ ∀ z ∈ T, ∀ w ∈ z, w ∈ T := by
  obtain ⟨u₀, hu₀⟩ := exists_singleton e
  let R : V → V → Prop := fun u v => (u = e ∧ v = x) ∨ IsSingletonOf u v
  obtain ⟨C, hC⟩ := GateHull.hull R (by definability) e x
  refine ⟨C, hC.start (Or.inl ⟨rfl, rfl⟩), fun z hz w hw => ?_⟩
  obtain ⟨s, hs⟩ := exists_singleton w
  have hsz : s ⊆ z := fun y hy => (hs.eq hy) ▸ hw
  obtain ⟨v, hv, h | h⟩ := hC.cover hz hsz (v := w) (Or.inr hs)
  · exact (he w (h.1 ▸ hs.mem_self)).elim
  · exact (h.eq hs.mem_self) ▸ hv

omit [Nonempty V] in
/-- Marked selection through a given enumerator `D`: besides `D` and `e`, the
members are exactly the marked members of `z₀` satisfying `φ`. -/
lemma select_with (z₀ D : V) (heD : e ∉ D) (hD : ∀ w ∈ z₀, ∃ s ∈ D, IsSingletonOf s w)
    (φ : V → Prop) (hφ : ℒₛₑₜ-predicate φ) :
    ∃ C : V, e ∈ C ∧ (∀ v ∈ C, v = D ∨ v = e ∨ (v ∈ z₀ ∧ e ∈ v ∧ φ v)) ∧
      ∀ v ∈ z₀, e ∈ v → φ v → v ∈ C := by
  obtain ⟨C, heC, hb, hc⟩ :=
    collect_with he z₀ D heD hD (fun w v => v = w ∧ φ w) (by definability)
  refine ⟨C, heC, fun v hv => ?_, fun v hv hev hφv => ?_⟩
  · rcases hb v hv with h | h | ⟨hev, w, hw, rfl, hφw⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨hw, hev, hφw⟩)
  · obtain ⟨v', hv', _, rfl, _⟩ := hc v hv ⟨v, hev, rfl, hφv⟩
    exact hv'

omit [Nonempty V] in
/-- Marked selection: for a definable `φ`, a marked object whose marked members are
exactly the marked members of `z₀` satisfying `φ`. -/
lemma select (z₀ : V) (φ : V → Prop) (hφ : ℒₛₑₜ-predicate φ) :
    ∃ C : V, e ∈ C ∧ ∀ v, (v ∈ C ∧ e ∈ v) ↔ (v ∈ z₀ ∧ e ∈ v ∧ φ v) := by
  obtain ⟨C, heC, hsound, hcomp⟩ := collect he z₀ (fun w v => v = w ∧ φ w) (by definability)
  refine ⟨C, heC, fun v => ⟨fun ⟨hv, hev⟩ => ?_, fun ⟨hv, hev, hφv⟩ => ?_⟩⟩
  · obtain ⟨w, hw, rfl, hφw⟩ := hsound v hv hev
    exact ⟨hw, hev, hφw⟩
  · obtain ⟨v', hv', _, rfl, _⟩ := hcomp v hv ⟨v, hev, rfl, hφv⟩
    exact ⟨hv', hev⟩

end Marked

end ZF209.GateModel
