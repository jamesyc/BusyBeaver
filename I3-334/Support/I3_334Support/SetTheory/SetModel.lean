module
public import I3_334Support.SetTheory.Definable
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic Manifest

variable {A V : Type} {M : Algebra A}

namespace SetContext

variable (N : SetContext M V)

def Subset (a b : V) : Prop := ∀ x, N.mem x a → N.mem x b

def NonemptySet (a : V) : Prop := ∃ x, N.mem x a

def Transitive (a : V) : Prop := ∀ x, N.mem x a → N.Subset x a

theorem ext (a b : V) (membership : ∀ x, N.mem x a ↔ N.mem x b) : a = b :=
  N.extensional a b membership

theorem subset_refl (x : V) : N.Subset x x := fun _ h => h
theorem subset_trans {x y z : V} (h : N.Subset x y) (j : N.Subset y z) : N.Subset x z :=
  fun a ha => j a (h a ha)
theorem subset_antisymm {x y : V} (h : N.Subset x y) (j : N.Subset y x) : x = y :=
  N.ext x y fun z => ⟨h z, j z⟩

include N in
theorem exists_point : Nonempty V := N.inhabited

theorem empty_exists : ∃ u, Internal.Empty N.mem u := N.emptySet

noncomputable def empty : V := Classical.choose N.empty_exists

theorem empty_mem (x : V) : ¬N.mem x N.empty := Classical.choose_spec N.empty_exists x

theorem empty_unique (a : V) : Internal.Empty N.mem a ↔ a = N.empty := by
  constructor
  · intro h
    exact N.ext a N.empty fun x => ⟨fun hx => (h x hx).elim, fun hx => (N.empty_mem x hx).elim⟩
  · rintro rfl
    exact N.empty_mem

theorem exists_pair (a b : V) : ∃ p, Internal.Pair N.mem a b p := N.pairs a b

noncomputable def pair (a b : V) : V := Classical.choose (N.exists_pair a b)

theorem mem_pair (a b x : V) : N.mem x (N.pair a b) ↔ x = a ∨ x = b :=
  Classical.choose_spec (N.exists_pair a b) x

noncomputable def singleton (a : V) : V := N.pair a a

theorem mem_singleton (a x : V) : N.mem x (N.singleton a) ↔ x = a := by
  simp [singleton, mem_pair]

theorem exists_power (a : V) : ∃ p, ∀ x, N.mem x p ↔ N.Subset x a :=
  N.powerSet a

noncomputable def power (a : V) : V := Classical.choose (N.exists_power a)

theorem mem_power (a x : V) : N.mem x (N.power a) ↔ N.Subset x a :=
  Classical.choose_spec (N.exists_power a) x

theorem exists_union (a : V) : ∃ u, ∀ x, N.mem x u ↔ ∃ y, N.mem y a ∧ N.mem x y :=
  N.unionSet a

noncomputable def union (a : V) : V := Classical.choose (N.exists_union a)

theorem mem_union (a x : V) : N.mem x (N.union a) ↔ ∃ y, N.mem y a ∧ N.mem x y :=
  Classical.choose_spec (N.exists_union a) x

noncomputable def union₂ (a b : V) : V := N.union (N.pair a b)

theorem mem_union₂ (a b x : V) : N.mem x (N.union₂ a b) ↔ N.mem x a ∨ N.mem x b := by
  simp only [union₂, mem_union, mem_pair]
  constructor
  · rintro ⟨y, rfl | rfl, h⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩

noncomputable def succ (a : V) : V := N.union₂ a (N.singleton a)

theorem mem_succ (a x : V) : N.mem x (N.succ a) ↔ N.mem x a ∨ x = a := by
  rw [succ, mem_union₂, mem_singleton]

theorem exists_diff (a b : V) : ∃ d, ∀ x, N.mem x d ↔ N.mem x a ∧ ¬N.mem x b :=
  N.separate [] (Definable.not (Definable.atom (S := N.square) (n := 2) (M.constant .E) (i := 0) (j := 1)
    (by decide) (by decide))) a b

noncomputable def difference (a b : V) : V := Classical.choose (N.exists_diff a b)

theorem mem_difference (a b x : V) : N.mem x (N.difference a b) ↔ N.mem x a ∧ ¬N.mem x b :=
  Classical.choose_spec (N.exists_diff a b) x

theorem exists_inter (a b : V) : ∃ d, ∀ x, N.mem x d ↔ N.mem x a ∧ N.mem x b :=
  N.separate [] (Definable.atom (S := N.square) (n := 2) (M.constant .E) (i := 0) (j := 1) (by decide) (by decide)) a b

noncomputable def inter (a b : V) : V := Classical.choose (N.exists_inter a b)

theorem mem_inter (a b x : V) : N.mem x (N.inter a b) ↔ N.mem x a ∧ N.mem x b :=
  Classical.choose_spec (N.exists_inter a b) x

noncomputable def orderedPair (a b : V) : V := N.pair (N.singleton a) (N.pair a b)

theorem orderedPair_intro (a b : V) : Internal.OrderedPair N.mem a b (N.orderedPair a b) :=
  ⟨N.singleton a, N.pair a b, N.mem_pair _ _, N.mem_pair _ _, N.mem_pair _ _⟩

theorem orderedPair_iff (a b p : V) : Internal.OrderedPair N.mem a b p ↔ p = N.orderedPair a b :=
  ⟨fun h => Internal.orderedPair_unique (N.ext) h (N.orderedPair_intro _ _),
    fun h => h.symm ▸ N.orderedPair_intro _ _⟩

theorem orderedPair_inj {a b c d : V} (h : N.orderedPair a b = N.orderedPair c d) : a = c ∧ b = d :=
  Internal.orderedPair_injective (N.orderedPair_intro a b) (h.symm ▸ N.orderedPair_intro c d)

theorem transempty : N.Transitive N.empty := fun x hx => (N.empty_mem x hx).elim

theorem trans_succ {a : V} (ha : N.Transitive a) : N.Transitive (N.succ a) := by
  intro x hx y hy
  rcases (N.mem_succ a x).mp hx with contained | rfl
  · exact (N.mem_succ a y).mpr (Or.inl (ha x contained y hy))
  · exact (N.mem_succ x y).mpr (Or.inl hy)

theorem trans_inter {a b : V} (ha : N.Transitive a) (hb : N.Transitive b) :
    N.Transitive (N.inter a b) := by
  intro x hx y hy
  have paired := (N.mem_inter _ _ _).mp hx
  exact (N.mem_inter _ _ _).mpr ⟨ha x paired.1 y hy, hb x paired.2 y hy⟩

theorem trans_union {sets : V} (trans : ∀ a, N.mem a sets → N.Transitive a) :
    N.Transitive (N.union sets) := by
  intro x hx y hy
  obtain ⟨a, ha, incl⟩ := (N.mem_union _ _).mp hx
  exact (N.mem_union _ _).mpr ⟨a, ha, trans a ha x incl y hy⟩

end SetContext

namespace Definable

variable {N : SetContext M V} {n i j k : Nat}

theorem mem (hi : i < n) (hj : j < n) :
    N.square.Definable n (fun s => N.mem (s i) (s j)) := atom (M.constant .E) hi hj

theorem subset (hi : i < n) (hj : j < n) :
    N.square.Definable n (fun s => N.Subset (s i) (s j)) :=
  (atom (M.constant .T) hi hj).congr fun s => N.subsetRel (s i) (s j)

theorem transitive (hi : i < n) : N.square.Definable n (fun s => N.Transitive (s i)) := by
  change N.square.Definable n (fun s => ∀ x, N.mem x (s i) → N.Subset x (s i))
  exact boundedAll hi _ (subset (N := N) (n := n + 1) (i := 0) (j := i + 1) (by omega) (by omega))

theorem nonempty (hi : i < n) : N.square.Definable n (fun s => N.NonemptySet (s i)) :=
  ex (mem (i := 0) (j := i + 1) (by omega) (by omega))

theorem empty (hi : i < n) : N.square.Definable n (fun s => Internal.Empty N.mem (s i)) :=
  all (not (mem (i := 0) (j := i + 1) (by omega) (by omega)))

theorem pair (hi : i < n) (hj : j < n) (hk : k < n) :
    N.square.Definable n (fun s => Internal.Pair N.mem (s i) (s j) (s k)) := by
  exact all (iff
    (mem (N := N) (n := n + 1) (i := 0) (j := k + 1) (by omega) (by omega))
    (or (eq (i := 0) (j := i + 1) (by omega) (by omega))
      (eq (i := 0) (j := j + 1) (by omega) (by omega))))

theorem orderedPair (hi : i < n) (hj : j < n) (hk : k < n) :
    N.square.Definable n (fun s => Internal.OrderedPair N.mem (s i) (s j) (s k)) := by
  exact ex (ex (and (pair (N := N) (n := n + 1 + 1) (i := i + 2) (j := i + 2) (k := 1) (by omega) (by omega) (by omega))
    (and (pair (i := i + 2) (j := j + 2) (k := 0) (by omega) (by omega) (by omega))
      (pair (i := 1) (j := 0) (k := k + 2) (by omega) (by omega) (by omega)))))

theorem graphValue (hi : i < n) (hj : j < n) (hk : k < n) :
    N.square.Definable n (fun s => Internal.At N.mem (s i) (s j) (s k)) :=
  boundedEx hi _ (orderedPair (N := N) (n := n + 1) (i := j + 1) (j := k + 1) (k := 0)
    (by omega) (by omega) (by omega))

end Definable
end PalomarI3380.SquareRepresentation
