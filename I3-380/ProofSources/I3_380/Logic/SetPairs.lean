module
public import I3_380.Logic.History
@[expose] public section

namespace PalomarI3380.Logic.Internal

variable {V : Type} {E : V → V → Prop}

def Extensional (E : V → V → Prop) : Prop :=
  ∀ a b, (∀ x, E x a ↔ E x b) → a = b

theorem pair_unique (he : Extensional E) {a b p q : V} (hp : Pair E a b p) (hq : Pair E a b q) :
    p = q :=
  he p q fun x => (hp x).trans (hq x).symm

theorem orderedPair_exists (pairs : ∀ a b, ∃ p, Pair E a b p) (a b : V) :
    ∃ p, OrderedPair E a b p := by
  obtain ⟨aa, haa⟩ := pairs a a
  obtain ⟨ab, hab⟩ := pairs a b
  obtain ⟨p, hp⟩ := pairs aa ab
  exact ⟨p, aa, ab, haa, hab, hp⟩

theorem orderedPair_unique (he : Extensional E) {a b p q : V}
    (hp : OrderedPair E a b p) (hq : OrderedPair E a b q) : p = q := by
  obtain ⟨aa, ab, haa, hab, hp⟩ := hp
  obtain ⟨aa', ab', haa', hab', hq⟩ := hq
  cases pair_unique he haa haa'
  cases pair_unique he hab hab'
  exact pair_unique he hp hq

private theorem orderedPair_intersection {a b p x : V} (h : OrderedPair E a b p) :
    (∀ y, E y p → E x y) ↔ x = a := by
  obtain ⟨aa, ab, haa, hab, hp⟩ := h
  constructor
  · intro hall
    exact ((haa x).mp (hall aa ((hp aa).mpr (Or.inl rfl)))).elim id id
  · rintro rfl y hy
    rcases (hp y).mp hy with rfl | rfl
    · exact (haa x).mpr (Or.inl rfl)
    · exact (hab x).mpr (Or.inl rfl)

private theorem orderedPair_union {a b p x : V} (h : OrderedPair E a b p) :
    (∃ y, E y p ∧ E x y) ↔ x = a ∨ x = b := by
  obtain ⟨aa, ab, haa, hab, hp⟩ := h
  constructor
  · rintro ⟨y, hy, hx⟩
    rcases (hp y).mp hy with rfl | rfl
    · exact Or.inl (((haa x).mp hx).elim id id)
    · exact (hab x).mp hx
  · exact fun h => ⟨ab, (hp ab).mpr (Or.inr rfl), (hab x).mpr h⟩

theorem orderedPair_injective {a b c d p : V}
    (h₁ : OrderedPair E a b p) (h₂ : OrderedPair E c d p) : a = c ∧ b = d := by
  have first : a = c :=
    (orderedPair_intersection h₂).mp ((orderedPair_intersection h₁).mpr rfl)
  subst c
  have bIn : b = a ∨ b = d :=
    (orderedPair_union h₂).mp ((orderedPair_union h₁).mpr (Or.inr rfl))
  have dIn : d = a ∨ d = b :=
    (orderedPair_union h₁).mp ((orderedPair_union h₂).mpr (Or.inr rfl))
  exact ⟨rfl, bIn.elim (fun eq => dIn.elim (fun h => eq.trans h.symm) Eq.symm) id⟩

end PalomarI3380.Logic.Internal
