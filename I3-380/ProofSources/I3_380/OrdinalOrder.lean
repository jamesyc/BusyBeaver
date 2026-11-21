module
public import I3_380.SetModel
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic

variable {A V : Type} {M : Algebra A} (N : SetContext M V)

/-- Least means least among the members of an actual set of the model.
A subset of the external carrier does not enter this definition. -/
def Least (r : V → V → Prop) (a x : V) : Prop :=
  N.mem x a ∧ ∀ y, N.mem y a → x = y ∨ r x y

structure WellOrderOn (r : V → V → Prop) (a : V) : Prop where
  irrefl : ∀ x, N.mem x a → ¬ r x x
  trans : ∀ x y z, N.mem x a → N.mem y a → N.mem z a → r x y → r y z → r x z
  compare : ∀ x y, N.mem x a → N.mem y a → r x y ∨ x = y ∨ r y x
  least : ∀ b, N.Subset b a → N.NonemptySet b → ∃ x, N.Least r b x

theorem WellOrderOn.restrict {r : V → V → Prop} {a b : V} (h : N.WellOrderOn r a) (hab : N.Subset b a) :
    N.WellOrderOn r b where
  irrefl x hx := h.irrefl x (hab x hx)
  trans x y z hx hy hz := h.trans x y z (hab x hx) (hab y hy) (hab z hz)
  compare x y hx hy := h.compare x y (hab x hx) (hab y hy)
  least c hc := h.least c (N.subset_trans hc hab)

theorem WellOrderOn.asymm {r : V → V → Prop} {a x y : V} (h : N.WellOrderOn r a)
    (hx : N.mem x a) (hy : N.mem y a) (hxy : r x y) (hyx : r y x) : False :=
  h.irrefl x hx (h.trans x y x hx hy hx hxy hyx)

/-- Use model-internal wellordering before establishing Foundation.
The transitivity requirements agree with the usual ordinal definition
once Foundation is available. -/
structure Ordinal (a : V) : Prop where
  transitive : N.Transitive a
  members_transitive : ∀ x, N.mem x a → N.Transitive x
  ordered : N.WellOrderOn N.mem a

theorem Ordinal.of_mem {a b : V} (h : N.Ordinal a) (hb : N.mem b a) : N.Ordinal b where
  transitive := h.members_transitive b hb
  members_transitive x hx := h.members_transitive x (h.transitive b hb x hx)
  ordered := WellOrderOn.restrict N h.ordered (h.transitive b hb)

theorem Ordinal.not_mem_self {a : V} (h : N.Ordinal a) : ¬N.mem a a :=
  fun ha => h.ordered.irrefl a ha ha

theorem Ordinal.exists_least {a b : V} (h : N.Ordinal a) (hb : N.Subset b a)
    (nonempty : N.NonemptySet b) : ∃ x, N.Least N.mem b x :=
  h.ordered.least b hb nonempty

theorem ordinal_empty : N.Ordinal N.empty where
  transitive := N.transempty
  members_transitive x hx := (N.empty_mem x hx).elim
  ordered := ⟨fun x hx => (N.empty_mem x hx).elim,
    fun x _ _ hx => (N.empty_mem x hx).elim,
    fun x _ hx => (N.empty_mem x hx).elim,
    fun _ subset ⟨x, hx⟩ => (N.empty_mem x (subset x hx)).elim⟩

theorem initial_segment {a b : V} (ha : N.Ordinal a) (sub : N.Subset b a)
    (initial : ∀ x, N.mem x b → ∀ y, N.mem y x → N.mem y b) :
    b = a ∨ N.mem b a := by
  classical
  by_cases same : b = a
  · exact Or.inl same
  · have excluded : N.NonemptySet (N.difference a b) := by
      apply Classical.byContradiction
      intro no
      apply same
      apply N.subset_antisymm sub
      intro x hx
      exact Classical.byContradiction fun absent =>
        no ⟨x, (N.mem_difference a b x).mpr ⟨hx, absent⟩⟩
    have contained : N.Subset (N.difference a b) a :=
      fun x hx => ((N.mem_difference a b x).mp hx).1
    obtain ⟨x, hx, smallest⟩ := ha.ordered.least (N.difference a b) contained excluded
    have ha₀ := (N.mem_difference a b x).mp hx
    have first : N.Subset x b := by
      intro y hy
      apply Classical.byContradiction
      intro missing
      have ya := ha.transitive x ha₀.1 y hy
      rcases smallest y ((N.mem_difference a b y).mpr ⟨ya, missing⟩) with eq | reverse
      · exact ha.ordered.irrefl x ha₀.1 (eq ▸ hy)
      · exact WellOrderOn.asymm N ha.ordered ya ha₀.1 hy reverse
    have second : N.Subset b x := by
      intro y hy
      rcases ha.ordered.compare y x (sub y hy) ha₀.1 with less | eq | above
      · exact less
      · exact (ha₀.2 (eq ▸ hy)).elim
      · exact (ha₀.2 (initial y hy x above)).elim
    exact Or.inr ((N.subset_antisymm second first) ▸ ha₀.1)

theorem ordinal_compare {a b : V} (ha : N.Ordinal a) (hb : N.Ordinal b) :
    N.mem a b ∨ a = b ∨ N.mem b a := by
  let both := N.inter a b
  have inA : N.Subset both a := fun x hx => ((N.mem_inter a b x).mp hx).1
  have inB : N.Subset both b := fun x hx => ((N.mem_inter a b x).mp hx).2
  have initial : N.Transitive both := N.trans_inter ha.transitive hb.transitive
  rcases N.initial_segment ha inA initial with eqA | contA <;>
    rcases N.initial_segment hb inB initial with eqB | contB
  · exact Or.inr (Or.inl (eqA.symm.trans eqB))
  · exact Or.inl (eqA ▸ contB)
  · exact Or.inr (Or.inr (eqB ▸ contA))
  · exact ((ha.of_mem N contA).not_mem_self N ((N.mem_inter a b both).mpr ⟨contA, contB⟩)).elim

theorem ordinal_subset_iff {a b : V} (ha : N.Ordinal a) (hb : N.Ordinal b) :
    N.Subset a b ↔ N.mem a b ∨ a = b := by
  constructor
  · intro h
    rcases N.ordinal_compare ha hb with ab | eq | ba
    · exact Or.inl ab
    · exact Or.inr eq
    · exact (hb.not_mem_self N (h b ba)).elim
  · rintro (h | rfl)
    · exact hb.transitive a h
    · exact N.subset_refl a

theorem ordinal_succ {a : V} (ha : N.Ordinal a) : N.Ordinal (N.succ a) := by
  have cover : ∀ x, N.mem x (N.succ a) → N.Ordinal x := by
    intro x hx
    rcases (N.mem_succ a x).mp hx with before | rfl
    · exact ha.of_mem N before
    · exact ha
  refine ⟨N.trans_succ ha.transitive, fun x hx => (cover x hx).transitive, ?_⟩
  refine ⟨fun x hx => (cover x hx).not_mem_self N, ?_,
    fun x y hx hy => N.ordinal_compare (cover x hx) (cover y hy), ?_⟩
  · intro x y z _ _ hz xy yz
    exact (cover z hz).transitive y yz x xy
  · intro b sub nonempty
    classical
    by_cases before : N.NonemptySet (N.inter b a)
    · have small : N.Subset (N.inter b a) a := fun x hx => ((N.mem_inter b a x).mp hx).2
      obtain ⟨x, hit, least⟩ := ha.ordered.least _ small before
      have found := (N.mem_inter b a x).mp hit
      refine ⟨x, found.1, fun y hy => ?_⟩
      rcases (N.mem_succ a y).mp (sub y hy) with earlier | rfl
      · exact least y ((N.mem_inter b a y).mpr ⟨hy, earlier⟩)
      · exact Or.inr found.2
    · have all (x : V) (hx : N.mem x b) : x = a :=
        ((N.mem_succ a x).mp (sub x hx)).elim
          (fun h => (before ⟨x, (N.mem_inter b a x).mpr ⟨hx, h⟩⟩).elim) id
      obtain ⟨x, hx⟩ := nonempty
      exact ⟨x, hx, fun y hy => Or.inl ((all x hx).trans (all y hy).symm)⟩

theorem ordinal_of_transitive_members {a : V} (trans : N.Transitive a)
    (below : ∀ x, N.mem x a → N.Ordinal x) : N.Ordinal a := by
  refine ⟨trans, fun x hx => (below x hx).transitive, ?_⟩
  refine ⟨fun x hx => (below x hx).not_mem_self N, ?_,
    fun x y hx hy => N.ordinal_compare (below x hx) (below y hy), ?_⟩
  · intro x y z _ _ hz xy yz
    exact (below z hz).transitive y yz x xy
  · rintro b belongs ⟨x, hx⟩
    have hxOrd := below x (belongs x hx)
    have ss := N.ordinal_succ hxOrd
    let bounded := N.inter b (N.succ x)
    have bound : N.Subset bounded (N.succ x) := fun y hy => ((N.mem_inter _ _ _).mp hy).2
    have inhabited : N.NonemptySet bounded :=
      ⟨x, (N.mem_inter _ _ _).mpr ⟨hx, (N.mem_succ _ _).mpr (Or.inr rfl)⟩⟩
    obtain ⟨y, hit, least⟩ := ss.ordered.least bounded bound inhabited
    have inBoth := (N.mem_inter _ _ _).mp hit
    refine ⟨y, inBoth.1, fun z hz => ?_⟩
    rcases N.ordinal_compare (below z (belongs z hz)) hxOrd with earlier | eq | later
    · exact least z ((N.mem_inter _ _ _).mpr ⟨hz, (N.mem_succ _ _).mpr (Or.inl earlier)⟩)
    · exact least z ((N.mem_inter _ _ _).mpr ⟨hz, (N.mem_succ _ _).mpr (Or.inr eq)⟩)
    · refine Or.inr ?_
      rcases (N.mem_succ _ _).mp inBoth.2 with belowX | same
      · exact (below z (belongs z hz)).transitive x later y belowX
      · exact same.symm ▸ later

theorem ordinal_union (a : V) (all : ∀ x, N.mem x a → N.Ordinal x) : N.Ordinal (N.union a) := by
  apply N.ordinal_of_transitive_members (N.trans_union fun x hx => (all x hx).transitive)
  intro x hx
  obtain ⟨b, hb, belongs⟩ := (N.mem_union a x).mp hx
  exact (all b hb).of_mem N belongs

end PalomarI3380.SquareRepresentation.SetContext
