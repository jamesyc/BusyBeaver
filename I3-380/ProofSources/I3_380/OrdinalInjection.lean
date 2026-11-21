module
public import I3_380.DefinableOrderType
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic

variable {A V : Type} {M : Algebra A} (N : SetContext M V)

structure Injection (source target graph : V) : Prop where
  functionOn : Internal.FunctionOn N.mem graph source
  into : ∀ x y, Internal.At N.mem graph x y → N.mem y target
  unique : ∀ x y z, Internal.At N.mem graph x z → Internal.At N.mem graph y z → x = y

def Injects (source target : V) : Prop :=
  ∃ f, N.Injection source target f

theorem injection_restrict {source target graph a b : V} (f : N.Injection source target graph)
    (sub : N.Subset a source) (sub' : ∀ x y, N.mem x a → Internal.At N.mem graph x y → N.mem y b) :
    N.Injects a b := by
  let g := N.restrictGraph graph a
  have restr := N.restricts_canonical graph a
  exact ⟨g, N.restricts_function f.functionOn sub restr, fun x y atG =>
    let ⟨hx, original⟩ := (N.restricts_value restr).mp atG; sub' x y hx original,
    fun x y z hx hy => f.unique x y z ((N.restricts_value restr).mp hx).2 ((N.restricts_value restr).mp hy).2⟩

/-- The ordinal order transported onto the range of an internal
injection is itself a coded set relation. -/
theorem ordinal_order_image {a X f : V} (ha : N.Ordinal a) (inj : N.Injection a X f) :
    ∃ r, N.Subset r (N.power (N.power X)) ∧
      N.WellOrderOn (Internal.At N.mem r) (N.range f) ∧
        N.OrderType (Internal.At N.mem r) (N.range f) a := by
  let E := N.mem
  let pred := fun s : Nat → V =>
    ∃ x y l r, Internal.OrderedPair E l r (s 0) ∧ Internal.At E (s 1) x l ∧
      Internal.At E (s 1) y r ∧ E x y
  have formula : N.square.Definable 2 pred := by
    have pair := Definable.orderedPair (N := N) (n := 6) (i := 1) (j := 0) (k := 4)
      (by decide) (by decide) (by decide)
    have first := Definable.graphValue (N := N) (n := 6) (i := 5) (j := 3) (k := 1)
      (by decide) (by decide) (by decide)
    have next := Definable.graphValue (N := N) (n := 6) (i := 5) (j := 2) (k := 0)
      (by decide) (by decide) (by decide)
    have order := Definable.mem (N := N) (n := 6) (i := 3) (j := 2) (by decide) (by decide)
    exact Definable.ex (Definable.ex (Definable.ex (Definable.ex (pair.and (first.and (next.and order))))))
  obtain ⟨r, meaning⟩ := N.separate [] formula (N.power (N.power X)) f
  have rSpec (l u : V) : Internal.At E r l u ↔
      ∃ x y, Internal.At E f x l ∧ Internal.At E f y u ∧ E x y := by
    rw [N.at_pair, meaning]
    constructor
    · rintro ⟨_, x, y, l', r', pair, first, next, before⟩
      obtain ⟨rfl, rfl⟩ := Internal.orderedPair_injective pair (N.orderedPair_intro l u)
      exact ⟨x, y, first, next, before⟩
    · rintro ⟨x, y, left, right, before⟩
      exact ⟨N.orderedPair_bound (inj.into x l left) (inj.into y u right), x, y, l, u,
        N.orderedPair_intro l u, left, right, before⟩
  let range := N.range f
  let inverse := fun s : Nat → V => Internal.At E (s 2) (s 1) (s 0)
  have described : N.square.Definable 3 inverse :=
    Definable.graphValue (N := N) (i := 2) (j := 1) (k := 0) (by decide) (by decide) (by decide)
  obtain ⟨g, gOn, gSpec⟩ := N.functionOf [f] described
    (fun x y z hy hz => inj.unique y z x hy hz) range (fun x hx => (N.mem_range f x).mp hx)
  have gValues (x y : V) : Internal.At E g x y ↔ Internal.At E f y x := by
    refine (gSpec x y).trans ?_
    exact ⟨And.right, fun h => ⟨(N.mem_range _ _).mpr ⟨y, h⟩, h⟩⟩
  have gOnto : N.IsRange g a := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, atF, _⟩ := inj.functionOn.1 y hy
      exact ⟨x, (gValues x y).mpr atF⟩
    · rintro ⟨x, h⟩
      exact SetRecursion.at_domain inj.functionOn ((gValues _ _).mp h)
  have relEquiv (x y l u : V) (gx : Internal.At E g l x) (gy : Internal.At E g u y) :
      Internal.At E r l u ↔ E x y := by
    let left := (gValues _ _).mp gx
    let right := (gValues _ _).mp gy
    refine (rSpec l u).trans ⟨?_, fun h => ⟨x, y, left, right, h⟩⟩
    rintro ⟨x', y', hLeft, hRight, order⟩
    have sameX := inj.unique x' x l hLeft left
    have sameY := inj.unique y' y u hRight right
    exact sameX ▸ sameY ▸ order
  have gInv {x y : V} (hx : Internal.At E g x y) : E y a :=
    (gOnto y).mpr ⟨x, hx⟩
  have ordered : N.WellOrderOn (Internal.At E r) range := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx h
      obtain ⟨y, atY, _⟩ := gOn.1 x hx
      exact ha.ordered.irrefl y (gInv atY) ((relEquiv _ _ _ _ atY atY).mp h)
    · intro x y z hx hy hz rxy ryz
      obtain ⟨i, gi, _⟩ := gOn.1 x hx
      obtain ⟨j, gj, _⟩ := gOn.1 y hy
      obtain ⟨k, gk, _⟩ := gOn.1 z hz
      exact (relEquiv _ _ _ _ gi gk).mpr (ha.ordered.trans i j k (gInv gi) (gInv gj) (gInv gk)
        ((relEquiv _ _ _ _ gi gj).mp rxy) ((relEquiv _ _ _ _ gj gk).mp ryz))
    · intro x y hx hy
      obtain ⟨i, gi, _⟩ := gOn.1 x hx
      obtain ⟨j, gj, _⟩ := gOn.1 y hy
      rcases ha.ordered.compare i j (gInv gi) (gInv gj) with before | same | after
      · exact Or.inl ((relEquiv _ _ _ _ gi gj).mpr before)
      · subst j
        obtain ⟨z, _, unique⟩ := inj.functionOn.1 i (gInv gi)
        exact Or.inr (Or.inl ((unique x ((gValues _ _).mp gi)).trans (unique y ((gValues _ _).mp gj)).symm))
      · exact Or.inr (Or.inr ((relEquiv _ _ _ _ gj gi).mpr after))
    · intro subset contained inhabited
      have definable := Definable.boundedEx (S := N.square) (n := 3) (i := 1) (by decide) _
        (Definable.graphValue (N := N) (n := 4) (i := 3) (j := 1) (k := 0) (by decide) (by decide) (by decide))
      obtain ⟨selected, pulled⟩ := N.separate [f] definable a subset
      have hSub : N.Subset selected a := fun x hx => ((pulled x).mp hx).1
      have hSome : N.NonemptySet selected := by
        obtain ⟨y, hy⟩ := inhabited
        obtain ⟨x, hx⟩ := (N.mem_range f y).mp (contained y hy)
        exact ⟨x, (pulled x).mpr ⟨SetRecursion.at_domain inj.functionOn hx, y, hy, hx⟩⟩
      obtain ⟨least, hl, min⟩ := ha.ordered.least selected hSub hSome
      obtain ⟨_, u, uBy, fLU⟩ := (pulled least).mp hl
      refine ⟨u, uBy, fun t ht => ?_⟩
      obtain ⟨z, zT⟩ := (N.mem_range f t).mp (contained t ht)
      have zA := SetRecursion.at_domain inj.functionOn zT
      have inSelected := (pulled z).mpr ⟨zA, t, ht, zT⟩
      rcases min z inSelected with same | before
      · subst z
        obtain ⟨p, _, unique⟩ := inj.functionOn.1 least zA
        exact Or.inl ((unique u fLU).trans (unique t zT).symm)
      · exact Or.inr ((rSpec u t).mpr ⟨least, z, fLU, zT, before⟩)
  exact ⟨r, fun p hp => ((meaning p).mp hp).1, ordered, g, ha, gOn, gOnto,
    fun x y l u => relEquiv l u x y⟩

end PalomarI3380.SquareRepresentation.SetContext
