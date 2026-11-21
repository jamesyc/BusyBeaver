module
public import I3_380.Hartogs
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic

variable {A V : Type} {M : Algebra A} (N : SetContext M V)

def Unused (a graph remaining : V) : Prop :=
  ∀ x, N.mem x remaining ↔ N.mem x a ∧ ¬∃ i, Internal.At N.mem graph i x

theorem unused_exists (a graph : V) : ∃ remaining, N.Unused a graph remaining :=
  ⟨N.difference a (N.range graph), fun _ =>
    (N.mem_difference _ _ _).trans (and_congr_right fun _ => not_congr (N.mem_range _ _))⟩

theorem unused_unique {a graph b c : V} (hb : N.Unused a graph b) (hc : N.Unused a graph c) : b = c :=
  N.ext b c fun x => (hb x).trans (hc x).symm

def SelectStep (key : V) (_ : V) (graph value : V) : Prop :=
  ∃ a chooser remaining, Internal.OrderedPair N.mem a chooser key ∧
    N.Unused a graph remaining ∧
    ((N.NonemptySet remaining ∧ Internal.At N.mem chooser remaining value) ∨
      (Internal.Empty N.mem remaining ∧ Internal.Empty N.mem value))

private theorem selection_definable : Definable.Relation4 N (N.SelectStep) := by
  intro n i _ k l hi _ hk hl
  let hPair := Definable.orderedPair (N := N) (n := n + 3) (i := 2) (j := 1) (k := i + 3)
    (by omega) (by omega) (by omega)
  let hRemaining := Definable.all (Definable.iff
    (Definable.mem (N := N) (n := n + 4) (i := 0) (j := 1) (by omega) (by omega))
    ((Definable.mem (N := N) (n := n + 4) (i := 0) (j := 3) (by omega) (by omega)).and
      (Definable.not (Definable.ex
        (Definable.graphValue (N := N) (n := n + 5) (i := k + 5) (j := 0) (k := 1)
          (by omega) (by omega) (by omega))))))
  let hPick := (Definable.nonempty (N := N) (n := n + 3) (i := 0) (by omega)).and
    (Definable.graphValue (N := N) (n := n + 3) (i := 1) (j := 0) (k := l + 3)
      (by omega) (by omega) (by omega))
  let hExhausted := (Definable.empty (N := N) (n := n + 3) (i := 0) (by omega)).and
    (Definable.empty (N := N) (n := n + 3) (i := l + 3) (by omega))
  exact Definable.ex (Definable.ex (Definable.ex (hPair.and (hRemaining.and (hPick.or hExhausted)))))

private theorem chooser_exists (X : V) :
    ∃ chooser, ∀ a, N.Subset a X → N.NonemptySet a →
      ∃ y, Internal.At N.mem chooser a y ∧ N.mem y a ∧
        ∀ z, Internal.At N.mem chooser a z → z = y := by
  let family := N.difference (N.power X) (N.singleton N.empty)
  have inhabited (a : V) (h : N.mem a family) : N.NonemptySet a := by
    apply Classical.byContradiction
    intro no
    have empty : Internal.Empty N.mem a := fun x hx => no ⟨x, hx⟩
    exact ((N.mem_difference _ _ _).mp h).2
      ((N.mem_singleton _ _).mpr ((N.empty_unique a).mp empty))
  obtain ⟨f, hf, picks⟩ := N.choiceSet family inhabited
  refine ⟨f, fun a sub ⟨x, hx⟩ => ?_⟩
  have inFamily : N.mem a family := (N.mem_difference _ _ _).mpr
    ⟨(N.mem_power _ _).mpr sub, fun h => N.empty_mem x (((N.mem_singleton _ _).mp h) ▸ hx)⟩
  obtain ⟨b, hb, one⟩ := hf.1 a inFamily
  exact ⟨b, hb, picks a b inFamily hb, one⟩

private def Saturated (X graph cut : V) : Prop :=
  ∀ y, N.mem y X → ∃ x, N.mem x cut ∧ Internal.At N.mem graph x y

private theorem saturation_definable {n i j k : Nat} (hi : i < n) (hj : j < n) (hk : k < n) :
    N.square.Definable n (fun s => N.Saturated (s i) (s j) (s k)) :=
  Definable.boundedAll hi _ (Definable.boundedEx (i := k + 1) (by omega) _
    (Definable.graphValue (i := j + 2) (j := 0) (k := 1) (by omega) (by omega) (by omega)))

/-- Internal Choice wellorders any set. Hartogs bounds the length of the
recursion that repeatedly takes a selected unused element. -/
theorem wellOrdering (X : V) : ∃ r, N.WellOrderOn (Internal.At N.mem r) X := by
  classical
  obtain ⟨height, ordinal, noInjection⟩ := N.hartogs X
  obtain ⟨chooser, select⟩ := N.chooser_exists X
  let key := N.orderedPair X chooser
  have unpack {x f : V} (h : Internal.OrderedPair N.mem x f key) : x = X ∧ f = chooser :=
    Internal.orderedPair_injective h (N.orderedPair_intro X chooser)
  have updateExists (x graph : V) : ∃ y, N.SelectStep key x graph y := by
    obtain ⟨remain, contents⟩ := N.unused_exists X graph
    by_cases remaining : N.NonemptySet remain
    · obtain ⟨y, chosen, _, _⟩ := select remain (fun z hz => ((contents z).mp hz).1) remaining
      exact ⟨y, X, chooser, remain, N.orderedPair_intro _ _, contents, Or.inl ⟨remaining, chosen⟩⟩
    · exact ⟨N.empty, X, chooser, remain, N.orderedPair_intro _ _, contents,
        Or.inr ⟨fun y hy => remaining ⟨y, hy⟩, N.empty_mem⟩⟩
  have updateUnique (x graph y z : V)
      (hy : N.SelectStep key x graph y) (hz : N.SelectStep key x graph z) : y = z := by
    obtain ⟨a, f, remain, p, contents, ys⟩ := hy
    obtain ⟨a', f', remain', p', contents', zs⟩ := hz
    obtain ⟨rfl, rfl⟩ := unpack p
    obtain ⟨rfl, rfl⟩ := unpack p'
    cases N.unused_unique contents contents'
    rcases ys with ⟨hY, vY⟩ | ⟨empty, yEmpty⟩ <;>
      rcases zs with ⟨hZ, vZ⟩ | ⟨empty', zEmpty⟩
    · obtain ⟨b, _, _, one⟩ := select remain (fun w hw => ((contents w).mp hw).1) hY
      exact (one y vY).trans (one z vZ).symm
    · obtain ⟨b, hb⟩ := hY
      exact (empty' b hb).elim
    · obtain ⟨b, hb⟩ := hZ
      exact (empty b hb).elim
    · exact ((N.empty_unique y).mp yEmpty).trans ((N.empty_unique z).mp zEmpty).symm
  let recursion : SetRecursion N :=
    ⟨height, height, key, fun _ => N.mem, Definable.membership_relation, ordinal.ordered,
      N.SelectStep, N.selection_definable, updateExists, updateUnique⟩
  obtain ⟨graph, sol⟩ := recursion.solution_exists
  let onGraph := sol.functionOn
  have selection {x y : V} (hx : N.mem x height) (hy : Internal.At N.mem graph x y)
      (notDone : ¬N.Saturated X graph x) :
      N.mem y X ∧ ∀ z, N.mem z x → ¬Internal.At N.mem graph z y := by
    obtain ⟨cut, prior, item, hc, pres, atItem, update⟩ := sol.agrees x hx
    obtain ⟨w, _, unique⟩ := onGraph.1 x hx
    have same := (unique item atItem).trans (unique y hy).symm
    subst item
    have cutEq : cut = x := by
      apply N.ext
      intro z
      refine (hc z).trans ?_
      exact ⟨And.right, fun zIn => ⟨ordinal.transitive x hx z zIn, zIn⟩⟩
    subst cut
    obtain ⟨a, f, remains, hp, desc, take⟩ := update
    obtain ⟨rfl, rfl⟩ := unpack hp
    rcases take with ⟨nonempty, chosen⟩ | ⟨finished, _⟩
    · obtain ⟨out, _, there, one⟩ := select remains (fun z hz => ((desc z).mp hz).1) nonempty
      have member : N.mem y remains := (one y chosen).symm ▸ there
      have ⟨inX, fresh⟩ := (desc y).mp member
      exact ⟨inX, fun z hz old => fresh ⟨z, (N.restricts_value pres).mpr ⟨hz, old⟩⟩⟩
    · exfalso
      apply notDone
      intro z hz
      apply Classical.byContradiction
      intro missing
      have absent : ¬∃ j, Internal.At N.mem prior j z := by
        rintro ⟨j, hj⟩
        have hx := (N.restricts_value pres).mp hj
        exact missing ⟨j, hx.1, hx.2⟩
      exact finished z ((desc z).mpr ⟨hz, absent⟩)
  have injBefore (bound : V) (sub : N.Subset bound height)
      (earlier : ∀ x, N.mem x bound → ¬N.Saturated X graph x) :
      N.Injection bound X (N.restrictGraph graph bound) := by
    have cut := N.restricts_canonical graph bound
    refine ⟨N.restricts_function onGraph sub cut, fun x y atValue => ?_, fun x y z h k => ?_⟩
    · obtain ⟨hx, atOriginal⟩ := (N.restricts_value cut).mp atValue
      exact (selection (sub x hx) atOriginal (earlier x hx)).1
    · obtain ⟨hx, fx⟩ := (N.restricts_value cut).mp h
      obtain ⟨hy, fy⟩ := (N.restricts_value cut).mp k
      rcases ordinal.ordered.compare x y (sub x hx) (sub y hy) with first | eq | second
      · exact ((selection (sub y hy) fy (earlier y hy)).2 x first fx).elim
      · exact eq
      · exact ((selection (sub x hx) fx (earlier x hx)).2 y second fy).elim
  obtain ⟨done, desc⟩ := N.separate [X, graph]
    (N.saturation_definable (n := 4) (i := 2) (j := 3) (k := 0) (by decide) (by decide) (by decide)) height height
  have sub : N.Subset done height := fun _ h => ((desc _).mp h).1
  by_cases someDone : N.NonemptySet done
  · obtain ⟨cut, cutIn, least⟩ := ordinal.ordered.least done sub someDone
    obtain ⟨hc, complete⟩ := (desc cut).mp cutIn
    have prior {x : V} (hx : N.mem x cut) : ¬N.Saturated X graph x := by
      intro sat
      have hHeight := ordinal.transitive cut hc x hx
      have hDone := (desc x).mpr ⟨hHeight, sat⟩
      rcases least x hDone with same | reverse
      · exact ordinal.ordered.irrefl cut hc (same ▸ hx)
      · exact WellOrderOn.asymm N ordinal.ordered hHeight hc hx reverse
    have injects := injBefore cut (ordinal.transitive cut hc) fun _ => prior
    let g := N.restrictGraph graph cut
    have rangeEq : N.range g = X := by
      apply N.ext
      intro y
      rw [N.mem_range]
      constructor
      · rintro ⟨x, h⟩
        exact injects.into x y h
      · intro hy
        obtain ⟨x, hx, h⟩ := complete y hy
        exact ⟨x, (N.restricts_value (N.restricts_canonical _ _)).mpr ⟨hx, h⟩⟩
    obtain ⟨r, _, order, _⟩ := N.ordinal_order_image (ordinal.of_mem N hc) injects
    exact ⟨r, rangeEq ▸ order⟩
  · have prior (x : V) (hx : N.mem x height) : ¬N.Saturated X graph x :=
      fun h => someDone ⟨x, (desc x).mpr ⟨hx, h⟩⟩
    exact (noInjection ⟨_, injBefore height (N.subset_refl _) prior⟩).elim

end PalomarI3380.SquareRepresentation.SetContext
