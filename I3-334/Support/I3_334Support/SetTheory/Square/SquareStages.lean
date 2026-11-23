module
public import I3_334Support.SetTheory.Graphs.NamedPoints
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Manifest

variable {A Point : Type} {M : Algebra A}

theorem named_edge (S : SquareRepresentation M Point) (hM : M.Models preceding) (r : A)
    {x y : Point} (edge : S.rel r x y) : ∃ u v, S.Named u ∧ S.Named v ∧ S.rel r u v := by
  have hDom : S.rel (domain M r) x x := (S.domain_iff r x x).mpr ⟨rfl, y, edge⟩
  obtain ⟨u, ⟨name, named⟩, hu⟩ := S.named_of_subidentity hM (domain M r)
    (fun a b h => ((S.domain_iff r a b).mp h).1) hDom
  obtain ⟨v, hv⟩ := ((S.domain_iff r u u).mp hu).2
  let rowRange := domain M (M.converse (M.product name r))
  have range (a b : Point) : S.rel rowRange a b ↔ a = b ∧ S.rel r u a := by
    change S.rel (domain M (M.converse (M.product name r))) a b ↔ _
    simp only [S.domain_iff, S.converse, S.product, named]
    constructor
    · rintro ⟨same, _, w, ⟨_, rfl⟩, edge⟩
      exact ⟨same, edge⟩
    · rintro ⟨same, found⟩
      exact ⟨same, u, u, ⟨rfl, rfl⟩, found⟩
  obtain ⟨w, hw, hr⟩ := S.named_of_subidentity hM rowRange (fun a b h => ((range a b).mp h).1)
    ((range v v).mpr ⟨rfl, hv⟩)
  exact ⟨u, w, ⟨name, named⟩, hw, ((range w w).mp hr).2⟩

theorem domain_eq (S : SquareRepresentation M Point) (hM : M.Models preceding) (a b : Point) :
    S.rel (M.constant .D) a b ↔ a = b ∧ ∃ y, S.rel (M.constant .J) a y := by
  have law := hM defineDomain (by simp [preceding, retained]) (fun _ => M.constant .U)
  change M.constant .D = domain M (M.constant .J) at law
  rw [law, S.domain_iff]

/-- Separation of the target equation survives passage to named points. -/
theorem named_moved (S : SquareRepresentation M Point) (hM : M.Models preceding)
    (separates : ¬ ∀ a b, S.rel (M.constant .D) a b ↔ S.rel (M.constant .J) a b) :
    ∃ x y, S.Named x ∧ S.Named y ∧ S.rel (M.constant .J) x y ∧ x ≠ y := by
  classical
  have existsMoved : ∃ x y, S.rel (M.constant .J) x y ∧ x ≠ y := by
    apply Classical.byContradiction
    intro noEdge
    apply separates
    intro a b
    rw [S.domain_eq hM a b]
    constructor
    · rintro ⟨rfl, y, ey⟩
      have same : a = y := Classical.byContradiction fun hn => noEdge ⟨a, y, ey, hn⟩
      rwa [← same] at ey
    · intro e
      exact ⟨Classical.byContradiction fun hn => noEdge ⟨a, b, e, hn⟩, b, e⟩
  obtain ⟨a, b, ab, ne⟩ := existsMoved
  let off := M.neg (M.nand (M.constant .J) (M.neg (M.constant .I)))
  have off_iff (x y : Point) : S.rel off x y ↔ S.rel (M.constant .J) x y ∧ x ≠ y := by
    simp only [off, S.meet, S.complement, S.identity]
  obtain ⟨u, v, hu, hv, hOff⟩ := S.named_edge hM off ((off_iff a b).mpr ⟨ab, ne⟩)
  exact ⟨u, v, hu, hv, (off_iff u v).mp hOff⟩

theorem stage_choice (S : SquareRepresentation M Point) (hM : M.Models preceding) (a : Point) :
    ∃ b, S.rel (M.constant .S) b b ∧ S.rel (M.constant .T) a b := by
  have self : S.rel (M.constant .T) a a := (S.subset_iff hM a a).mpr fun _ h => h
  obtain ⟨b, selected⟩ := (S.choice_domain hM (M.constant .T) a).mpr ⟨a, self⟩
  have law := hM defineStages (by simp [preceding]) (fun _ => M.constant .U)
  change M.constant .S = M.product (M.converse (M.choice (M.constant .T)))
    (M.choice (M.constant .T)) at law
  exact ⟨b, by rw [law, S.product]; exact ⟨a, (S.converse _ _ _).mpr selected, selected⟩,
    S.choice_sub hM _ selected⟩

theorem stage_iff (S : SquareRepresentation M Point) (hM : M.Models preceding)
    {a : Point} (ha : S.rel (M.constant .S) a a) (x : Point) :
    S.rel (M.constant .E) x a ↔
      ∃ b, S.rel (M.constant .E) b a ∧ S.rel (M.constant .S) b b ∧ S.rel (M.constant .T) x b := by
  have law := hM stageLaw (by simp [preceding, retained]) (fun _ => M.constant .U)
  let s := M.constant .S
  let e := M.converse (M.constant .E)
  have sDiag {p q : Point} (hs : S.rel s p q) : p = q := by
    have defn := hM defineStages (by simp [preceding]) (fun _ => M.constant .U)
    change s = M.product (M.converse (M.choice (M.constant .T))) (M.choice (M.constant .T)) at defn
    rw [defn, S.product] at hs
    obtain ⟨z, first, second⟩ := hs
    exact S.choice_functional hM _ ((S.converse _ _ _).mp first) second
  change M.product s e = M.product (M.product (M.product s e) s) (M.converse (M.constant .T)) at law
  have left : S.rel (M.product s e) a x ↔ S.rel (M.constant .E) x a := by
    rw [S.product]
    constructor
    · rintro ⟨y, sy, ey⟩
      exact (sDiag sy).symm ▸ (S.converse _ _ _).mp ey
    · intro h
      exact ⟨a, ha, (S.converse _ _ _).mpr h⟩
  have rel : S.rel (M.product s e) a x ↔
      ∃ b, (∃ c, S.rel (M.product s e) a c ∧ S.rel s c b) ∧ S.rel (M.constant .T) x b := by
    have hEq := Iff.of_eq (congrArg (fun r => S.rel r a x) law)
    refine hEq.trans ?_
    simp only [S.product, S.converse]
  constructor
  · intro hx
    obtain ⟨b, ⟨c, ec, stage⟩, bounds⟩ := rel.mp (left.mpr hx)
    obtain rfl := sDiag stage
    have heb : S.rel (M.constant .E) c a := by
      obtain ⟨z, sEdge, eEdge⟩ := (S.product _ _ _ _).mp ec
      exact (sDiag sEdge).symm ▸ (S.converse _ _ _).mp eEdge
    exact ⟨c, heb, stage, bounds⟩
  · rintro ⟨b, earlier, bs, bounds⟩
    exact left.mp (rel.mpr ⟨b, ⟨b, (S.product _ _ _ _).mpr
      ⟨a, ha, (S.converse _ _ _).mpr earlier⟩, bs⟩, bounds⟩)

/-- The selected stage gives a common set containing every subset of
each member of a given set. -/
theorem power_cover (S : SquareRepresentation M Point) (hM : M.Models preceding) (a : Point) :
    ∃ cover, ∀ y z, S.rel (M.constant .E) y a → S.rel (M.constant .T) z y →
      S.rel (M.constant .E) z cover := by
  obtain ⟨b, stage, contains⟩ := S.stage_choice hM a
  refine ⟨b, fun y z hy hz => ?_⟩
  have hy' := (S.subset_iff hM a b).mp contains y hy
  obtain ⟨c, earlier, cs, yc⟩ := (S.stage_iff hM stage y).mp hy'
  have zc := (S.subset_iff hM z c).mpr fun v hv =>
    (S.subset_iff hM y c).mp yc v ((S.subset_iff hM z y).mp hz v hv)
  exact (S.stage_iff hM stage z).mpr ⟨c, earlier, cs, zc⟩

theorem inhabited_set_of_domain (S : SquareRepresentation M Point) (hM : M.Models preceding)
    {x : Point} (hx : S.rel (M.constant .D) x x) :
    ∃ a, S.rel (M.constant .E) x a := by
  have law := hM domainClosed (by simp [preceding, retained]) (fun _ => M.constant .U)
  let active := M.neg (M.nand (M.constant .S) (M.constant .D))
  change M.constant .D = M.neg (M.nand (M.constant .I)
    (M.product (M.product (M.constant .E) active) (M.constant .U))) at law
  rw [law, S.meet, S.product] at hx
  obtain ⟨_, a, existsEarlier, _⟩ := hx
  obtain ⟨b, member, _⟩ := (S.product _ _ _ _).mp existsEarlier
  exact ⟨b, member⟩

end PalomarI3380.SquareRepresentation
