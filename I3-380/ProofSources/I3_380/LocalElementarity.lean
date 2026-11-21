module
public import I3_380.LocalAlgebra
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic Manifest

variable {A Point : Type} {M : Algebra A} {S : SquareRepresentation M Point}

abbrev Domain (S : SquareRepresentation M Point) := {x : Point // S.activePoint x}

theorem localProjections (hM : M.Models preceding) (closed : S.LocalClosure) :
    Nonempty (QuasiProjections (LocalRelation.square hM closed)) := by
  let model := LocalRelation.square hM closed
  let alg := LocalRelation.algebra hM closed
  let uniqueRow := fun a => alg.inf a (alg.neg (alg.product a (alg.neg (alg.constant .I))))
  have specs (r : LocalRelation S) (x y : S.Domain) :
      model.rel (uniqueRow r) x y ↔ model.rel r x y ∧ ∀ z, model.rel r x z → z = y := by
    apply (model.meet r (alg.neg (alg.product r (alg.neg (alg.constant .I)))) x y).trans
    apply and_congr_right
    intro _
    rw [model.complement, model.product]
    constructor
    · intro none z hz
      apply Classical.byContradiction
      intro ne
      exact none ⟨z, hz, (model.complement _ _ _).mpr fun h => ne ((model.identity _ _).mp h)⟩
    · rintro all ⟨z, hz, ne⟩
      exact (model.complement _ _ _).mp ne ((model.identity _ _).mpr (all z hz))
  refine model.projections_of_selection ?_ uniqueRow ?_ ?_
  · intro a b
    obtain ⟨p, active, pair⟩ := closed.pairs a.property b.property
    refine ⟨⟨p, active⟩, fun x => ?_⟩
    change S.rel (M.constant .E) x.val p ∧ S.activePoint p ↔ x = a ∨ x = b
    simp only [active, and_true, Subtype.ext_iff]
    exact pair _
  · intro r p x y hx hy
    exact ((specs r p y).mp hy).2 x ((specs r p x).mp hx).1
  · intro r p a unique
    exact (specs r p a).mpr ⟨(unique a).mpr rfl, fun x hx => (unique x).mp hx⟩

theorem j_has_image (hM : M.Models preceding) (x : S.Domain) :
    ∃ y, S.rel (M.constant .J) x.val y :=
  ((S.domain_eq hM x.val x.val).mp x.property).2

noncomputable def jMap (hM : M.Models preceding) (closed : S.LocalClosure) (x : S.Domain) : S.Domain :=
  ⟨Classical.choose (j_has_image hM x),
    (j_active hM closed (Classical.choose_spec (j_has_image hM x))).2⟩

theorem jMap_edge (hM : M.Models preceding) (closed : S.LocalClosure) (x : S.Domain) :
    S.rel (M.constant .J) x.val (jMap hM closed x).val :=
  Classical.choose_spec (j_has_image hM x)

theorem jMap_moved (hM : M.Models preceding) (closed : S.LocalClosure) {x y : Point}
    (edge : S.rel (M.constant .J) x y) (different : x ≠ y) :
    ∃ a : S.Domain, jMap hM closed a ≠ a := by
  let source : S.Domain := ⟨x, (j_active hM closed edge).1⟩
  have image := j_single_valued hM closed (jMap_edge hM closed source) edge
  exact ⟨source, fun h => different ((congrArg Subtype.val h).symm.trans image)⟩

theorem jMap_maintainsEncoding (hM : M.Models preceding) (closed : S.LocalClosure)
    (P : QuasiProjections (LocalRelation.square hM closed)) {n : Nat} {code : S.Domain}
    {env : Nat → S.Domain} (encoded : P.Encodes n code env) :
    P.Encodes n (jMap hM closed code) (jMap hM closed ∘ env) := by
  induction n generalizing code env with
  | zero => trivial
  | succ n ih =>
    obtain ⟨head, tail, rest, encoded⟩ := encoded
    exact ⟨P.first.generated.preserved hM (jMap_edge hM closed code) (jMap_edge hM closed (env 0)) head,
      jMap hM closed tail,
      P.second.generated.preserved hM (jMap_edge hM closed code) (jMap_edge hM closed tail) rest,
      ih encoded⟩

/-- The nontrivial graph preserves and reflects every fixed first-order
formula in the active membership domain, with arbitrary parameters. -/
theorem local_elementarity (hM : M.Models preceding) (closed : S.LocalClosure)
    (p : Formula) (n : Nat) (bound : Bound p n) (env : Nat → S.Domain) :
    eval (fun x y => S.rel (M.constant .E) x.val y.val) p env ↔
      eval (fun x y => S.rel (M.constant .E) x.val y.val) p (jMap hM closed ∘ env) := by
  obtain ⟨P⟩ := localProjections hM closed
  let model := LocalRelation.square hM closed
  let alg := LocalRelation.algebra hM closed
  let formula := RelationFormula.liftMembership (alg.constant .E) p
  have bound' : formula.Bound n := (RelationFormula.liftMembership_bound _ _ _).mpr bound
  have pointwise (values : Nat → S.Domain) :
      RelationFormula.eval model formula values ↔
        eval (fun x y => S.rel (M.constant .E) x.val y.val) p values := by
    rw [RelationFormula.liftMembership_eval]
    induction p generalizing values <;>
      simp only [eval, model, alg, LocalRelation.square, LocalRelation.algebra, LocalRelation.member,
        localSeed, Subtype.property, and_true, *]
  obtain ⟨code, hCode⟩ := P.encoding_exists n env
  let r := RelationFormula.truth P n formula
  have copied := jMap_maintainsEncoding hM closed P hCode
  exact (pointwise env).symm.trans ((RelationFormula.truth_correct P formula bound' hCode).symm.trans
    ((LocalRelation.reflects hM closed r (jMap_edge hM closed code) (jMap_edge hM closed code)).trans
      ((RelationFormula.truth_correct P formula bound' copied).trans
        (pointwise (jMap hM closed ∘ env)))))

end PalomarI3380.SquareRepresentation
