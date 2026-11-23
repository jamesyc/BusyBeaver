module
public import I3_334.Proof.RankPreservation
public import I3_334.Proof.Ground
public import I3_334Support.Equations.EquationalConsistency
@[expose] public section

namespace PalomarI3334.ForwardModel

open PalomarI3380 PalomarI3380.Logic PalomarI3380.Logic.Expanded
open PalomarI3380.SquareRepresentation Templates

variable {V : Type} {E G : V → V → Prop}
variable (L : ClassAxioms E G) (inhabited : Nonempty V)

local notation "Ctx" => (L.context inhabited)
local notation "R" => ClassRelation E G
local infixl:70 " ⋆ " => ClassRelation.product

noncomputable def algebra (stage j : V) : NativeAlgebra R where
  domain := .rankDiagonal stage
  embedding := EquationModel.embedding L inhabited j
  membership := .member
  seed := .member ⋆ .rankDiagonal stage
  identity := .one
  neg := .complement
  converse := .converse
  choice := EquationModel.select L inhabited
  nand := .nand
  product := .product
  other _ _ := .top

theorem seed_holds (stage : V) (x y : V) :
    (ClassRelation.member (E := E) (G := G) ⋆ .rankDiagonal stage).holds x y ↔ E x y ∧ E y stage := by
  change (∃ z, E x z ∧ z = y ∧ E z stage) ↔ _
  exact ⟨fun ⟨_, edge, same, inStage⟩ => same ▸ ⟨edge, inStage⟩,
    fun ⟨edge, inStage⟩ => ⟨y, edge, rfl, inStage⟩⟩

def safeValue (stage : V) : SafeTerm → R
  | .seed => .member ⋆ .rankDiagonal stage
  | .one => .one
  | .top => .top
  | .neg t => (safeValue stage t).complement
  | .converse t => (safeValue stage t).converse
  | .nand t u => (safeValue stage t).nand (safeValue stage u)
  | .product t u => safeValue stage t ⋆ safeValue stage u

theorem safeValue_holds (stage : V) (t : SafeTerm) (x y : V) :
    (safeValue (E := E) (G := G) stage t).holds x y ↔ t.rel (fun a b => E a b ∧ E b stage) x y := by
  induction t generalizing x y with
  | seed => exact seed_holds stage x y
  | one | top => rfl
  | neg t ih => exact not_congr (ih x y)
  | converse t ih => exact ih y x
  | nand t u it iu => exact not_congr (and_congr (it x y) (iu x y))
  | product t u it iu =>
    change (∃ z, (safeValue stage t : R).holds x z ∧ (safeValue stage u : R).holds z y) ↔ _
    exact exists_congr fun z => and_congr (it x z) (iu z y)

theorem safe_operation (stage j : V) (tag : Nat) (terms : List SafeTerm) (h : 3 ≤ tag) :
    (algebra L inhabited stage j).operation tag (terms.map (safeValue stage)) =
      safeValue stage (SafeTerm.fromOp tag terms) := by
  have tags : tag = 3 ∨ tag = 4 ∨ tag = 5 ∨ 6 ≤ tag := by omega
  rcases tags with rfl | rfl | rfl | h
  all_goals
    try
      obtain ⟨n, eq⟩ := Nat.exists_eq_add_of_le h
      rw [eq, Nat.add_comm 6]
    cases terms with
    | nil => rfl
    | cons t rest =>
      cases rest with
      | nil => rfl
      | cons u other => cases other <;> rfl

theorem eval_guarded (stage j : V) : (t : RawTerm) → Guarded t →
    (algebra L inhabited stage j).evalRaw t = safeValue stage (SafeTerm.ofRaw t)
  | .app tag children, safe => by
    have tagSafe := safe ⟨children.length, tag⟩ (by simp)
    rw [NativeAlgebra.evalRaw_app]
    have childValues : children.map (algebra L inhabited stage j).evalRaw =
        (children.map SafeTerm.ofRaw).map (safeValue stage) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro child mem
      apply eval_guarded stage j child
      intro tok inside
      apply safe
      simp only [RawTerm.tokens_app, List.mem_cons, List.mem_flatMap]
      exact .inr ⟨child, mem, inside⟩
    rw [childValues]
    exact (safe_operation L inhabited stage j tag _ tagSafe).trans
      (congrArg (safeValue stage) (RawTerm.fold_app SafeTerm.fromOp tag children).symm)
termination_by t _ => sizeOf t
decreasing_by have h := List.sizeOf_lt_of_mem mem; simp_wf; omega

theorem guarded_preserved {w height stage j : V} (omega : Internal.Omega E w)
    (rank : (Ctx).Rank height stage)
    (mapping : Internal.FunctionInto E j stage stage)
    (elementary : Internal.ElementaryOnRank E w stage j)
    (t : RawTerm) (safe : Guarded t) {x y u v : V}
    (left : Internal.At E j x u) (right : Internal.At E j y v)
    (edge : ((algebra L inhabited stage j).evalRaw t).holds x y) :
    ((algebra L inhabited stage j).evalRaw t).holds u v := by
  let D := fun z => E z stage
  have hx : D x := SetRecursion.at_domain (N := Ctx) mapping.1 left
  have hy : D y := SetRecursion.at_domain (N := Ctx) mapping.1 right
  let ix : RankPreservation.In D := ⟨x,hx⟩
  let iy : RankPreservation.In D := ⟨y,hy⟩
  let outside : RankPreservation.Out D := ⟨stage,(Ctx).rank_no_self rank⟩
  let graph (a : RankPreservation.In D) := mapping.1.1 a.val a.property
  let f (a : RankPreservation.In D) : RankPreservation.In D :=
    ⟨Classical.choose (graph a), mapping.2 _ a.property _ (Classical.choose_spec (graph a)).1⟩
  have hf (a : RankPreservation.In D) : Internal.At E j a.val (f a).val :=
    (Classical.choose_spec (graph a)).1
  have ux : (f ix).val = u := ((Classical.choose_spec (graph ix)).2 _ left).symm
  have vy : (f iy).val = v := ((Classical.choose_spec (graph iy)).2 _ right).symm
  have elem p (env : Fin 3 → RankPreservation.In D) :
      LocalFormula.eval (fun a b => E a.val b.val) (fun _ => True) p env ↔
        LocalFormula.eval (fun a b => E a.val b.val) (fun _ => True) p (f ∘ env) := by
    have rel (values : Fin 3 → RankPreservation.In D) :
        LocalFormula.eval (fun a b => E a.val b.val) (fun _ => True) p values ↔
          LocalFormula.eval E D p (Subtype.val ∘ values) :=
      Logic.eval_along Subtype.val (fun _ _ h => Subtype.ext h) E D
        (fun point => ⟨fun h => ⟨⟨point,h⟩, rfl⟩, fun ⟨a, eq⟩ => eq ▸ a.property⟩)
        p values
    exact (rel env).trans (((Ctx).embedding_preserves_local omega mapping elementary p
      (Subtype.val ∘ env) (Subtype.val ∘ f ∘ env) (fun i => (env i).property)
      (fun i => hf (env i))).trans (rel _).symm)
  have invariant := RankPreservation.preserves D E
    (fun x y edge inStage => (Ctx).rank_transitive rank y inStage x edge)
    f ix outside elem (SafeTerm.ofRaw t) ix iy
  rw [eval_guarded L inhabited stage j t safe] at edge ⊢
  apply (safeValue_holds stage (SafeTerm.ofRaw t) u v).mpr
  simpa only [ux, vy] using invariant.mp ((safeValue_holds stage (SafeTerm.ofRaw t) x y).mp edge)


private theorem complement_nand (r s : R) : (r.nand s).complement = r.meet s :=
  ClassRelation.ext fun _ _ => Classical.not_not

private theorem nand_top (r s : R) (disjoint : ∀ x y, r.holds x y → s.holds x y → False) :
    r.nand s = ClassRelation.top :=
  ClassRelation.ext fun x y => ⟨fun _ => trivial, fun _ h => disjoint x y h.1 h.2⟩

private theorem product_assoc (r s t : R) : r ⋆ (s ⋆ t) = r ⋆ s ⋆ t :=
  ClassRelation.ext fun _ _ =>
    ⟨fun ⟨u, edge, v, middle, last⟩ => ⟨v, ⟨u, edge, middle⟩, last⟩,
      fun ⟨v, ⟨u, edge, middle⟩, last⟩ => ⟨u, edge, v, middle, last⟩⟩

private theorem meet_top : (ClassRelation.top : R).meet ClassRelation.top = ClassRelation.top :=
  ClassRelation.ext fun _ _ => ⟨fun _ => trivial, fun _ => ⟨trivial, trivial⟩⟩

open Manifest in
theorem models {w height stage j : V} (omega : Internal.Omega E w)
    (rank : (Ctx).Rank height stage) (limit : Internal.Inductive E height)
    (mapping : Internal.FunctionInto E j stage stage)
    (elementary : Internal.ElementaryOnRank E w stage j) (minimum : ClassMinimum E G) :
    (algebra L inhabited stage j).Models := by
  let old := EquationModel.algebra L inhabited stage j
  have oldModel : old.Models preceding :=
    EquationModel.models_preceding L inhabited omega rank limit mapping elementary minimum
  let M := algebra L inhabited stage j
  let choose := EquationModel.select L inhabited
  let embedding := EquationModel.embedding L inhabited j
  let e : R := ClassRelation.member
  let i : R := ClassRelation.one
  let t : R := ClassRelation.subset
  let u : R := ClassRelation.top
  let s : R := EquationModel.stages L inhabited
  let dom : R := ClassRelation.rankDiagonal stage
  have oldChoose (a : R) : (choose a).meet a = choose a := by
    apply ClassRelation.ext
    intro x y
    exact ⟨And.left, fun h => ⟨h, EquationModel.select_sub L inhabited a h⟩⟩
  have max : e.complement.nand e = u := by
    apply nand_top
    intro x y hn hp
    exact hn hp
  have subset : (e.converse ⋆ e.complement).complement = t :=
    (oldModel defineSubset (by simp [preceding]) (fun _ => u)).symm
  have stageDef : (choose t).converse ⋆ choose t = s :=
    (oldModel defineStages (by simp [preceding]) (fun _ => u)).symm
  have diag : s.converse = s := by
    apply ClassRelation.ext
    intro x y
    change (y = x ∧ ∃ b, (Ctx).Rank b y) ↔ (x = y ∧ ∃ b, (Ctx).Rank b x)
    exact ⟨fun ⟨h, hr⟩ => ⟨h.symm, h ▸ hr⟩, fun ⟨h, hr⟩ => ⟨h.symm, h ▸ hr⟩⟩
  have transpose (r s : R) : (r ⋆ s).converse = s.converse ⋆ r.converse :=
    ClassRelation.ext fun _ _ => exists_congr fun _ => and_comm
  have stageLaw' : t ⋆ (s ⋆ (e ⋆ s)) = e ⋆ s := by
    have law : s ⋆ e.converse = s ⋆ e.converse ⋆ s ⋆ t.converse :=
      EquationModel.stages_law L inhabited
    have both := congrArg ClassRelation.converse law
    have involution (r : R) : r.converse.converse = r := rfl
    simpa only [transpose, diag, involution] using both.symm
  have domainEq : (i.nand (embedding ⋆ u)).complement = dom :=
    (oldModel defineDomain (by simp [preceding, retained]) (fun _ => u)).symm
  have closeEq : (i.nand (e ⋆ dom ⋆ (s ⋆ u))).complement = dom := by
    have eq := (oldModel domainClosed (by simp [preceding, retained]) (fun _ => u)).symm
    change (i.nand (e ⋆ (s.nand dom).complement ⋆ u)).complement = dom at eq
    rw [complement_nand s dom] at eq
    have one : dom ⋆ s = s.meet dom := by
      apply ClassRelation.ext
      intro x y
      change (∃ z, (x = z ∧ E x stage) ∧ s.holds z y) ↔ s.holds x y ∧ (x = y ∧ E x stage)
      constructor
      · rintro ⟨z, ⟨rfl, inStage⟩, hs⟩
        exact ⟨hs, hs.1, inStage⟩
      · rintro ⟨hs, ⟨rfl, inStage⟩⟩
        exact ⟨x, ⟨rfl, inStage⟩, hs⟩
    rw [product_assoc, ← product_assoc e dom s, one]
    exact eq
  apply NativeAlgebra.models_of_raw
  intro eq listed a b c d safe
  let values := NativeAlgebra.valuation a b c (M.evalRaw d)
  simp only [equations, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with h | h | h | h | h | h | h | h | h | h <;> subst eq
  · rfl
  · exact oldModel Manifest.rightIdentity (by simp [preceding, retained]) (fun _ => a)
  · have image : (((e.converse ⋆ choose a).complement ⋆ e).complement.meet
        ((e.converse ⋆ choose a ⋆ e.complement).complement)) ⋆ u = u := by
      have law : ((e.converse ⋆ choose a ⋆ e.complement).complement.meet
            (((e.converse ⋆ choose a).complement ⋆ e).complement)) ⋆ u = u := by
        have eq := oldModel Manifest.imageEquation (by simp [preceding, retained]) (fun _ => a)
        change (((e.converse ⋆ choose a ⋆ e.complement).complement.nand
          ((e.converse ⋆ choose a).complement ⋆ e).complement).complement) ⋆ u = u at eq
        rwa [complement_nand] at eq
      have comm (r s : R) : r.meet s = s.meet r :=
        ClassRelation.ext fun _ _ => and_comm
      rw [comm] at law
      exact law
    have adjoint : (a.converse ⋆ ((a ⋆ b).complement.meet c)).nand b = u := by
      apply nand_top
      rintro x y ⟨z, za, missing, _⟩ edge
      exact missing ⟨x, za, edge⟩
    have preservation : (M.evalRaw d ⋆ embedding).nand (embedding ⋆ (M.evalRaw d).complement) = u := by
      apply nand_top
      rintro x y ⟨z, xz, zy⟩ ⟨q, xq, missing⟩
      exact missing (guarded_preserved L inhabited omega rank mapping elementary d safe xq zy xz)
    have covered : a.nand (choose a ⋆ u).complement = u := by
      apply nand_top
      intro x y edge missing
      obtain ⟨z, selected⟩ := EquationModel.select_exists L inhabited minimum omega a x ⟨y, edge⟩
      exact missing ⟨z, selected, trivial⟩
    have functional : ((choose a).converse ⋆ choose a).nand i.complement = u := by
      apply nand_top
      rintro x y ⟨z, left, right⟩ different
      exact different (EquationModel.select_function L inhabited minimum a left right)
    have extensional : t.converse.nand (t.meet i.complement) = u := by
      apply nand_top
      rintro x y inclusion ⟨reverse, different⟩
      exact different ((Ctx).ext x y (fun z => ⟨reverse z, inclusion z⟩))
    change (M.meet (M.eval values factorImage) (M.meet (M.eval values factorAdjunction)
      (M.meet (M.eval values factorPreservation) (M.meet (M.eval values factorCoverage)
        (M.meet (M.eval values factorFunction) (M.eval values factorExtensionality)))))) =
      e.complement.nand e
    have fi : M.eval values factorImage = u := by
      change (((e.converse ⋆ ((choose a).nand a).complement).complement ⋆ e).complement.nand
          (e.converse ⋆ (((choose a).nand a).complement ⋆ e.complement)).complement).complement ⋆
            e.complement.nand e = u
      rw [complement_nand, complement_nand, oldChoose, max, product_assoc]
      exact image
    have fa : M.eval values factorAdjunction = u := by
      change (a.converse ⋆ ((a ⋆ b).complement.nand c).complement).nand b = u
      rw [complement_nand]
      exact adjoint
    have fp : M.eval values factorPreservation = u := preservation
    have fc : M.eval values factorCoverage = u := by
      change a.nand (((choose a).nand a).complement ⋆ e.complement.nand e).complement = u
      rwa [max, complement_nand, oldChoose]
    have ff : M.eval values factorFunction = u := functional
    have fe : M.eval values factorExtensionality = u := by
      change ((e.converse ⋆ e.complement).complement).converse.nand
        (((e.converse ⋆ e.complement).complement).nand i.complement).complement = u
      rwa [subset, complement_nand]
    have unit : M.meet u u = u := (complement_nand u u).trans meet_top
    rw [fi, fa, fp, fc, ff, fe, max]
    simp only [unit]
  · change (e.converse ⋆ e.complement).complement ⋆
      (((choose (e.converse ⋆ e.complement).complement).converse ⋆ choose (e.converse ⋆ e.complement).complement) ⋆
        (e ⋆ ((choose (e.converse ⋆ e.complement).complement).converse ⋆
          choose (e.converse ⋆ e.complement).complement))) =
      e ⋆ ((choose (e.converse ⋆ e.complement).complement).converse ⋆ choose (e.converse ⋆ e.complement).complement)
    rwa [subset, stageDef]
  · exact (oldModel meredith1 (by simp [preceding]) (fun v => if v.val = 0 then a else b)).symm
  · exact product_assoc a b c
  · change (i.nand (embedding ⋆ e.complement.nand e)).complement = dom
    rwa [max]
  · exact (oldModel meredith2 (by simp [preceding]) (fun v =>
      if v.val = 0 then a else if v.val = 1 then b else c)).symm
  · change (i.nand (e ⋆ dom ⋆ (((choose (e.converse ⋆ e.complement).complement).converse ⋆
      choose (e.converse ⋆ e.complement).complement) ⋆ e.complement.nand e))).complement = dom
    rwa [max, subset, stageDef]
  · rfl

include L inhabited in
theorem underivability (minimum : ClassMinimum E G) (large : Internal.HasI3 E) :
    ¬ Derives (.app 1 []) (.app 0 []) := by
  obtain ⟨w,height,stage,j,omega,rank,limit,mapping,⟨x,y,_,_,edge,different⟩,elementary⟩ := large
  have realRank := (Ctx).rank_from_internal (L.ordinary.foundation (fun _ => (Ctx).empty)) rank
  let M := algebra L inhabited stage j
  have isModel := models L inhabited omega realRank limit mapping elementary minimum
  intro proof
  have equality := proof.sound isModel
  simp only [NativeAlgebra.evalRaw_app, List.map_nil, NativeAlgebra.operation] at equality
  have fromGraph : (EquationModel.embedding L inhabited j).holds x y := edge
  change (ClassRelation.rankDiagonal stage : R) = EquationModel.embedding L inhabited j at equality
  rw [← equality] at fromGraph
  exact different fromGraph.1

end PalomarI3334.ForwardModel

namespace PalomarI3334

open PalomarI3380 PalomarI3380.Logic PalomarI3380.Logic.Expanded
open PalomarI3380.SquareRepresentation.SetContext

theorem guarded_underivability_of_consistency (h : ZFCI3Consistent) :
    ¬ Derives (.app 1 []) (.app 0 []) := by
  obtain ⟨V,E,⟨enumerated⟩,model⟩ := countable_zfci3_model_of_consistency h
  let v := enumerated.get 0
  have nonempty : Nonempty V := ⟨v⟩
  have ordinary : ZFCModel E := fun p hp => model p
    (hp.elim Or.inl (fun h => Or.inr (Or.inl h)))
  have large : Internal.HasI3 E :=
    (SetFormula.holds_i3 (E := E) (env := fun _ => v)).mp (model _ (Or.inr (Or.inr rfl)) _)
  obtain ⟨G,axioms,minimum⟩ := OrdinaryContext.amenable_global_order ordinary nonempty enumerated
  exact ForwardModel.underivability axioms nonempty minimum large

end PalomarI3334
