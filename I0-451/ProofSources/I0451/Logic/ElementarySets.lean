module
public import I0451.Logic.Relativize
public import I0451.Logic.ZFModel
public import I0451.Logic.NaturalBounds

/-! Basic first-order properties of transitive domains and their
elementary self-maps. -/
@[expose] public section
namespace I0451.Logic.ZFModel

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.AssignmentCode

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "E" => (fun (x y : V) => x ∈ y)
abbrev domainMem (d : V) (x y : Domain E d) : Prop := x.val ∈ y.val

def unorderedPairFormula : Identity.Formula 3 :=
  .universal (.conjunction
    (.imp (.mem 0 1) (.imp (.negation (.eq 0 2)) (.eq 0 3)))
    (.conjunction (.imp (.eq 0 2) (.mem 0 1)) (.imp (.eq 0 3) (.mem 0 1))))

theorem unorderedPairFormula_eval {d : V} (transitive : IsTransitive d) (p x y : Domain E d) :
    unorderedPairFormula.eval (domainMem d) ![p,x,y] ↔ p.val = ({x.val, y.val} : V) := by
  classical
  simp only [unorderedPairFormula, Identity.Formula.eval_universal,
    Identity.Formula.eval_conjunction, Identity.Formula.eval_negation, Identity.Formula.eval]
  change (∀ z : Domain E d,
    (z.val ∈ p.val → z ≠ x → z = y) ∧ (z = x → z.val ∈ p.val) ∧ (z = y → z.val ∈ p.val)) ↔ _
  constructor
  · intro h
    apply mem_ext_iff.mpr
    intro z
    constructor
    · intro member
      let index : Domain E d := ⟨z, transitive.transitive _ p.property z member⟩
      by_cases same : index = x
      · exact mem_insert.mpr (.inl (congrArg Subtype.val same))
      · have other := (h index).1 member same
        exact mem_insert.mpr (.inr (by simpa using congrArg Subtype.val other))
    · intro member
      rcases (show z = x.val ∨ z = y.val by simpa using member) with rfl | rfl
      · exact (h x).2.1 rfl
      · exact (h y).2.2 rfl
  · intro eq z
    have iffPair : z.val ∈ p.val ↔ z = x ∨ z = y := by
      rw [eq]
      simp [Subtype.ext_iff]
    exact ⟨fun h different => ((iffPair.mp h).resolve_left different),
      fun h => iffPair.mpr (.inl h), fun h => iffPair.mpr (.inr h)⟩

theorem elementary_preserves_pair {d : V} (transitive : IsTransitive d)
    {j : Domain E d → Domain E d} (elementary : Identity.Elementary (domainMem d) j)
    {p x y : Domain E d} (eq : p.val = ({x.val, y.val} : V)) :
    (j p).val = ({(j x).val, (j y).val} : V) := by
  apply (unorderedPairFormula_eval transitive (j p) (j x) (j y)).mp
  have args : j ∘ ![p,x,y] = ![j p,j x,j y] := by simp [Matrix.comp_vecCons', Function.comp_def, Matrix.vec_single_eq_const]
  rw [← args]
  exact (elementary unorderedPairFormula ![p,x,y]).mp ((unorderedPairFormula_eval transitive p x y).mpr eq)

theorem pair_components_in {d x y : V} (transitive : IsTransitive d) (member : ⟨x,y⟩ₖ ∈ d) :
    x ∈ d ∧ y ∈ d := by
  have xy : ({x,y} : V) ∈ d := transitive.transitive _ member _ (by simp [kpair])
  exact ⟨transitive.transitive _ xy _ (by simp), transitive.transitive _ xy _ (by simp)⟩

theorem elementary_preserves_kpair {d : V} (transitive : IsTransitive d)
    {j : Domain E d → Domain E d} (elementary : Identity.Elementary (domainMem d) j)
    {p x y : Domain E d} (eq : p.val = ⟨x.val,y.val⟩ₖ) :
    (j p).val = ⟨(j x).val,(j y).val⟩ₖ := by
  let u : Domain E d := ⟨{x.val}, transitive.transitive p.val p.property _ (by simp [eq, kpair])⟩
  let v : Domain E d := ⟨{x.val,y.val}, transitive.transitive p.val p.property _ (by simp [eq, kpair])⟩
  have head := elementary_preserves_pair transitive elementary (p := u) (x := x) (y := x)
    (by simp [u])
  have tail := elementary_preserves_pair transitive elementary (p := v) (x := x) (y := y) rfl
  have both := elementary_preserves_pair transitive elementary (p := p) (x := u) (y := v) eq
  simpa [kpair, head, tail] using both

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem elementary_preserves_subset {d : V} (transitive : IsTransitive d)
    {j : Domain E d → Domain E d} (elementary : Identity.Elementary (domainMem d) j)
    (a b : Domain E d) : a.val ⊆ b.val ↔ (j a).val ⊆ (j b).val := by
  let formula : Identity.Formula 2 := .universal (.imp (.mem 0 1) (.mem 0 2))
  have evaluate (x y : Domain E d) : formula.eval (domainMem d) ![x,y] ↔ x.val ⊆ y.val := by
    simp only [formula, Identity.Formula.eval_universal, Identity.Formula.eval]
    change (∀ z : Domain E d, z.val ∈ x.val → z.val ∈ y.val) ↔ _
    exact ⟨fun h z hz => h ⟨z, transitive.transitive x.val x.property z hz⟩ hz,
      fun h z => h z.val⟩
  have args : j ∘ ![a,b] = ![j a,j b] := by simp [Matrix.comp_vecCons', Function.comp_def, Matrix.vec_single_eq_const]
  exact (evaluate a b).symm.trans (((by rw [← args]; exact elementary formula ![a,b] :
    formula.eval (domainMem d) ![a,b] ↔ formula.eval (domainMem d) ![j a,j b])).trans (evaluate (j a) (j b)))

theorem elementary_fixed_pair_components {d : V} (transitive : IsTransitive d)
    {j : Domain E d → Domain E d} (elementary : Identity.Elementary (domainMem d) j)
    {p x y : Domain E d} (pair : p.val = ⟨x.val,y.val⟩ₖ) (fixed : j p = p) :
    j x = x ∧ j y = y := by
  have next := elementary_preserves_kpair transitive elementary (p := p) (x := x) (y := y) pair
  have same := kpair_inj (next.symm.trans ((congrArg Subtype.val fixed).trans pair))
  exact ⟨Subtype.ext same.1, Subtype.ext same.2⟩

def restrictToMember {d : V} (transitive : IsTransitive d) {j : Domain E d → Domain E d}
    (elementary : Identity.Elementary (domainMem d) j) {M : Domain E d} (fixed : j M = M) :
    Domain E M.val → Domain E M.val :=
  fun x =>
    let lifted : Domain E d := ⟨x.val, transitive.transitive M.val M.property x.val x.property⟩
    ⟨(j lifted).val, (congrArg (fun m : Domain E d => (j lifted).val ∈ m.val) fixed).mp
      ((elementary.mem_iff lifted M).mp x.property)⟩

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem restrictToMember_elementary {d : V} (transitive : IsTransitive d) {j : Domain E d → Domain E d}
    (elementary : Identity.Elementary (domainMem d) j) {M : Domain E d} (fixed : j M = M) :
    Identity.Elementary (domainMem M.val) (restrictToMember transitive elementary fixed) := by
  let points : {x : Domain E d // domainMem d x M} ≃ Domain E M.val :=
    { toFun := fun z => ⟨z.val.val, z.property⟩
      invFun := fun z => ⟨⟨z.val, transitive.transitive M.val M.property z.val z.property⟩, z.property⟩
      left_inv := fun z => Subtype.ext (Subtype.ext rfl)
      right_inv := fun z => Subtype.ext rfl }
  intro n formula v
  exact Identity.Elementary.transport (E' := domainMem M.val) (j' := restrictToMember transitive elementary fixed)
    (Identity.Elementary.restricted elementary fixed) points (fun _ _ => Iff.rfl) (fun _ => Subtype.ext rfl) (n := n) formula v

end I0451.Logic.ZFModel
