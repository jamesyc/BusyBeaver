module
public import I0451.Logic.ElementarySets

/-! Empty set and successor are preserved by elementary self-maps
of transitive sets. Consequently a critical point cannot be a natural
ordinal, including a nonstandard one in a model of ZF. -/
@[expose] public section
namespace I0451.Logic.ZFModel

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.AssignmentCode

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "E" => (fun (x y : V) => x ∈ y)

theorem elementary_preserves_empty {d : V} (transitive : IsTransitive d)
    {j : Domain E d → Domain E d} (elementary : Identity.Elementary (domainMem d) j)
    (p : Domain E d) (empty : p.val = ∅) : (j p).val = ∅ := by
  let f : Identity.Formula 1 := .universal (.negation (.mem 0 1))
  have evaluates (q : Domain E d) : f.eval (domainMem d) (fun _ => q) ↔ q.val = ∅ := by
    simp only [f, Identity.Formula.eval_universal, Identity.Formula.eval_negation, Identity.Formula.eval]
    change (∀ u : Domain E d, u.val ∉ q.val) ↔ q.val = ∅
    constructor
    · intro proof
      apply isEmpty_iff_eq_empty.mp
      exact fun y h => proof ⟨y, transitive.transitive q.val q.property y h⟩ h
    · intro eq
      simp [eq]
  exact (evaluates (j p)).mp ((elementary f (fun _ => p)).mp ((evaluates p).mpr empty))

def successorFormula : Identity.Formula 2 :=
  .universal (.conjunction
    (.imp (.mem 0 1) (.imp (.negation (.eq 0 2)) (.mem 0 2)))
    (.conjunction (.imp (.eq 0 2) (.mem 0 1)) (.imp (.mem 0 2) (.mem 0 1))))

theorem successorFormula_eval {d : V} (transitive : IsTransitive d) (p x : Domain E d) :
    successorFormula.eval (domainMem d) ![p,x] ↔ p.val = succ x.val := by
  classical
  simp only [successorFormula, Identity.Formula.eval_universal, Identity.Formula.eval_conjunction,
    Identity.Formula.eval_negation, Identity.Formula.eval]
  change (∀ z : Domain E d,
    (z.val ∈ p.val → z ≠ x → z.val ∈ x.val) ∧ (z = x → z.val ∈ p.val) ∧
      (z.val ∈ x.val → z.val ∈ p.val)) ↔ _
  constructor
  · intro rule
    apply mem_ext_iff.mpr
    intro z
    rw [mem_succ_iff]
    constructor
    · intro member
      let q : Domain E d := ⟨z, transitive.transitive p.val p.property z member⟩
      by_cases same : q = x
      · exact .inl (congrArg Subtype.val same)
      · exact .inr ((rule q).1 member same)
    · rintro (rfl | member)
      · exact (rule x).2.1 rfl
      · exact (rule ⟨z, transitive.transitive x.val x.property z member⟩).2.2 member
  · intro eq z
    have mem : z.val ∈ p.val ↔ z = x ∨ z.val ∈ x.val := by rw [eq, mem_succ_iff, Subtype.ext_iff]
    exact ⟨fun h other => (mem.mp h).resolve_left other, fun equal => mem.mpr (.inl equal),
      fun inside => mem.mpr (.inr inside)⟩

theorem elementary_preserves_successor {d : V} (transitive : IsTransitive d)
    {j : Domain E d → Domain E d} (elementary : Identity.Elementary (domainMem d) j)
    (p x : Domain E d) (eq : p.val = succ x.val) :
    (j p).val = succ (j x).val := by
  apply (successorFormula_eval transitive (j p) (j x)).mp
  have args : j ∘ ![p,x] = ![j p,j x] := by simp [Matrix.comp_vecCons', Function.comp_def, Matrix.vec_single_eq_const]
  rw [← args]
  exact (elementary successorFormula ![p,x]).mp ((successorFormula_eval transitive p x).mpr eq)

end I0451.Logic.ZFModel
