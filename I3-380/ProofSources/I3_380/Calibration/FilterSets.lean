module
public import I3_380.Calibration.CodedUltrafilter
public import I3_380.Calibration.RelationalTheory
@[expose] public section

namespace PalomarI3380.Calibration.TermWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open Logic.Expanded (ClassAxioms OmegaDomain)
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def ChosenCode (seed : CanonicalTerm M) (code : M) : Prop :=
  Canonical code ∧ CodeLe code (unitName (M := M)).val ∧
    ∃ i trace, FilterHistory seed i trace ∧ CodeLe trace.[i] code

theorem chosenCode_definable (seed : CanonicalTerm M) : 𝚺ᴬ_[2]-Predicate (ChosenCode seed) := by
  have canonSigma : ℬ[<,ℒₒᵣ].Hierarchy 𝚺 2 canonicalDef.val :=
    canonicalDef.hierarchy_of_lt (by decide)
  let canon : 𝚺ᴬ_[2].Semisentence 1 := .mkSigma canonicalDef.val canonSigma
  have canonical : 𝚺ᴬ_[2]-Predicate (Canonical (M := M)) :=
    (show 𝚺ᴬ_[2]-Predicate (Canonical (M := M)) via canon from
      .mk fun v => by
        rw [Matrix.fun_eq_vec_one v]
        exact canonical_eval _).to_definable
  have history := filterHistory_definable seed
  have order : 𝚺ᴬ_[2]-Relation (CodeLe (M := M)) :=
    (codeLe_defined (M := M)).of_lt (by decide)
  have indexed : 𝚺ᴬ_[2].Definable (fun v : Fin 3 → M => CodeLe (v 0).[v 1] (v 2)) := by
    apply order.comp _ (.var 2)
    definability
  unfold ChosenCode
  exact canonical.and ((order.comp (.var 0) (.const _)).and
    ((history.comp (.var 1) (.var 0)).and indexed).exsCons.exsCons)

theorem chosenCode_meaning (laws : RelationLaws (stagedAlgebra (M := M))) (seed : CanonicalTerm M)
    (subunit : stagedAlgebra.le (canonicalClass seed) (stagedAlgebra.constant .I))
    (nonzero : canonicalClass seed ≠ stagedAlgebra.zero) (x : CanonicalTerm M) :
    ChosenCode seed x.val ↔ (namedUltrafilter laws seed subunit nonzero).member (canonicalClass x) := by
  unfold ChosenCode
  rw [← namedUltrafilter_member laws seed subunit nonzero]
  exact ⟨And.right,fun member => ⟨x.property,member⟩⟩

variable {V : Type} {E G : V → V → Prop}
    {laws : ClassAxioms E G} {inhabited : Nonempty V} (D : OmegaDomain laws inhabited)

theorem chosen_set :
    letI : D.Points↓[ℒₒᵣ] ⊧* 𝗣𝗔 := D.models_peano
    ∀ seed : CanonicalTerm D.Points, ∃ table : V, ∀ code : D.Points, E code.val table ↔ ChosenCode seed code := by
  letI : D.Points↓[ℒₒᵣ] ⊧* 𝗣𝗔 := D.models_peano
  intro seed
  obtain ⟨formula,meaning⟩ := (chosenCode_definable seed).definable
  obtain ⟨table,atTable⟩ := D.separate_arithmetic formula.val id
  refine ⟨table,fun code => (atTable code.val).trans ?_⟩
  constructor
  · rintro ⟨x,represents,holds⟩
    have same : x=code := Subtype.ext represents
    subst x
    exact (meaning ![code]).mp holds
  · intro h
    exact ⟨code,rfl,(meaning ![code]).mpr h⟩

end PalomarI3380.Calibration.TermWords
