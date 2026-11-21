module
public import I3_380.Calibration.CanonicalTerms
@[expose] public section

namespace PalomarI3380.Calibration.TermWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

/-- The operations on the quotient use the original defining terms
for the two stage constants removed by the compiler. -/
def operationTerm : {k : Nat} → FunctionSymbol k → PalomarI3380.Term (Fin k)
  | _, .constant c => Manifest.expand (.const c)
  | _, .complement => .neg (.var 0)
  | _, .choose => .choice (.var 0)
  | _, .localRelation => .localRel (.var 0)
  | _, .converse => .converse (.var 0)
  | _, .nand => .nand (.var 0) (.var 1)
  | _, .product => .product (.var 0) (.var 1)
  | _, .node => .node (.var 0) (.var 1) (.var 2)

theorem operationTerm_eval {A : Type} (model : Algebra A) (chosen : A → Prop)
    {k : Nat} (symbol : FunctionSymbol k) (input : Fin k → A) :
    model.eval input (operationTerm symbol) =
      @Tarski.Structure.func FilterLanguage A (structureOf model.withStages chosen) k symbol input := by
  cases symbol with
  | constant c => exact Algebra.eval_expand model input (.const c)
  | _ => rfl

noncomputable def termValueDef {k : Nat} (t : PalomarI3380.Term (Fin k)) : 𝚺ᴬ₁.Semisentence 1 :=
  .mkSigma “entry. ∃ out args raw,
    !adjoinDef entry out args ∧ !(instantiateDef t) raw args ∧ !sameCodeDef out raw”

noncomputable def operationGraphDef {k : Nat} (symbol : FunctionSymbol k) : 𝚺ᴬ₁.Semisentence 1 :=
  termValueDef (operationTerm symbol)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem termValueDef_eval {k : Nat} (t : PalomarI3380.Term (Fin k)) (out args : M) :
    (termValueDef t).val.Evalb ![out ∷ args] ↔ SameCode out (instantiate t args) := by
  simp [termValueDef,adjoin_defined.iff,(instantiate_defined (M := M) t).iff,sameCode_eval]

theorem canonicalTermValue_eval {k : Nat} (t : PalomarI3380.Term (Fin k))
    (assignment : Fin (k+1) → CanonicalTerm M) :
    (termValueDef t).val.Evalb ![matrixToVec (fun i => (assignment i).val)] ↔
      canonicalClass (assignment 0) =
        (quotientAlgebra (M := M)).eval (fun i => canonicalClass (assignment i.succ)) t := by
  let input := fun i : Fin k =>
    (⟨(assignment i.succ).val,by simpa using (assignment i.succ).property.1⟩ : GroundTerm M)
  let out := (⟨(assignment 0).val,by simpa using (assignment 0).property.1⟩ : GroundTerm M)
  change (termValueDef t).val.Evalb ![out.val ∷ matrixToVec (fun i => (input i).val)] ↔
    groundClass out = (quotientAlgebra (M := M)).eval (groundClass ∘ input) t
  rw [termValueDef_eval,instantiate_eval,eval_quotient]
  constructor
  · intro related
    exact Quotient.sound related.2.2
  · intro equal
    exact ⟨out.isSemiterm_zero,(groundAlgebra.eval input t).isSemiterm_zero,Quotient.exact equal⟩

theorem canonicalOperation_eval {k : Nat} (symbol : FunctionSymbol k) (chosen : GroundClasses M → Prop)
    (assignment : Fin (k+1) → CanonicalTerm M) :
    (operationGraphDef symbol).val.Evalb ![matrixToVec (fun i => (assignment i).val)] ↔
      canonicalClass (assignment 0) =
      @Tarski.Structure.func FilterLanguage (GroundClasses M)
        (structureOf quotientAlgebra.withStages chosen) k symbol (fun i => canonicalClass (assignment i.succ)) := by
  rw [operationGraphDef,canonicalTermValue_eval,operationTerm_eval _ chosen]

theorem operationGraph_set {V : Type} {E G : V → V → Prop}
    {laws : Logic.Expanded.ClassAxioms E G} {inhabited : Nonempty V}
    (D : Logic.Expanded.OmegaDomain laws inhabited) {k : Nat} (symbol : FunctionSymbol k) :
    ∃ table : V, ∀ entry : D.Points, E entry.val table ↔
      (operationGraphDef symbol).val.Evalb ![entry] := by
  obtain ⟨table,membership⟩ := D.separate_arithmetic (operationGraphDef symbol).val Empty.elim
  refine ⟨table,fun entry => (membership _).trans ?_⟩
  constructor
  · rintro ⟨other,value,checked⟩
    have same : other = entry := Subtype.ext value
    simpa only [same] using checked
  · exact fun checked => ⟨entry,rfl,checked⟩

end PalomarI3380.Calibration.TermWords
