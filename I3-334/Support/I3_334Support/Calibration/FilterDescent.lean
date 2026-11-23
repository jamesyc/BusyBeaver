module
public import I3_334Support.Calibration.CodedOperationGraphs
public import I3_334Support.RelationAlgebra.Representation
@[expose] public section

namespace PalomarI3380.Calibration.TermWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open Manifest (meet)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def meetValueDef : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “out a b. ∃ tail pair entry,
    !adjoinDef tail b 0 ∧ !adjoinDef pair a tail ∧ !adjoinDef entry out pair ∧
    !(termValueDef (meet (.var 0) (.var 1) : PalomarI3380.Term (Fin 2))) entry”

theorem meetValue_eval (out a b : CanonicalTerm M) :
    meetValueDef.val.Evalb ![out.val,a.val,b.val] ↔
      canonicalClass out = (quotientAlgebra (M := M)).withStages.inf (canonicalClass a) (canonicalClass b) := by
  have pure := canonicalTermValue_eval (meet (.var 0) (.var 1) : PalomarI3380.Term (Fin 2)) ![out,a,b]
  change (termValueDef (meet (.var 0) (.var 1) : PalomarI3380.Term (Fin 2))).val.Evalb
    ![out.val ∷ a.val ∷ b.val ∷ 0] ↔ _ at pure
  have graph : (termValueDef (meet (.var 0) (.var 1) : PalomarI3380.Term (Fin 2))).val.Eval
        ![out.val ∷ a.val ∷ b.val ∷ (0 : M)] Empty.elim ↔ _ := pure
  simpa [meetValueDef,adjoin_defined.iff,Manifest.meet,Algebra.eval,Algebra.withStages,Algebra.inf] using graph

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

noncomputable def nameClass (c : GroundClasses M) : CanonicalTerm M :=
  Classical.choose (canonicalClass_surjective c)

@[simp] theorem nameClass_class (c : GroundClasses M) : canonicalClass (nameClass c) = c :=
  Classical.choose_spec (canonicalClass_surjective c)

noncomputable def requestName (i : M) : CanonicalTerm M := by
  classical
  exact if valid : Canonical i then ⟨i,valid⟩ else nameClass ((quotientAlgebra (M := M)).withStages.constant .I)

noncomputable def descendName (current : CanonicalTerm M) (index : M) : CanonicalTerm M := by
  classical
  let alg := (quotientAlgebra (M := M)).withStages
  let part := alg.inf (canonicalClass current) (canonicalClass (requestName index))
  exact if part = alg.zero then current else nameClass part

/-- One descent step, expressed on codes with the names of the unit
and zero supplied as parameters. The function itself is proved total. -/
noncomputable def descentStepDef : 𝚺ᴬ_[2].Semisentence 5 :=
  .mkSigma “index current out unit zero. ∃ request part,
    ((!canonicalDef index ∧ request=index) ∨ (¬!canonicalDef index ∧ request=unit)) ∧
    !canonicalDef part ∧ !meetValueDef part current request ∧
    ((part=zero ∧ out=current) ∨ (part≠zero ∧ out=part))”
    (by
      have canonSigma : ℬ[<,ℒₒᵣ].Hierarchy 𝚺 2 canonicalDef.val :=
        canonicalDef.hierarchy_of_lt (by decide)
      have canonPi : ℬ[<,ℒₒᵣ].Hierarchy 𝚷 2 canonicalDef.val :=
        canonicalDef.hierarchy_of_lt (by decide)
      have meetSigma : ℬ[<,ℒₒᵣ].Hierarchy 𝚺 2 meetValueDef.val :=
        meetValueDef.hierarchy_of_lt (by decide)
      simp [canonSigma,canonPi,meetSigma])

theorem descentStepDef_eval (current : CanonicalTerm M) (index out : M) :
    descentStepDef.val.Evalb ![index,current.val,out,
      (nameClass ((quotientAlgebra (M := M)).withStages.constant .I)).val,
      (nameClass ((quotientAlgebra (M := M)).withStages.zero)).val] ↔
      out = (descendName current index).val := by
  classical
  let alg := (quotientAlgebra (M := M)).withStages
  let unit := nameClass (M := M) (alg.constant .I)
  let zero := nameClass (M := M) alg.zero
  let desired := requestName index
  let intersection := nameClass (alg.inf (canonicalClass current) (canonicalClass desired))
  have requested (r : M) :
      ((Canonical index ∧ r=index) ∨ (¬Canonical index ∧ r=unit.val)) ↔ r=desired.val := by
    by_cases valid : Canonical index <;> simp [desired,requestName,valid,unit,alg]
  have sameZero : intersection.val = zero.val ↔ alg.inf (canonicalClass current) (canonicalClass desired)=alg.zero := by
    constructor
    · intro eq
      have equal : intersection = zero := Subtype.ext eq
      simpa [intersection,zero] using congrArg canonicalClass equal
    · intro eq
      exact congrArg Subtype.val (canonicalClass_injective (by simp [intersection,zero,eq]))
  have next :
      ((intersection.val=zero.val ∧ out=current.val) ∨ (intersection.val≠zero.val ∧ out=intersection.val)) ↔
        out = (descendName current index).val := by
    by_cases empty : alg.inf (canonicalClass current) (canonicalClass desired)=alg.zero <;>
      simp [descendName,desired,alg,intersection,zero,sameZero,empty]
  have semantics : descentStepDef.val.Evalb ![index,current.val,out,unit.val,zero.val] ↔
      ∃ part : M, Canonical part ∧ meetValueDef.val.Evalb ![part,current.val,desired.val] ∧
        ((part=zero.val ∧ out=current.val) ∨ (part≠zero.val ∧ out=part)) := by
    simp [descentStepDef,canonical_eval,requested]
  change descentStepDef.val.Evalb ![index,current.val,out,unit.val,zero.val] ↔ _
  rw [semantics]
  constructor
  · rintro ⟨p,pCanonical,computed,choice⟩
    let part : CanonicalTerm M := ⟨p,pCanonical⟩
    have result : canonicalClass part = alg.inf (canonicalClass current) (canonicalClass desired) :=
      (meetValue_eval part current desired).mp computed
    have proof : part = intersection := canonicalClass_injective (by simpa [intersection] using result)
    have code : p = intersection.val := congrArg Subtype.val proof
    exact next.mp (code ▸ choice)
  · intro verified
    refine ⟨intersection.val,intersection.property,?_ ,next.mpr verified⟩
    exact (meetValue_eval intersection current desired).mpr (by simp [intersection,alg])

end PalomarI3380.Calibration.TermWords
