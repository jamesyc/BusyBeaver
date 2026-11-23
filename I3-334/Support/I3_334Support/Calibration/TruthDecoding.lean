module
public import I3_334Support.Calibration.GraphValuations
public import I3_334Support.Arithmetic.SetInduction
@[expose] public section

namespace PalomarI3380.Calibration.CodedGraph

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

noncomputable def atomInputDef (kind : Nat) : 𝚺ᴬ₁.Semisentence 4 :=
  .mkSigma “atom formula assignment fallback. ∃ raw k r terms values,
    !subDef raw formula 1 ∧ !pair₄Def raw ↑kind k r terms ∧
    !valuesDef values terms assignment fallback ∧ !pair₃Def atom k r values”

def unaryInputDef (kind : Nat) : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “formula sub. ∃ raw, !pairDef raw ↑kind sub ∧ formula=raw+1”

def binaryInputDef (kind : Nat) : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “formula p q. ∃ raw, !pair₃Def raw ↑kind p q ∧ formula=raw+1”

def pushInputDef : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “out x assignment. ∃ b f next, !pairDef assignment b f ∧ !adjoinDef next x b ∧ !pairDef out next f”

def truthInputDef : 𝚺ᴬ₁.Semisentence 1 :=
  .mkSigma “formula. ∃ raw, !pairDef raw 2 0 ∧ formula=raw+1”

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def pushBound (x assignment : M) : M := ⟪x ∷ π₁ assignment,π₂ assignment⟫

theorem pair3_match (x a b c : M) :
    x=⟪a,b,c⟫ ↔ a=π₁ x ∧ b=π₁ (π₂ x) ∧ c=π₂ (π₂ x) := by
  constructor
  · rintro rfl; simp
  · rintro ⟨rfl,rfl,rfl⟩; rw [pair_unpair,pair_unpair]

theorem pair4_match (x a b c d : M) :
    x=⟪a,b,c,d⟫ ↔ a=π₁ x ∧ b=π₁ (π₂ x) ∧ c=π₁ (π₂ (π₂ x)) ∧ d=π₂ (π₂ (π₂ x)) := by
  constructor
  · rintro rfl; simp
  · rintro ⟨rfl,rfl,rfl,rfl⟩; rw [pair_unpair,pair_unpair,pair_unpair]

theorem atomInput_eval (kind : Nat) (atom formula assignment fallback : M) :
    (atomInputDef kind).val.Evalb ![atom,formula,assignment,fallback] ↔
    (kind : M)=π₁ (formula-1) ∧
      ∃ values, Values values (π₂ (π₂ (π₂ (formula-1)))) assignment fallback ∧
        atom=⟪π₁ (π₂ (formula-1)),π₁ (π₂ (π₂ (formula-1))),values⟫ := by
  simp [atomInputDef,values_eval,sub_defined.iff,pair₄_defined.iff,pair₃_defined.iff,
    pair4_match,numeral_eq_natCast]

theorem unaryInput_eval (kind : Nat) (formula sub : M) :
    (unaryInputDef kind).val.Evalb ![formula,sub] ↔ formula=⟪(kind : M),sub⟫+1 := by
  simp [unaryInputDef,pair_defined.iff,numeral_eq_natCast]

theorem binaryInput_eval (kind : Nat) (formula p q : M) :
    (binaryInputDef kind).val.Evalb ![formula,p,q] ↔ formula=⟪(kind : M),p,q⟫+1 := by
  simp [binaryInputDef,pair₃_defined.iff,numeral_eq_natCast]

theorem pushInput_eval (out x assignment : M) :
    pushInputDef.val.Evalb ![out,x,assignment] ↔ out=pushBound x assignment := by
  have split (code l r : M) : code=⟪l,r⟫ ↔ l=π₁ code ∧ r=π₂ code := by
    constructor
    · rintro rfl; simp
    · rintro ⟨rfl,rfl⟩; rw [pair_unpair]
  simp [pushInputDef,pair_defined.iff,split,adjoin_defined.iff,pushBound]
  exact ⟨fun ⟨a,b⟩ => ⟨b,a.symm⟩,fun ⟨a,b⟩ => ⟨b.symm,a⟩⟩

theorem truthInput_eval (formula : M) :
    truthInputDef.val.Evalb ![formula] ↔ formula=(^⊤ : M) := by
  simp [truthInputDef,pair_defined.iff,qqVerum]

end PalomarI3380.Calibration.CodedGraph
