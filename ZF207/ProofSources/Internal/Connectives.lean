module
public import Internal.Codes
@[expose] public section
/-! # Derived connectives on codes in a model of arithmetic -/
namespace ZF207.Internal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Derived connectives in `V`, as in `CKernel.Generic.Codes`. -/
noncomputable def cneg (a : V) : V := imp a 1
noncomputable def cand (a b : V) : V := cneg (imp a (cneg b))
noncomputable def cor (a b : V) : V := imp (cneg a) b
noncomputable def cex (x a : V) : V := cneg (all x (cneg a))
noncomputable def ciff (a b : V) : V := cand (imp a b) (imp b a)
noncomputable def ctop : V := cneg 1

lemma cneg_eq (a : V) : cneg a = (codes : CKernel.Generic.Codes V).neg a := rfl
lemma cand_eq (a b : V) : cand a b = (codes : CKernel.Generic.Codes V).and a b := rfl
lemma cor_eq (a b : V) : cor a b = (codes : CKernel.Generic.Codes V).or a b := rfl
lemma cex_eq (x a : V) : cex x a = (codes : CKernel.Generic.Codes V).ex x a := rfl
lemma ciff_eq (a b : V) : ciff a b = (codes : CKernel.Generic.Codes V).iff a b := rfl

end

def negDef : 𝚺ᴬ₁.Semisentence 2 := .mkSigma “y a. !impDef y a 1”
def andDef : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “y a b. ∃ nb, !impDef nb b 1 ∧ ∃ i, !impDef i a nb ∧ !impDef y i 1”
def orDef : 𝚺ᴬ₁.Semisentence 3 := .mkSigma “y a b. ∃ na, !impDef na a 1 ∧ !impDef y na b”
def exDef : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “y x a. ∃ na, !impDef na a 1 ∧ ∃ u, !allDef u x na ∧ !impDef y u 1”
def iffDef : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “y a b. ∃ i, !impDef i a b ∧ ∃ j, !impDef j b a ∧ !andDef y i j”

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance cneg_defined : 𝚺ᴬ₁-Function₁ (cneg : V → V) via negDef := .mk fun v => by
  simp [negDef, cneg]

instance cand_defined : 𝚺ᴬ₁-Function₂ (cand : V → V → V) via andDef := .mk fun v => by
  simp [andDef, cand, cneg]

instance cor_defined : 𝚺ᴬ₁-Function₂ (cor : V → V → V) via orDef := .mk fun v => by
  simp [orDef, cor, cneg]

instance cex_defined : 𝚺ᴬ₁-Function₂ (cex : V → V → V) via exDef := .mk fun v => by
  simp [exDef, cex, cneg]

instance ciff_defined : 𝚺ᴬ₁-Function₂ (ciff : V → V → V) via iffDef := .mk fun v => by
  simp [iffDef, ciff, cand, cneg]

end

/-! ## Unary numerals -/

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance imp_definable (Γ m) : Γᴬ_[m + 1]-Function₂ (imp : V → V → V) :=
  .of_sigmaOne (.of_zero imp_defined.to_definable)
instance all_definable (Γ m) : Γᴬ_[m + 1]-Function₂ (all : V → V → V) :=
  .of_sigmaOne (.of_zero all_defined.to_definable)
instance eqc_definable (Γ m) : Γᴬ_[m + 1]-Function₂ (eqc : V → V → V) :=
  .of_sigmaOne (.of_zero eqc_defined.to_definable)
instance mem_definable (Γ m) : Γᴬ_[m + 1]-Function₂ (mem : V → V → V) :=
  .of_sigmaOne (.of_zero mem_defined.to_definable)
instance cneg_definable (Γ m) : Γᴬ_[m + 1]-Function₁ (cneg : V → V) :=
  .of_sigmaOne cneg_defined.to_definable
instance cand_definable (Γ m) : Γᴬ_[m + 1]-Function₂ (cand : V → V → V) :=
  .of_sigmaOne cand_defined.to_definable
instance cex_definable (Γ m) : Γᴬ_[m + 1]-Function₂ (cex : V → V → V) :=
  .of_sigmaOne cex_defined.to_definable
instance ciff_definable (Γ m) : Γᴬ_[m + 1]-Function₂ (ciff : V → V → V) :=
  .of_sigmaOne ciff_defined.to_definable
instance cor_definable (Γ m) : Γᴬ_[m + 1]-Function₂ (cor : V → V → V) :=
  .of_sigmaOne cor_defined.to_definable

/-- The predicate defined by a Σ1 formula. -/
instance evalb_definable (D : 𝚺ᴬ₁.Semisentence 1) :
    𝚺ᴬ₁-Predicate (fun y : V => D.val.Evalb ![y]) := by
  have : 𝚺ᴬ₁-Predicate (fun y : V => D.val.Evalb ![y]) via D := .mk fun v => by
    have : v = ![v 0] := by funext i; match i with | 0 => rfl
    rw [this]; simp
  exact this.to_definable

end

end ZF207.Internal
