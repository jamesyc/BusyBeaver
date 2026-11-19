module
public import Internal.Tait.Equations
public import CKernel.Logic
@[expose] public section
/-! # The calculus inside a model, and induction on formulas in models of PA

`IntLogic V` is a portable calculus (`CKernel.Generic.EqLogic`) on the codes of
`V` whose provability predicate is defined by a Σ1 formula. The lemmas about
translations are internal inductions whose hypotheses quantify over parameters,
so they are Π2; models of PA have the induction they need. -/
namespace ZF207.Internal.Tait
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open CKernel.Generic

/-- A calculus on the codes of `V` with Σ1 provability. -/
structure IntLogic (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] where
  D : 𝚺ᴬ₁.Semisentence 1
  S : EqLogic V
  codes_eq : S.toCodes = codes
  prov_iff (x : V) : S.Prov x ↔ D.val.Evalb ![x]
  E_eq (a b : V) : S.E a b = ceqv a b
  ok_iff (x : V) : S.ok x ↔ x ≠ rlab 0

namespace IntLogic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (L : IntLogic V)

/-- Provability. -/
def Pr (x : V) : Prop := L.D.val.Evalb ![x]

instance pr_definable : 𝚺ᴬ₁-Predicate L.Pr := evalb_definable L.D

lemma pr_iff (x : V) : L.Pr x ↔ L.S.Prov x := (L.prov_iff x).symm

@[simp] lemma s_imp (a b : V) : L.S.imp a b = imp a b := by
  rw [show L.S.imp = L.S.toCodes.imp from rfl, L.codes_eq]; rfl
@[simp] lemma s_mem (a b : V) : L.S.mem a b = mem a b := by
  rw [show L.S.mem = L.S.toCodes.mem from rfl, L.codes_eq]; rfl
@[simp] lemma s_eq (a b : V) : L.S.eq a b = eqc a b := by
  rw [show L.S.eq = L.S.toCodes.eq from rfl, L.codes_eq]; rfl
@[simp] lemma s_all (x a : V) : L.S.all x a = all x a := by
  rw [show L.S.all = L.S.toCodes.all from rfl, L.codes_eq]; rfl
@[simp] lemma s_bot : L.S.bot = (1 : V) := by
  rw [show L.S.bot = L.S.toCodes.bot from rfl, L.codes_eq]; rfl
@[simp] lemma s_neg (a : V) : L.S.neg a = cneg a := by simp [Codes.neg, cneg]
@[simp] lemma s_and (a b : V) : L.S.and a b = cand a b := by simp [Codes.and, cand, cneg]
@[simp] lemma s_or (a b : V) : L.S.or a b = cor a b := by simp [Codes.or, cor, cneg]
@[simp] lemma s_ex (x a : V) : L.S.ex x a = cex x a := by simp [Codes.ex, cex, cneg]
@[simp] lemma s_E (a b : V) : L.S.E a b = ceqv a b := L.E_eq a b
@[simp] lemma s_iff (a b : V) : L.S.iff a b = ciff a b := by
  simp [Codes.iff, ciff, Codes.and, cand, cneg]

end IntLogic

/-! ## Induction on formulas in models of PA -/

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {L : Language} [L.Encodable] [L.LORDefinable]

theorem uformula_induction (Γ : SigmaPiDelta) (s : ℕ) {P : V → Prop} (hP : Γᴬ_[s + 1]-Predicate P)
    (hrel : ∀ k r v, L.IsRel k r → IsUTermVec L k v → P (^rel k r v))
    (hnrel : ∀ k r v, L.IsRel k r → IsUTermVec L k v → P (^nrel k r v))
    (hverum : P ^⊤) (hfalsum : P ^⊥)
    (hand : ∀ p q, IsUFormula L p → IsUFormula L q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsUFormula L p → IsUFormula L q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, IsUFormula L p → P p → P (^∀ p))
    (hexs : ∀ p, IsUFormula L p → P p → P (^∃ p)) :
    ∀ p, IsUFormula L p → P p := by
  have hQ : Γᴬ_[s + 1].DefinablePred (fun p : V => IsUFormula L p → P p) :=
    .imp (IsUFormula.definable' (L := L) Γ.alt s) hP
  refine InductionOnHierarchy.order_induction_sigma Γ (s + 1) hQ ?_
  intro p ih hp
  rcases hp.case with ⟨k, r, v, hr, hv, rfl⟩ | ⟨k, r, v, hr, hv, rfl⟩ | rfl | rfl |
    ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩
  · exact hrel k r v hr hv
  · exact hnrel k r v hr hv
  · exact hverum
  · exact hfalsum
  · exact hand p₁ p₂ h₁ h₂ (ih p₁ (by simp) h₁) (ih p₂ (by simp) h₂)
  · exact hor p₁ p₂ h₁ h₂ (ih p₁ (by simp) h₁) (ih p₂ (by simp) h₂)
  · exact hall p₁ h₁ (ih p₁ (by simp) h₁)
  · exact hexs p₁ h₁ (ih p₁ (by simp) h₁)

end

end ZF207.Internal.Tait
