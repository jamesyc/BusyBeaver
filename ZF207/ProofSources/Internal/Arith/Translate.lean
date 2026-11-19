module
public import Internal.Arith.Syntax
@[expose] public section
/-! # The formula translation `J`

`J ι ε n p` translates an internal ℒₒᵣ formula with `n` bound variables in scope at
the marker `ε`. Under each binder `n` grows by one and `ε` is shifted. -/
namespace ZF207.Internal.Arith
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

/-- The graph function `(n, t) ↦ G n t`. -/
noncomputable def GDef (ι : Interp) : 𝚺ᴬ₁.Semisentence 4 :=
  ((Graph.blueprint ι).result ℒₒᵣ).rew (Rew.subst ![#0, #3, #2, #1])

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (ι : Interp)

/-- The relation template for an ℒₒᵣ relation index. -/
noncomputable def relT (R : V) : V := if R = eqIndex then (tq ι.eq : V) else (tq ι.lt : V)

/-- An atom: `∃∃ (G t₀ [#1] ∧ G t₁ [#0] ∧ R(e, #1, #0))`. -/
noncomputable def atomJ (ε n R t₀ t₁ : V) : V :=
  ^∃ ^∃ ((subst ℒₛₑₜ (^#1 ∷ bv2 n) (G ι ε n t₀) ^⋏ subst ℒₛₑₜ (^#0 ∷ bv2 n) (G ι ε n t₁)) ^⋏
    subst ℒₛₑₜ (bs (bs ε) ∷ ^#1 ∷ ^#0 ∷ 0) (relT ι R))

instance G_defined : 𝚺ᴬ₁-Function₃ (fun ε n t : V => G ι ε n t) via GDef ι := .mk fun v => by
  have h := (Graph.construction ι (V := V)).result_defined (L := ℒₒᵣ) |>.iff
    (v := ![v 0, v 3, v 2, v 1])
  have e : (fun i : Fin 2 => (![v 0, v 3, v 2, v 1] : Fin 4 → V) i.succ.succ) = ![v 2, v 1] := by
    funext i; match i with | 0 => rfl | 1 => rfl
  simp only [GDef, Bounding.HierarchySymbol.Semiformula.val_rew, Semiformula.eval_rew,
    Function.comp_def]
  simpa [G, e, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using h

instance G_definable : 𝚺ᴬ₁-Function₃ (G ι : V → V → V → V) := (G_defined ι).to_definable
instance G_definable' (Γ m) : Γᴬ_[m + 1]-Function₃ (G ι : V → V → V → V) :=
  (G_definable ι).of_sigmaOne

end

noncomputable def atomJDef (ι : Interp) : 𝚺ᴬ₁.Semisentence 6 := .mkSigma
  “y e n R t₀ t₁. ∃ g₀, !(GDef ι) g₀ e n t₀ ∧
    ∃ g₁, !(GDef ι) g₁ e n t₁ ∧
    ∃ v, !bv2Def v n ∧ ∃ b₁, !qqBvarDef b₁ 1 ∧ ∃ b₀, !qqBvarDef b₀ 0 ∧
    ∃ l, !adjoinDef l b₁ v ∧ ∃ r, !adjoinDef r b₀ v ∧
    ∃ s₀, !(substsGraph ℒₛₑₜ) s₀ l g₀ ∧ ∃ s₁, !(substsGraph ℒₛₑₜ) s₁ r g₁ ∧
    ∃ rt, ((R = ↑eqIndex ∧ rt = ↑(tq ι.eq)) ∨ (R ≠ ↑eqIndex ∧ rt = ↑(tq ι.lt))) ∧
    ∃ e₁, !bsDef e₁ e ∧ ∃ e₂, !bsDef e₂ e₁ ∧
    ∃ w₂, !adjoinDef w₂ b₀ 0 ∧ ∃ w₁, !adjoinDef w₁ b₁ w₂ ∧ ∃ w, !adjoinDef w e₂ w₁ ∧
    ∃ o, !(substsGraph ℒₛₑₜ) o w rt ∧
    ∃ c₁, !qqAndDef c₁ s₀ s₁ ∧ ∃ c₂, !qqAndDef c₂ c₁ o ∧ ∃ x, !qqExsDef x c₂ ∧ !qqExsDef y x”

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (ι : Interp)

lemma atomJ_defined : 𝚺ᴬ₁-Function₅ (atomJ ι : V → V → V → V → V → V) via atomJDef ι :=
  .mk fun v => by
    by_cases h : v 3 = eqIndex <;>
      simp [atomJDef, atomJ, relT, h, (G_defined (V := V) ι).iff, bv2_defined.iff,
        subst.defined.iff, bs_defined.iff, numeral_eq_natCast]

end

namespace JRec

noncomputable def blueprint (ι : Interp) : UformulaRec1.Blueprint where
  rel := .mkSigma “y q k R v. ∃ n, !pi₁Def n q ∧ ∃ e, !pi₂Def e q ∧
    ∃ t₀, !nthDef t₀ v 0 ∧ ∃ t₁, !nthDef t₁ v 1 ∧ !(atomJDef ι) y e n R t₀ t₁”
  nrel := .mkSigma “y q k R v. ∃ n, !pi₁Def n q ∧ ∃ e, !pi₂Def e q ∧
    ∃ t₀, !nthDef t₀ v 0 ∧ ∃ t₁, !nthDef t₁ v 1 ∧
    ∃ a, !(atomJDef ι) a e n R t₀ t₁ ∧ !(negGraph ℒₛₑₜ) y a”
  verum := .mkSigma “y q. !qqVerumDef y”
  falsum := .mkSigma “y q. !qqFalsumDef y”
  and := .mkSigma “y q p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂”
  or := .mkSigma “y q p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂”
  all := .mkSigma “y q p₁ ys. ∃ r, !nthDef r ys 0 ∧ ∃ e, !pi₂Def e q ∧ ∃ e₁, !bsDef e₁ e ∧
    ∃ b₀, !qqBvarDef b₀ 0 ∧ ∃ dm, !(unDef (tq ι.dom)) dm e₁ b₀ ∧ ∃ d, !(negGraph ℒₛₑₜ) d dm ∧
    ∃ c, !qqOrDef c d r ∧ !qqAllDef y c”
  exs := .mkSigma “y q p₁ ys. ∃ r, !nthDef r ys 0 ∧ ∃ e, !pi₂Def e q ∧ ∃ e₁, !bsDef e₁ e ∧
    ∃ b₀, !qqBvarDef b₀ 0 ∧ ∃ dm, !(unDef (tq ι.dom)) dm e₁ b₀ ∧ ∃ c, !qqAndDef c dm r ∧
    !qqExsDef y c”
  allChanges := .mkSigma “q' q i. ∃ n, !pi₁Def n q ∧ ∃ e, !pi₂Def e q ∧ ∃ e₁, !bsDef e₁ e ∧
    !pairDef q' (n + 1) e₁”
  exsChanges := .mkSigma “q' q i. ∃ n, !pi₁Def n q ∧ ∃ e, !pi₂Def e q ∧ ∃ e₁, !bsDef e₁ e ∧
    !pairDef q' (n + 1) e₁”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (ι : Interp)

noncomputable def construction : UformulaRec1.Construction V (blueprint ι) where
  rel q _ R v := atomJ ι (π₂ q) (π₁ q) R v.[0] v.[1]
  nrel q _ R v := neg ℒₛₑₜ (atomJ ι (π₂ q) (π₁ q) R v.[0] v.[1])
  verum _ := ^⊤
  falsum _ := ^⊥
  and _ _ _ y₁ y₂ := y₁ ^⋏ y₂
  or _ _ _ y₁ y₂ := y₁ ^⋎ y₂
  all q _ ys := ^∀ (neg ℒₛₑₜ (un (tq ι.dom) (bs (π₂ q)) ^#0) ^⋎ ys.[0])
  exs q _ ys := ^∃ (un (tq ι.dom) (bs (π₂ q)) ^#0 ^⋏ ys.[0])
  allChanges q _ := ⟪π₁ q + 1, bs (π₂ q)⟫
  exsChanges q _ := ⟪π₁ q + 1, bs (π₂ q)⟫
  rel_defined := .mk fun v => by simp [blueprint, (atomJ_defined (V := V) ι).iff]
  nrel_defined := .mk fun v => by
    simp [blueprint, (atomJ_defined (V := V) ι).iff, neg.defined.iff]
  verum_defined := .mk fun v => by simp [blueprint]
  falsum_defined := .mk fun v => by simp [blueprint]
  and_defined := .mk fun v => by simp [blueprint]
  or_defined := .mk fun v => by simp [blueprint]
  all_defined := .mk fun v => by
    simp [blueprint, neg.defined.iff, (un_defined (V := V) _).iff, bs_defined.iff,
      numeral_eq_natCast]
  exs_defined := .mk fun v => by
    simp [blueprint, (un_defined (V := V) _).iff, bs_defined.iff, numeral_eq_natCast]
  allChanges_defined := .mk fun v => by simp [blueprint, bs_defined.iff]
  exChanges_defined := .mk fun v => by simp [blueprint, bs_defined.iff]

end JRec

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (ι : Interp)

/-- The translation of a formula with `n` bound variables in scope, at marker `ε`. -/
noncomputable def J (ε n p : V) : V := (JRec.construction ι).result ℒₒᵣ ⟪n, ε⟫ p

noncomputable def JDef (ι : Interp) : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y e n p. ∃ q, !pairDef q n e ∧ !((JRec.blueprint ι).result ℒₒᵣ) y q p”

instance J_defined : 𝚺ᴬ₁-Function₃ (J ι : V → V → V → V) via JDef ι := .mk fun v => by
  simp [JDef, J, (JRec.construction ι).result_defined (L := ℒₒᵣ) |>.iff]

instance J_definable : 𝚺ᴬ₁-Function₃ (J ι : V → V → V → V) := (J_defined ι).to_definable

instance J_definable' (Γ m) : Γᴬ_[m + 1]-Function₃ (J ι : V → V → V → V) :=
  (J_definable ι).of_sigmaOne

variable {ι}

@[simp] lemma J_rel {ε n k R v : V} (hR : (ℒₒᵣ).IsRel k R) (hv : IsUTermVec ℒₒᵣ k v) :
    J ι ε n (^rel k R v) = atomJ ι ε n R v.[0] v.[1] := by
  simp [J, hR, hv, JRec.construction]

@[simp] lemma J_nrel {ε n k R v : V} (hR : (ℒₒᵣ).IsRel k R) (hv : IsUTermVec ℒₒᵣ k v) :
    J ι ε n (^nrel k R v) = neg ℒₛₑₜ (atomJ ι ε n R v.[0] v.[1]) := by
  simp [J, hR, hv, JRec.construction]

@[simp] lemma J_verum (ε n : V) : J ι ε n ^⊤ = ^⊤ := by simp [J, JRec.construction]
@[simp] lemma J_falsum (ε n : V) : J ι ε n ^⊥ = ^⊥ := by simp [J, JRec.construction]

@[simp] lemma J_and {ε n p q : V} (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    J ι ε n (p ^⋏ q) = J ι ε n p ^⋏ J ι ε n q := by simp [J, hp, hq, JRec.construction]

@[simp] lemma J_or {ε n p q : V} (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    J ι ε n (p ^⋎ q) = J ι ε n p ^⋎ J ι ε n q := by simp [J, hp, hq, JRec.construction]

@[simp] lemma J_all {ε n p : V} (hp : IsUFormula ℒₒᵣ p) :
    J ι ε n (^∀ p) = ^∀ (neg ℒₛₑₜ (un (tq ι.dom) (bs ε) ^#0) ^⋎ J ι (bs ε) (n + 1) p) := by
  simp [J, hp, JRec.construction]

@[simp] lemma J_exs {ε n p : V} (hp : IsUFormula ℒₒᵣ p) :
    J ι ε n (^∃ p) = ^∃ (un (tq ι.dom) (bs ε) ^#0 ^⋏ J ι (bs ε) (n + 1) p) := by
  simp [J, hp, JRec.construction]

end

end ZF207.Internal.Arith
