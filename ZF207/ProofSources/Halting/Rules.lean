module
public import LiteralCRuleModelAlignment
public import ExactTraceFormula
public import ExactTraceModelEquations
public import ExactMemberDefinability
public import ConcreteModelListAppend
public import Internal.Model
@[expose] public section
/-! # The halting chain's trace rule over the machine's codes

The halting chain starts from an internal trace of `modelCRule`, whose code functions
`t299`, `t300`, `t302`, `t322` are `4 · cantor` with tags `0, 1, 3, 2`, i.e. the machine's
`imp`, `mem`, `eqc`, `all`; its axiom templates `t323 … t330` are the heads, `ρ8` and the
gate bundle. So `modelCRule` is the rule `cRule` over `Internal.codes`, which has a Σ1
definition, and "some trace contains `x`" is a Σ1 predicate `D` closed under the machine's
rules (`ProvRules D`). -/
namespace ZF207.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ZF207.MM0ModelReplay ZFR.ArithmeticRepresentation
open ZF207.Internal (imp mem eqc all codes cantor impDef memDef eqcDef allDef negDef exDef
  cneg cex)

/-! ## The rule over the machine's codes -/

section
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The axiom templates over the machine's codes. -/
def cAxiom (n : M) : Prop := ∃ a d h u : M,
  n = 0 ∨ n = (codes (V := M)).head6 d a h ∨ n = (codes (V := M)).head5 d h ∨ n = (codes (V := M)).head4 h d a ∨
  n = (codes (V := M)).head3 h d a ∨ n = (codes (V := M)).head2 d a h ∨ n = (codes (V := M)).head1 d h ∨
  (u ≤ d ∧ n = (codes (V := M)).rho8 d a h u) ∨ (a ≠ d ∧ a ≠ h ∧ n = (codes (V := M)).bundle h d a)

/-- One trace step: an axiom, modus ponens, or generalization from earlier entries. -/
def cRule (r xs : M) : Prop :=
  cAxiom r ∨ (∃ b, modelMember b xs ∧ modelMember (imp b r) xs) ∨
  (∃ i b, modelMember b xs ∧ r = all i b)

end

/-! ## The code functions -/

section
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma modelCantor_eq (a b : M) : modelCantor a b = cantor a b :=
  (modelCantor_unique a b _ (ZF207.Internal.two_mul_cantor a b)).symm

lemma t30_eq : t30 (M := M) = 1 := by simp [t30, t29, t28]
lemma t31_eq : t31 (M := M) = 2 := by simp [t31, t30, t29, t28]; norm_num
lemma t32_eq : t32 (M := M) = 3 := by simp [t32, t31, t30, t29, t28]; norm_num
lemma t33_eq : t33 (M := M) = 4 := by simp [t33, t32, t31, t30, t29, t28]; norm_num

lemma t299_eq (a b : M) : t299 a b = imp a b := by
  simp only [t299, literalPair_modelCantor, modelCantor_eq, t33_eq, imp, t45]

lemma t300_eq (a b : M) : t300 a b = mem a b := by
  simp only [t300, literalPair_modelCantor, modelCantor_eq, t33_eq, t30_eq, mem, t45, t44]

lemma t302_eq (a b : M) : t302 a b = eqc a b := by
  simp only [t302, literalPair_modelCantor, modelCantor_eq, t33_eq, t32_eq, eqc, t45, t44]

lemma t322_eq (x a : M) : t322 x a = all x a := by
  simp only [t322, literalPair_modelCantor, modelCantor_eq, t33_eq, t31_eq, all, t45, t44]


lemma t323_eq (a d h : M) : t323 a d h = (codes (V := M)).head6 d a h := by
  simp only [t323, t299_eq, t322_eq]; rfl
lemma t324_eq (a d h : M) : t324 a d h = (codes (V := M)).head5 d h := by
  simp only [t324, t299_eq, t322_eq, t302_eq, t30_eq]; rfl
lemma t325_eq (a d h : M) : t325 a d h = (codes (V := M)).head4 h d a := by
  simp only [t325, t299_eq, t300_eq, t302_eq]; rfl
lemma t326_eq (a d h : M) : t326 a d h = (codes (V := M)).head3 h d a := by
  simp only [t326, t299_eq, t300_eq, t302_eq]; rfl
lemma t327_eq (a d h : M) : t327 a d h = (codes (V := M)).head2 d a h := by
  simp only [t327, t299_eq, t322_eq]; rfl
lemma t328_eq (a d h : M) : t328 a d h = (codes (V := M)).head1 d h := by
  simp only [t328, t299_eq, t322_eq, t30_eq]; rfl
lemma t329_eq (a d h u : M) : t329 a d h u = (codes (V := M)).rho8 d a h u := by
  simp only [t329, t299_eq]; rfl
lemma t330_eq (a d h : M) : t330 a d h = (codes (V := M)).bundle h d a := by
  simp only [t330, t299_eq, t300_eq, t302_eq, t322_eq, t30_eq]; rfl

lemma modelCRule_eq : (modelCRule : M → M → Prop) = cRule := by
  funext r xs
  simp only [modelCRule, modelCAxiom, cRule, cAxiom, t299_eq, t322_eq, t323_eq, t324_eq, t325_eq,
    t326_eq, t327_eq, t328_eq, t329_eq, t330_eq]

end

/-! ## Σ1 definitions -/

def head1Def : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “y d h. ∃ u, !allDef u d h ∧ ∃ e, !exDef e d u ∧ !impDef y e h”
def head2Def : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y d a h. ∃ u, !allDef u a h ∧ ∃ v, !allDef v d u ∧ ∃ w, !allDef w d h ∧
    ∃ z, !allDef z a w ∧ !impDef y v z”
def head3Def : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y h d a. ∃ p, !memDef p h d ∧ ∃ q, !eqcDef q h a ∧ ∃ r, !memDef r a d ∧
    ∃ s, !impDef s q r ∧ !impDef y p s”
def head4Def : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y h d a. ∃ p, !eqcDef p h d ∧ ∃ q, !memDef q a h ∧ ∃ r, !memDef r a d ∧
    ∃ s, !impDef s q r ∧ !impDef y p s”
def head5Def : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “y d h. ∃ q, !eqcDef q h d ∧ !exDef y d q”
def head6Def : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y d a h. ∃ p, !allDef p d a ∧ ∃ i, !impDef i a h ∧ ∃ q, !allDef q d i ∧
    ∃ r, !allDef r d h ∧ ∃ s, !impDef s q r ∧ !impDef y p s”
def gateBodyDef : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y a d h. ∃ m1, !memDef m1 h a ∧ ∃ n1, !impDef n1 m1 1 ∧ ∃ i1, !impDef i1 a n1 ∧
    ∃ u, !allDef u h i1 ∧ ∃ nu, !impDef nu u 1 ∧ ∃ i2, !impDef i2 a nu ∧
    ∃ v, !allDef v h i2 ∧ ∃ m2, !memDef m2 a d ∧ ∃ m3, !memDef m3 a h ∧
    ∃ i3, !impDef i3 m2 m3 ∧ ∃ w, !allDef w a i3 ∧ ∃ i4, !impDef i4 w v ∧
    ∃ z, !allDef z d i4 ∧ ∃ nz, !impDef nz z 1 ∧ ∃ i5, !impDef i5 a nz ∧
    ∃ x, !allDef x d i5 ∧ ∃ nx, !impDef nx x 1 ∧ ∃ i6, !impDef i6 m1 nx ∧
    ∃ g, !allDef g h i6 ∧ ∃ i7, !impDef i7 a m1 ∧ ∃ n7, !impDef n7 i7 1 ∧ !impDef y g n7”
def bundleDef : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y a b c. ∃ e, !eqcDef e a b ∧ ∃ ae, !allDef ae c e ∧ ∃ ve, !impDef ve e ae ∧
    ∃ m, !memDef m a b ∧ ∃ am, !allDef am c m ∧ ∃ vm, !impDef vm m am ∧
    ∃ gb, !gateBodyDef gb c b a ∧ ∃ q, !allDef q c gb ∧ ∃ j, !impDef j vm q ∧
    ∃ k, !impDef k ve j ∧ !impDef y k 1”
def cAxiomDef : 𝚺ᴬ₁.Semisentence 1 := .mkSigma
  “n. ∃ a, ∃ d, ∃ h, ∃ u, n = 0 ∨ !head6Def n d a h ∨ !head5Def n d h ∨
    !head4Def n h d a ∨ !head3Def n h d a ∨ !head2Def n d a h ∨ !head1Def n d h ∨
    (u ≤ d ∧ ∃ p, !impDef p h u ∧ ∃ q, !impDef q p d ∧ ∃ r, !impDef r d h ∧
      ∃ s, !impDef s a h ∧ ∃ t, !impDef t r s ∧ !impDef n q t) ∨ (a ≠ d ∧ a ≠ h ∧ !bundleDef n h d a)”
def cRuleDef : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “r xs. !cAxiomDef r ∨ (∃ b, !memberFormula b xs ∧ ∃ c, !impDef c b r ∧ !memberFormula c xs) ∨
    (∃ i, ∃ b, !memberFormula b xs ∧ !allDef r i b)”
/-- Some `cRule`-trace contains `x`. -/
def D : 𝚺ᴬ₁.Semisentence 1 := .mkSigma
  “x. ∃ p, !(traceFormula cRuleDef) p ∧ !memberFormula x p”

section
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


lemma head1Def_iff (y d h : M) : head1Def.val.Evalb ![y, d, h] ↔ y = (codes (V := M)).head1 d h := by
  simp [head1Def, CKernel.Generic.Codes.head1, CKernel.Generic.Codes.ex,
    CKernel.Generic.Codes.neg, codes, cex, cneg]
lemma head2Def_iff (y d a h : M) : head2Def.val.Evalb ![y, d, a, h] ↔ y = (codes (V := M)).head2 d a h := by
  simp [head2Def, CKernel.Generic.Codes.head2, codes]
lemma head3Def_iff (y h d a : M) : head3Def.val.Evalb ![y, h, d, a] ↔ y = (codes (V := M)).head3 h d a := by
  simp [head3Def, CKernel.Generic.Codes.head3, codes]
lemma head4Def_iff (y h d a : M) : head4Def.val.Evalb ![y, h, d, a] ↔ y = (codes (V := M)).head4 h d a := by
  simp [head4Def, CKernel.Generic.Codes.head4, codes]
lemma head5Def_iff (y d h : M) : head5Def.val.Evalb ![y, d, h] ↔ y = (codes (V := M)).head5 d h := by
  simp [head5Def, CKernel.Generic.Codes.head5, CKernel.Generic.Codes.ex,
    CKernel.Generic.Codes.neg, codes, cex, cneg]
lemma head6Def_iff (y d a h : M) : head6Def.val.Evalb ![y, d, a, h] ↔ y = (codes (V := M)).head6 d a h := by
  simp [head6Def, CKernel.Generic.Codes.head6, codes]
lemma gateBodyDef_iff (y a d h : M) :
    gateBodyDef.val.Evalb ![y, a, d, h] ↔ y = (codes (V := M)).gateBody a d h := by
  simp [gateBodyDef, CKernel.Generic.Codes.gateBody, codes]
lemma bundleDef_iff (y a b c : M) : bundleDef.val.Evalb ![y, a, b, c] ↔ y = (codes (V := M)).bundle a b c := by
  simp [bundleDef, gateBodyDef_iff, CKernel.Generic.Codes.bundle, CKernel.Generic.Codes.neg,
    CKernel.Generic.Codes.eqVac, CKernel.Generic.Codes.memVac, CKernel.Generic.Codes.qGate, codes]

lemma cAxiomDef_defined : 𝚺ᴬ₁.DefinedPred (cAxiom (M := M)) cAxiomDef := .mk (by
  intro v
  simp [cAxiomDef, cAxiom, head1Def_iff, head2Def_iff, head3Def_iff, head4Def_iff, head5Def_iff,
    head6Def_iff, bundleDef_iff, CKernel.Generic.Codes.rho8, codes])

lemma cRuleDef_defined : 𝚺ᴬ₁.DefinedRel (cRule (M := M)) cRuleDef := .mk (by
  intro v
  simp [cRuleDef, cRule, Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons',
    cAxiomDef_defined.iff, memberFormula_defined.iff])

lemma cTrace_defined : 𝚺ᴬ₁.DefinedPred (modelTrace (cRule (M := M))) (traceFormula cRuleDef) :=
  traceFormula_defined cRuleDef cRule cRuleDef_defined

end

section
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma D_iff (x : M) : D.val.Evalb ![x] ↔ ∃ p, modelTrace modelCRule p ∧ modelMember x p := by
  rw [modelCRule_eq]
  simp [D, Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons', cTrace_defined.iff,
    memberFormula_defined.iff]

end

end ZF207.Halting
