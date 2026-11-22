module
public import ZF192Support.Coding.Histories.TraceFormula
public import ZF192Support.Coding.Histories.TraceEquations
public import ZF192Support.Coding.Lists.MemberDefinability
public import ZF192Support.Calculus.Internal.Model
@[expose] public section
/-! # The machine's calculus in arithmetic models

The machine's axiom templates and proof rules have Σ₁ definitions over the
same code constructors used by the compiler. The provability predicate `D`
says that a trace of these rules contains the requested code. -/
namespace ZF192Support.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ZFR.ArithmeticRepresentation
open ZF192Support.Internal (imp mem eqc all codes cantor impDef memDef eqcDef allDef negDef exDef
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
def rho8Def : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “y d a h u. ∃ p, !impDef p h u ∧ ∃ q, !impDef q p d ∧ ∃ r, !impDef r d h ∧
    ∃ s, !impDef s a h ∧ ∃ t, !impDef t r s ∧ !impDef y q t”

def cAxiomDef : 𝚺ᴬ₁.Semisentence 1 := .mkSigma
  “n. ∃ a, ∃ d, ∃ h, ∃ u, n = 0 ∨ !head6Def n d a h ∨ !head5Def n d h ∨
    !head4Def n h d a ∨ !head3Def n h d a ∨ !head2Def n d a h ∨ !head1Def n d h ∨
    (u ≤ d ∧ !rho8Def n d a h u) ∨ (a ≠ d ∧ a ≠ h ∧ !bundleDef n h d a)”
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

lemma rho8Def_iff (y d a h u : M) :
    rho8Def.val.Evalb ![y, d, a, h, u] ↔ y = (codes (V := M)).rho8 d a h u := by
  simp [rho8Def, CKernel.Generic.Codes.rho8, codes]

lemma cAxiomDef_defined : 𝚺ᴬ₁.DefinedPred (cAxiom (M := M)) cAxiomDef := .mk (by
  intro v
  simp [cAxiomDef, cAxiom, head1Def_iff, head2Def_iff, head3Def_iff, head4Def_iff,
    head5Def_iff, head6Def_iff, bundleDef_iff]
  simp [Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton, rho8Def_iff])


lemma cRuleDef_defined : 𝚺ᴬ₁.DefinedRel (cRule (M := M)) cRuleDef := .mk (by
  intro v
  simp [cRuleDef, cRule, Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons',
    cAxiomDef_defined.iff, memberFormula_defined.iff])

lemma cTrace_defined : 𝚺ᴬ₁.DefinedPred (modelTrace (cRule (M := M))) (traceFormula cRuleDef) :=
  traceFormula_defined cRuleDef cRule cRuleDef_defined

end

section
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma D_iff (x : M) : D.val.Evalb ![x] ↔ ∃ p, modelTrace cRule p ∧ modelMember x p := by
  simp [D, Semiformula.eval_rew, Function.comp_def, Matrix.comp_vecCons', cTrace_defined.iff,
    memberFormula_defined.iff]

end

/-- `C` proves `x` (in `ℕ`). -/
def CProv (x : ℕ) : Prop := D.val.Evalb ![x]

end ZF192Support.Halting
