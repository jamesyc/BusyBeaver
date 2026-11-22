module
public import ZF192Support.Calculus.Internal.SetLanguage
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Functions
public import Foundation.FirstOrder.Arithmetic.HFS.PRF
@[expose] public section
/-! # Interpreting arithmetic formulas in set theory, internally

An `Interp` gives set-theoretic templates for the domain of numbers, equality,
order, zero, one, addition and multiplication (fixed `ℒₛₑₜ` semisentences), each
with a first argument `e` (a marker selecting one model), and a marker template.
Inside a model of arithmetic, `J ε n p` translates an internal ℒₒᵣ semiformula
with `n` bound variables into an `ℒₛₑₜ` semiformula with the same bound
variables:
* a term `t` becomes its graph `G n t`, an `ℒₛₑₜ` semiformula whose `#0` is the
  value and whose `#(j+1)` is the term's `#j`; compound terms quantify the values
  of their two arguments;
* an atom `R(t₀, t₁)` is `∃∃ (G t₀ ∧ G t₁ ∧ R(#1, #0))` with the graphs re-indexed;
* quantifiers are relativized to the domain template.
The marker `ε` is an `ℒₛₑₜ` term; it is shifted past every new bound variable.
Template codes are fixed numerals; re-indexing uses `subst` with vectors of
consecutive bound variables. -/
namespace ZF192Support.Internal.Arith
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

/-- Set-theoretic templates for arithmetic. -/
structure Interp where
  mark : Semisentence ℒₛₑₜ 1
  dom : Semisentence ℒₛₑₜ 2
  eq : Semisentence ℒₛₑₜ 3
  lt : Semisentence ℒₛₑₜ 3
  zero : Semisentence ℒₛₑₜ 2
  one : Semisentence ℒₛₑₜ 2
  add : Semisentence ℒₛₑₜ 4
  mul : Semisentence ℒₛₑₜ 4

/-- The code of a template. -/
noncomputable def tq {k : ℕ} (φ : Semisentence ℒₛₑₜ k) : ℕ := Encodable.encode φ

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma tq_eq {k : ℕ} (φ : Semisentence ℒₛₑₜ k) : ((tq φ : ℕ) : V) = ⌜φ⌝ :=
  (Sentence.quote_eq_encode φ).symm

end

/-! ## Consecutive bound variables -/

namespace Idv

noncomputable def blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. y = 0”
  succ := .mkSigma “y v n. !(qVecGraph ℒₛₑₜ) y v”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def construction : PR.Construction V blueprint where
  zero _ := 0
  succ _ _ v := qVec ℒₛₑₜ v
  zero_defined := .mk fun v => by simp [blueprint]
  succ_defined := .mk fun v => by simp [blueprint, qVec.defined.iff]

end Idv

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `idv n = [#0, …, #(n-1)]`. -/
noncomputable def idv (n : V) : V := Idv.construction.result ![] n

@[simp] lemma idv_zero : idv (0 : V) = 0 := by simp [idv, Idv.construction]
@[simp] lemma idv_succ (n : V) : idv (n + 1) = qVec ℒₛₑₜ (idv n) := by
  simp [idv, Idv.construction]

noncomputable def idvDef : 𝚺ᴬ₁.Semisentence 2 := Idv.blueprint.resultDef

instance idv_defined : 𝚺ᴬ₁-Function₁ (idv : V → V) via idvDef := .mk fun v => by
  have h := (Idv.construction (V := V)).result_defined_iff v
  simpa [idvDef, idv, Matrix.empty_eq] using h

instance idv_definable : 𝚺ᴬ₁-Function₁ (idv : V → V) := idv_defined.to_definable
instance idv_definable' (Γ m) : Γᴬ_[m + 1]-Function₁ (idv : V → V) := .of_sigmaOne idv_definable

/-- `bv2 n = [#2, …, #(n+1)]`, `bv3 n = [#3, …, #(n+2)]`. -/
noncomputable def bv2 (n : V) : V := termBShiftVec ℒₛₑₜ n (termBShiftVec ℒₛₑₜ n (idv n))
noncomputable def bv3 (n : V) : V := termBShiftVec ℒₛₑₜ n (bv2 n)

noncomputable def bv2Def : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “y n. ∃ i, !idvDef i n ∧ ∃ a, !(termBShiftVecGraph ℒₛₑₜ) a n i ∧
    !(termBShiftVecGraph ℒₛₑₜ) y n a”

noncomputable def bv3Def : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “y n. ∃ b, !bv2Def b n ∧ !(termBShiftVecGraph ℒₛₑₜ) y n b”

instance bv2_defined : 𝚺ᴬ₁-Function₁ (bv2 : V → V) via bv2Def := .mk fun v => by
  simp [bv2Def, bv2, idv_defined.iff, termBShiftVec.defined.iff]

instance bv3_defined : 𝚺ᴬ₁-Function₁ (bv3 : V → V) via bv3Def := .mk fun v => by
  simp [bv3Def, bv3, bv2_defined.iff, termBShiftVec.defined.iff]

end

/-! ## Term graphs -/

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (ι : Interp)

/-- The marker shifted past `k` new bound variables. -/
noncomputable def bs (ε : V) : V := termBShift ℒₛₑₜ ε

/-- The equality template at a marker and two terms. -/
noncomputable def eqAt (ε a b : V) : V := subst ℒₛₑₜ (ε ∷ a ∷ b ∷ 0) (tq ι.eq : V)

/-- A unary template (zero, one, domain) at a marker and a term. -/
noncomputable def un (op : ℕ) (ε a : V) : V := subst ℒₛₑₜ (ε ∷ a ∷ 0) (op : V)

/-- A binary operation: `∃∃ (G a [#1] ∧ G b [#0] ∧ op(e, #1, #0, #2))`; `ε` is the marker for
terms with `n` bound variables. -/
noncomputable def binG (op : ℕ) (ε n a b : V) : V :=
  ^∃ ^∃ ((subst ℒₛₑₜ (^#1 ∷ bv3 n) a ^⋏ subst ℒₛₑₜ (^#0 ∷ bv3 n) b) ^⋏
    subst ℒₛₑₜ (bs (bs (bs ε)) ∷ ^#1 ∷ ^#0 ∷ ^#2 ∷ 0) (op : V))

/-- The graph of a function application. -/
noncomputable def funcG (ε n k g w : V) : V :=
  if k = 2 ∧ g = addIndex then binG (tq ι.add) ε n w.[0] w.[1]
  else if k = 2 ∧ g = mulIndex then binG (tq ι.mul) ε n w.[0] w.[1]
  else if k = 0 ∧ g = zeroIndex then un (tq ι.zero) (bs ε) ^#0
  else if k = 0 ∧ g = oneIndex then un (tq ι.one) (bs ε) ^#0
  else 0

end

noncomputable def bsDef : 𝚺ᴬ₁.Semisentence 2 := termBShiftGraph ℒₛₑₜ

noncomputable def eqAtDef (ι : Interp) : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y e a b. ∃ w₂, !adjoinDef w₂ b 0 ∧ ∃ w₁, !adjoinDef w₁ a w₂ ∧ ∃ w, !adjoinDef w e w₁ ∧
    !(substsGraph ℒₛₑₜ) y w ↑(tq ι.eq)”

noncomputable def unDef (op : ℕ) : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “y e a. ∃ w₁, !adjoinDef w₁ a 0 ∧ ∃ w, !adjoinDef w e w₁ ∧ !(substsGraph ℒₛₑₜ) y w ↑op”

noncomputable def binGDef (op : ℕ) : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “y e n a b. ∃ v, !bv3Def v n ∧ ∃ b₁, !qqBvarDef b₁ 1 ∧ ∃ b₀, !qqBvarDef b₀ 0 ∧
    ∃ b₂, !qqBvarDef b₂ 2 ∧ ∃ l, !adjoinDef l b₁ v ∧ ∃ r, !adjoinDef r b₀ v ∧
    ∃ sa, !(substsGraph ℒₛₑₜ) sa l a ∧ ∃ sb, !(substsGraph ℒₛₑₜ) sb r b ∧
    ∃ e₁, !bsDef e₁ e ∧ ∃ e₂, !bsDef e₂ e₁ ∧ ∃ e₃, !bsDef e₃ e₂ ∧
    ∃ t₃, !adjoinDef t₃ b₂ 0 ∧ ∃ t₂, !adjoinDef t₂ b₀ t₃ ∧ ∃ t₁, !adjoinDef t₁ b₁ t₂ ∧
    ∃ t₀, !adjoinDef t₀ e₃ t₁ ∧
    ∃ o, !(substsGraph ℒₛₑₜ) o t₀ ↑op ∧ ∃ c₁, !qqAndDef c₁ sa sb ∧ ∃ c₂, !qqAndDef c₂ c₁ o ∧
    ∃ x, !qqExsDef x c₂ ∧ !qqExsDef y x”

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (ι : Interp)

lemma bs_defined : 𝚺ᴬ₁-Function₁ (bs : V → V) via bsDef := termBShift.defined (L := ℒₛₑₜ)

instance bs_definable : 𝚺ᴬ₁-Function₁ (bs : V → V) := bs_defined.to_definable
instance bs_definable' (Γ m) : Γᴬ_[m + 1]-Function₁ (bs : V → V) := .of_sigmaOne bs_definable

lemma eqAt_defined : 𝚺ᴬ₁-Function₃ (eqAt ι : V → V → V → V) via eqAtDef ι := .mk fun v => by
  simp [eqAtDef, eqAt, subst.defined.iff, numeral_eq_natCast]

lemma un_defined (op : ℕ) : 𝚺ᴬ₁-Function₂ (un op : V → V → V) via unDef op := .mk fun v => by
  simp [unDef, un, subst.defined.iff, numeral_eq_natCast]

lemma binG_defined (op : ℕ) : 𝚺ᴬ₁-Function₄ (binG op : V → V → V → V → V) via binGDef op :=
  .mk fun v => by
    simp [binGDef, binG, bv3_defined.iff, subst.defined.iff, bs_defined.iff, numeral_eq_natCast]

end

namespace Graph

noncomputable def funcDef (ι : Interp) : 𝚺ᴬ₁.Semisentence 7 := .mkSigma “y k g v w n e.
    (k = 2 ∧ g = ↑addIndex → ∃ a, !nthDef a w 0 ∧ ∃ b, !nthDef b w 1 ∧
      !(binGDef (tq ι.add)) y e n a b) ∧
    (¬(k = 2 ∧ g = ↑addIndex) → k = 2 ∧ g = ↑mulIndex →
      ∃ a, !nthDef a w 0 ∧ ∃ b, !nthDef b w 1 ∧ !(binGDef (tq ι.mul)) y e n a b) ∧
    (¬(k = 2 ∧ g = ↑addIndex) → ¬(k = 2 ∧ g = ↑mulIndex) → k = 0 ∧ g = ↑zeroIndex →
      ∃ e₁, !bsDef e₁ e ∧ ∃ b₀, !qqBvarDef b₀ 0 ∧ !(unDef (tq ι.zero)) y e₁ b₀) ∧
    (¬(k = 2 ∧ g = ↑addIndex) → ¬(k = 2 ∧ g = ↑mulIndex) → ¬(k = 0 ∧ g = ↑zeroIndex) →
      k = 0 ∧ g = ↑oneIndex →
      ∃ e₁, !bsDef e₁ e ∧ ∃ b₀, !qqBvarDef b₀ 0 ∧ !(unDef (tq ι.one)) y e₁ b₀) ∧
    (¬(k = 2 ∧ g = ↑addIndex) → ¬(k = 2 ∧ g = ↑mulIndex) → ¬(k = 0 ∧ g = ↑zeroIndex) →
      ¬(k = 0 ∧ g = ↑oneIndex) → y = 0)”

noncomputable def bvarDef (ι : Interp) : 𝚺ᴬ₁.Semisentence 4 := .mkSigma “y z n e.
    ∃ e₁, !bsDef e₁ e ∧ ∃ b₀, !qqBvarDef b₀ 0 ∧ ∃ b, !qqBvarDef b (z + 1) ∧
      !(eqAtDef ι) y e₁ b₀ b”

noncomputable def fvarDef (ι : Interp) : 𝚺ᴬ₁.Semisentence 4 := .mkSigma “y x n e.
    ∃ e₁, !bsDef e₁ e ∧ ∃ b₀, !qqBvarDef b₀ 0 ∧ ∃ b, !qqFvarDef b x ∧ !(eqAtDef ι) y e₁ b₀ b”

noncomputable def blueprint (ι : Interp) : Language.TermRec.Blueprint 2 where
  bvar := bvarDef ι
  fvar := fvarDef ι
  func := funcDef ι

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (ι : Interp)

lemma func_defined : 𝚺ᴬ₁.DefinedFunction
    (fun v : Fin 6 → V => funcG ι (v 5) (v 4) (v 0) (v 1) (v 3)) (funcDef ι) := .mk fun v => by
  simp only [funcDef]
  simp [(binG_defined (V := V) _).iff, (un_defined (V := V) _).iff, bs_defined.iff,
    numeral_eq_natCast]
  unfold funcG
  split_ifs <;> simp_all <;> tauto

lemma bvar_defined : 𝚺ᴬ₁.DefinedFunction
    (fun v : Fin 3 → V => eqAt ι (bs (v 2)) ^#0 ^#(v 0 + 1)) (bvarDef ι) := .mk fun v => by
  simp [bvarDef, (eqAt_defined (V := V) ι).iff, bs_defined.iff]

lemma fvar_defined : 𝚺ᴬ₁.DefinedFunction
    (fun v : Fin 3 → V => eqAt ι (bs (v 2)) ^#0 ^&(v 0)) (fvarDef ι) := .mk fun v => by
  simp [fvarDef, (eqAt_defined (V := V) ι).iff, bs_defined.iff]

noncomputable def construction : Language.TermRec.Construction V (blueprint ι) where
  bvar p z := eqAt ι (bs (p 1)) ^#0 ^#(z + 1)
  fvar p x := eqAt ι (bs (p 1)) ^#0 ^&x
  func p k g _ w := funcG ι (p 1) (p 0) k g w
  bvar_defined := bvar_defined ι
  fvar_defined := fvar_defined ι
  func_defined := func_defined ι

end Graph

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (ι : Interp)

/-- The graph of a term with `n` bound variables, at the marker `ε`. -/
noncomputable def G (ε n t : V) : V := (Graph.construction ι).result ℒₒᵣ ![n, ε] t

@[simp] lemma G_bvar (ε n z : V) : G ι ε n ^#z = eqAt ι (bs ε) ^#0 ^#(z + 1) := by
  simp [G, Graph.construction]

@[simp] lemma G_fvar (ε n x : V) : G ι ε n ^&x = eqAt ι (bs ε) ^#0 ^&x := by
  simp [G, Graph.construction]

end

end ZF192Support.Internal.Arith
