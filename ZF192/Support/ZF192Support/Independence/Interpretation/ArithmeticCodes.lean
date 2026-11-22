module
public import ZF192Support.Independence.Arithmetization.AxStep
@[expose] public section
/-! # The marker translation of standard formulas, outside

`Gx ι ε t` and `Jx ι ε p` mirror the internal term graph `G` and formula translation `J` on
standard terms and formulas, so that `⌜Jx ι ε p⌝ = J ι ⌜ε⌝ n ⌜p⌝` in every model
(`quote_Jx`). `kaxX ι σ = ∀e (Mark e → Ĵσ)` has code `kax ι ⌜σ⌝`. -/
namespace ZF192Support.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

variable (ι : ZF192Support.Internal.Arith.Interp)

/-- A template instance. -/
def tpl {k n : ℕ} (φ : Semisentence ℒₛₑₜ k) (w : Fin k → Semiterm ℒₛₑₜ ℕ n) :
    Semiformula ℒₛₑₜ ℕ n :=
  (Rewriting.emb φ : Semiproposition ℒₛₑₜ k) ⇜ w

/-- `[#k, #(j + d)]`: the value variable at `k`, the term variables pushed up by `d`. -/
def pushV {n : ℕ} (d : ℕ) (k : Fin (n + d)) : Fin (n + 1) → Semiterm ℒₛₑₜ ℕ (n + d) :=
  Fin.cases #k fun j => #(j.addNat d)

/-- The graph of a standard term: the value is `#0`, the term's variables are `#(i+1)`. -/
def Gx {n : ℕ} (ε : Semiterm ℒₛₑₜ ℕ n) : Semiterm ℒₒᵣ ℕ n → Semiformula ℒₛₑₜ ℕ (n + 1)
  | #z => tpl ι.eq ![Rew.bShift ε, #0, #z.succ]
  | &x => tpl ι.eq ![Rew.bShift ε, #0, &x]
  | .func Language.ORing.Func.zero _ => tpl ι.zero ![Rew.bShift ε, #0]
  | .func Language.ORing.Func.one _ => tpl ι.one ![Rew.bShift ε, #0]
  | .func Language.ORing.Func.add v =>
    ∃¹ ∃¹ (((Gx ε (v 0)) ⇜ pushV 3 1 ⋏ (Gx ε (v 1)) ⇜ pushV 3 0) ⋏
      tpl ι.add ![Rew.bShift (Rew.bShift (Rew.bShift ε)), #1, #0, #2])
  | .func Language.ORing.Func.mul v =>
    ∃¹ ∃¹ (((Gx ε (v 0)) ⇜ pushV 3 1 ⋏ (Gx ε (v 1)) ⇜ pushV 3 0) ⋏
      tpl ι.mul ![Rew.bShift (Rew.bShift (Rew.bShift ε)), #1, #0, #2])

/-- The template of an ℒₒᵣ relation. -/
def relTx {k : ℕ} : Language.ORing.Rel k → Semisentence ℒₛₑₜ 3
  | .eq => ι.eq
  | .lt => ι.lt

/-- The translation of an atom. -/
def atomJx {n k : ℕ} (ε : Semiterm ℒₛₑₜ ℕ n) (r : Language.ORing.Rel k)
    (t₀ t₁ : Semiterm ℒₒᵣ ℕ n) : Semiformula ℒₛₑₜ ℕ n :=
  ∃¹ ∃¹ (((Gx ι ε t₀) ⇜ pushV 2 1 ⋏ (Gx ι ε t₁) ⇜ pushV 2 0) ⋏
    tpl (relTx ι r) ![Rew.bShift (Rew.bShift ε), #1, #0])

/-- The marker translation of a standard formula. -/
def Jx : {n : ℕ} → Semiterm ℒₛₑₜ ℕ n → Semiformula ℒₒᵣ ℕ n → Semiformula ℒₛₑₜ ℕ n
  | _, _, .verum => ⊤
  | _, _, .falsum => ⊥
  | _, ε, .rel (arity := 2) r v => atomJx ι ε r (v 0) (v 1)
  | _, ε, .nrel (arity := 2) r v => ∼atomJx ι ε r (v 0) (v 1)
  | _, ε, .and p q => Jx ε p ⋏ Jx ε q
  | _, ε, .or p q => Jx ε p ⋎ Jx ε q
  | _, ε, .all p => ∀¹ (∼tpl ι.dom ![Rew.bShift ε, #0] ⋎ Jx (Rew.bShift ε) p)
  | _, ε, .exs p => ∃¹ (tpl ι.dom ![Rew.bShift ε, #0] ⋏ Jx (Rew.bShift ε) p)

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
open Bootstrapping Bootstrapping.Arithmetic ZF192Support.Internal.Arith

lemma quote_tpl {k n : ℕ} (φ : Semisentence ℒₛₑₜ k) (w : Fin k → Semiterm ℒₛₑₜ ℕ n) :
    (⌜tpl φ w⌝ : V) =
      subst ℒₛₑₜ (SemitermVec.val fun i => (⌜w i⌝ : Bootstrapping.Semiterm V ℒₛₑₜ n)) (tq φ : V) := by
  simp [tpl, Semiformula.quote_def, tq_eq, Sentence.quote_def]

lemma vec_bvars_eq {n d : ℕ} (b : V) (hb : len b = n) (hnth : ∀ i < (n : V), b.[i] = ^#(i + d)) :
    SemitermVec.val (fun j : Fin n =>
      (⌜(#(j.addNat d) : Semiterm ℒₛₑₜ ℕ (n + d))⌝ : Bootstrapping.Semiterm V ℒₛₑₜ (n + d))) = b := by
  apply nth_ext (by simp [hb])
  intro i hi
  have hi' : i < (n : V) := by simpa using hi
  obtain ⟨j, rfl⟩ := eq_nat_of_lt_nat hi'
  have hj : j < n := by exact_mod_cast hi'
  rw [hnth _ hi', show ((j : ℕ) : V) = ((⟨j, hj⟩ : Fin n) : ℕ) from rfl, SemitermVec.val_nth_eq]
  simp

lemma val_pushV3 {n : ℕ} (k : Fin (n + 3)) :
    SemitermVec.val (fun i => (⌜pushV 3 k i⌝ : Bootstrapping.Semiterm V ℒₛₑₜ (n + 3))) =
      ^#((k : ℕ) : V) ∷ bv3 (n : V) := by
  rw [SemitermVec.val_succ]
  have ht : (Matrix.vecTail fun i => (⌜pushV 3 k i⌝ : Bootstrapping.Semiterm V ℒₛₑₜ (n + 3))) =
      fun j : Fin n => (⌜(#(j.addNat 3) : Semiterm ℒₛₑₜ ℕ (n + 3))⌝ : Bootstrapping.Semiterm V ℒₛₑₜ (n + 3)) := by
    funext j; simp [Matrix.vecTail, pushV]
  rw [ht, vec_bvars_eq _ (by simp) (fun i hi => nth_bv3 hi)]
  simp [pushV, Matrix.vecHead]

lemma val_pushV2 {n : ℕ} (k : Fin (n + 2)) :
    SemitermVec.val (fun i => (⌜pushV 2 k i⌝ : Bootstrapping.Semiterm V ℒₛₑₜ (n + 2))) =
      ^#((k : ℕ) : V) ∷ bv2 (n : V) := by
  rw [SemitermVec.val_succ]
  have ht : (Matrix.vecTail fun i => (⌜pushV 2 k i⌝ : Bootstrapping.Semiterm V ℒₛₑₜ (n + 2))) =
      fun j : Fin n => (⌜(#(j.addNat 2) : Semiterm ℒₛₑₜ ℕ (n + 2))⌝ : Bootstrapping.Semiterm V ℒₛₑₜ (n + 2)) := by
    funext j; simp [Matrix.vecTail, pushV]
  rw [ht, vec_bvars_eq _ (by simp) (fun i hi => nth_bv2 hi)]
  simp [pushV, Matrix.vecHead]

lemma quote_subst_pushV3 {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ (n + 1)) (k : Fin (n + 3)) :
    (⌜φ ⇜ pushV 3 k⌝ : V) = subst ℒₛₑₜ (^#((k : ℕ) : V) ∷ bv3 (n : V)) (⌜φ⌝ : V) := by
  rw [Semiformula.quote_def, Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs,
    val_pushV3, ← Semiformula.quote_def]

lemma quote_subst_pushV2 {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ (n + 1)) (k : Fin (n + 2)) :
    (⌜φ ⇜ pushV 2 k⌝ : V) = subst ℒₛₑₜ (^#((k : ℕ) : V) ∷ bv2 (n : V)) (⌜φ⌝ : V) := by
  rw [Semiformula.quote_def, Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs,
    val_pushV2, ← Semiformula.quote_def]

theorem quote_Gx {n : ℕ} (ε : Semiterm ℒₛₑₜ ℕ n) (t : Semiterm ℒₒᵣ ℕ n) :
    (⌜Gx ι ε t⌝ : V) = G ι (⌜ε⌝ : V) (n : V) (⌜t⌝ : V) := by
  induction t with
  | bvar z =>
    simp [Gx, quote_tpl, eqAt, bs, Semiterm.quote_def, Matrix.vecHead, Matrix.vecTail]
  | fvar x =>
    simp [Gx, quote_tpl, eqAt, bs, Semiterm.quote_def, Matrix.vecHead, Matrix.vecTail]
  | func f v ih =>
    cases f with
    | zero =>
      simp [Gx, quote_tpl, Semiterm.quote_def, Matrix.vecHead, Matrix.vecTail]
      erw [quote_func_zero]
      rw [← qqZero_eq_qqFunc, G_zero]; simp [un, bs]
    | one =>
      simp [Gx, quote_tpl, Semiterm.quote_def, Matrix.vecHead, Matrix.vecTail]
      erw [quote_func_one]
      rw [← qqOne_eq_qqFunc, G_one]; simp [un, bs]
    | add =>
      have h2 : 2 % (n + 1 + 1 + 1) = 2 := Nat.mod_eq_of_lt (by omega)
      simp only [Gx, Semiformula.quote_ex, Semiformula.quote_and, quote_subst_pushV3, quote_tpl, ih]
      simp [Semiterm.quote_def, Matrix.vecHead, Matrix.vecTail, h2]
      erw [quote_func_add]
      rw [show (^func 2 (addIndex : V) ((⌜v 0⌝ : Bootstrapping.Semiterm V ℒₒᵣ n).val ∷
        (⌜v 1⌝ : Bootstrapping.Semiterm V ℒₒᵣ n).val ∷ 0)) = (⌜v 0⌝ : Bootstrapping.Semiterm V ℒₒᵣ n).val ^+
        (⌜v 1⌝ : Bootstrapping.Semiterm V ℒₒᵣ n).val from rfl, G_add ι (by simp) (by simp), binG]
      simp [bs]
    | mul =>
      have h2 : 2 % (n + 1 + 1 + 1) = 2 := Nat.mod_eq_of_lt (by omega)
      simp only [Gx, Semiformula.quote_ex, Semiformula.quote_and, quote_subst_pushV3, quote_tpl, ih]
      simp [Semiterm.quote_def, Matrix.vecHead, Matrix.vecTail, h2]
      erw [quote_func_mul]
      rw [show (^func 2 (mulIndex : V) ((⌜v 0⌝ : Bootstrapping.Semiterm V ℒₒᵣ n).val ∷
        (⌜v 1⌝ : Bootstrapping.Semiterm V ℒₒᵣ n).val ∷ 0)) = (⌜v 0⌝ : Bootstrapping.Semiterm V ℒₒᵣ n).val ^*
        (⌜v 1⌝ : Bootstrapping.Semiterm V ℒₒᵣ n).val from rfl, G_mul ι (by simp) (by simp), binG]
      simp [bs]

lemma quote_neg' {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n) : (⌜∼φ⌝ : V) = neg ℒₛₑₜ (⌜φ⌝ : V) := by
  simp [Semiformula.quote_def]

lemma quote_rel_eqI : (⌜(Language.ORing.Rel.eq : (ℒₒᵣ).Rel 2)⌝ : V) = eqIndex := rfl
lemma quote_rel_ltI : (⌜(Language.ORing.Rel.lt : (ℒₒᵣ).Rel 2)⌝ : V) = ltIndex := rfl

lemma quote_atomJx {n : ℕ} (ε : Semiterm ℒₛₑₜ ℕ n) (r : Language.ORing.Rel 2) (t₀ t₁ : Semiterm ℒₒᵣ ℕ n) :
    (⌜atomJx ι ε r t₀ t₁⌝ : V) = atomJ ι (⌜ε⌝ : V) (n : V) (⌜r⌝ : V) (⌜t₀⌝ : V) (⌜t₁⌝ : V) := by
  simp only [atomJx, Semiformula.quote_ex, Semiformula.quote_and, quote_subst_pushV2, quote_tpl,
    quote_Gx]
  cases r
  · simp [atomJ, relT, relTx, quote_rel_eqI, Semiterm.quote_def, Matrix.vecHead, Matrix.vecTail, bs]
  · simp [atomJ, relT, relTx, quote_rel_ltI, eqIndex_ne_ltIndex.symm, Semiterm.quote_def,
      Matrix.vecHead, Matrix.vecTail, bs]

theorem quote_Jx {n : ℕ} (p : Semiformula ℒₒᵣ ℕ n) : ∀ ε : Semiterm ℒₛₑₜ ℕ n,
    (⌜Jx ι ε p⌝ : V) = J ι (⌜ε⌝ : V) (n : V) (⌜p⌝ : V) := by
  induction p using Semiformula.rec' with
  | hverum => intro ε; simp [Jx]
  | hfalsum => intro ε; simp [Jx]
  | hrel r v =>
    intro ε
    rename_i k
    match k, r with
    | 2, r =>
      have hR : (ℒₒᵣ).IsRel ((2 : ℕ) : V) (⌜r⌝ : V) := by cases r <;> simp [quote_rel_eqI, quote_rel_ltI]
      simp only [Jx, quote_atomJx]
      rw [Semiformula.quote_rel, J_rel hR (by simp)]
      simp [Semiterm.quote_def, Matrix.vecHead, Matrix.vecTail]
  | hnrel r v =>
    intro ε
    rename_i k
    match k, r with
    | 2, r =>
      have hR : (ℒₒᵣ).IsRel ((2 : ℕ) : V) (⌜r⌝ : V) := by cases r <;> simp [quote_rel_eqI, quote_rel_ltI]
      simp only [Jx, quote_neg', quote_atomJx]
      rw [Semiformula.quote_nrel, J_nrel hR (by simp)]
      simp [Semiterm.quote_def, Matrix.vecHead, Matrix.vecTail]
  | hand p q ihp ihq =>
    intro ε
    simp [Jx, ihp, ihq, J_and (Semiformula.quote_isSemiformula p).isUFormula
      (Semiformula.quote_isSemiformula q).isUFormula]
  | hor p q ihp ihq =>
    intro ε
    simp [Jx, ihp, ihq, J_or (Semiformula.quote_isSemiformula p).isUFormula
      (Semiformula.quote_isSemiformula q).isUFormula]
  | hall p ih =>
    intro ε
    rw [Semiformula.quote_all, J_all (Semiformula.quote_isSemiformula p).isUFormula]
    simp [Jx, ih, quote_tpl, quote_neg', un, bs, Semiterm.quote_def, Matrix.vecHead, Matrix.vecTail]
  | hexs p ih =>
    intro ε
    rw [Semiformula.quote_ex, J_exs (Semiformula.quote_isSemiformula p).isUFormula]
    simp [Jx, ih, quote_tpl, quote_neg', un, bs, Semiterm.quote_def, Matrix.vecHead, Matrix.vecTail]

end

/-- `∀e (Mark e → Ĵσ)` for a sentence `σ`, as a proposition. -/
def kaxP (σ : Sentence ℒₒᵣ) : Proposition ℒₛₑₜ :=
  ∀¹ (∼tpl ι.mark ![#0] ⋎ Jx ι #0 (Rew.castLE (by simp : 0 ≤ 1) ▹ (Rewriting.emb σ : Proposition ℒₒᵣ)))

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
open Bootstrapping Bootstrapping.Arithmetic ZF192Support.Internal.Arith

theorem quote_kaxP (σ : Sentence ℒₒᵣ) : (⌜kaxP ι σ⌝ : V) = kax ι (⌜σ⌝ : V) := by
  simp [kaxP, kax, jhat, markAt, imp, quote_neg', quote_tpl, quote_Jx, Semiformula.quote_castLE,
    Sentence.quote_def, Semiterm.quote_def, Matrix.vecHead, Matrix.vecTail]

end

end ZF192Support.Halting
