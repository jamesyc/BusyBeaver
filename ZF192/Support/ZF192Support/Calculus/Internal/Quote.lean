module
public import ZF192Support.Calculus.Internal.Tait.Equations
public import ZF192Support.Calculus.Internal.Tait.Sequent
@[expose] public section
/-! # The translation of standard formulas, computed outside

`trX e d m f φ` is the pair `⟪χ φ, χ (∼φ)⟫` computed by recursion on a standard formula `φ`;
it agrees with the internal `tr` on `⌜φ⌝` in every model (`tr_quote`). -/
namespace ZF192Support.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ZF192Support.Internal ZF192Support.Internal.Tait

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The label of a standard term. -/
noncomputable def tlab (e m : V) {n : ℕ} : SyntacticSemiterm ℒₛₑₜ n → V
  | #i => e.[((i : ℕ) : V)]
  | &j => ylab (m + (j : V))
  | .func f _ => nomatch f

/-- The atom of a standard relation (`=` is `0`, `∈` is `1`). -/
noncomputable def atomX (e m : V) {n k : ℕ} (R : (ℒₛₑₜ).Rel k) (v : Fin k → SyntacticSemiterm ℒₛₑₜ n) :
    V :=
  match k, R, v with
  | 2, .eq, v => atomL 0 (tlab e m (v 0)) (tlab e m (v 1))
  | 2, .mem, v => atomL 1 (tlab e m (v 0)) (tlab e m (v 1))

variable (m f : V)

/-- `⟪χ φ, χ (∼φ)⟫` for a standard formula. -/
noncomputable def trX : {n : ℕ} → (e d : V) → Semiproposition ℒₛₑₜ n → V × V
  | _, _, _, .verum => (cneg 1, cneg (cneg 1))
  | _, _, _, .falsum => (cneg (cneg 1), cneg 1)
  | _, e, _, .rel R v => (atomX e m R v, cneg (atomX e m R v))
  | _, e, _, .nrel R v => (cneg (atomX e m R v), atomX e m R v)
  | _, e, d, .and p q => (cand (trX e d p).1 (trX e d q).1, cneg (cand (trX e d p).1 (trX e d q).1))
  | _, e, d, .or p q => (cneg (cand (trX e d p).2 (trX e d q).2), cand (trX e d p).2 (trX e d q).2)
  | _, e, d, .all p =>
    (all (xlab f d) (trX (xlab f d ∷ e) (d + 1) p).1, cneg (all (xlab f d) (trX (xlab f d ∷ e) (d + 1) p).1))
  | _, e, d, .exs p =>
    (cneg (all (xlab f d) (trX (xlab f d ∷ e) (d + 1) p).2), all (xlab f d) (trX (xlab f d ∷ e) (d + 1) p).2)

end

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma vlab_quote (e m : V) {n : ℕ} (t : SyntacticSemiterm ℒₛₑₜ n) :
    vlab e m (⌜t⌝ : V) = tlab e m t := by
  rcases t with i | j | ⟨f, _⟩
  · simp [tlab]
  · simp [tlab]
  · exact nomatch f

lemma encode_eqRel : Encodable.encode (Language.Set.Rel.eq : (ℒₛₑₜ).Rel 2) = 0 := rfl
lemma encode_memRel : Encodable.encode (Language.Set.Rel.mem : (ℒₛₑₜ).Rel 2) = 1 := rfl

/-- The internal translation of a standard formula. -/
theorem tr_quote (m f : V) {n : ℕ} (φ : Semiproposition ℒₛₑₜ n) : ∀ e d : V,
    tr ⟪e, d, m, f⟫ (⌜φ⌝ : V) = ⟪(trX m f e d φ).1, (trX m f e d φ).2⟫ := by
  induction φ using Semiformula.rec' with
  | hverum => intro e d; simp [trX, posPair]
  | hfalsum => intro e d; simp [trX, negPair]
  | hrel R v =>
    intro e d
    rename_i k
    match k, R with
    | 2, .eq =>
      rw [Semiformula.quote_rel, tr_rel (by simp [GödelQuote.quote, encode_eqRel, encode_memRel]) (by simp)]
      simp [trX, posPair, atomX, atom, ← vlab_quote, atomL, GödelQuote.quote, encode_eqRel, encode_memRel, Matrix.vecHead, Matrix.vecTail]
    | 2, .mem =>
      rw [Semiformula.quote_rel, tr_rel (by simp [GödelQuote.quote, encode_eqRel, encode_memRel]) (by simp)]
      simp [trX, posPair, atomX, atom, ← vlab_quote, atomL, GödelQuote.quote, encode_eqRel, encode_memRel, Matrix.vecHead, Matrix.vecTail]
  | hnrel R v =>
    intro e d
    rename_i k
    match k, R with
    | 2, .eq =>
      rw [Semiformula.quote_nrel, tr_nrel (by simp [GödelQuote.quote, encode_eqRel, encode_memRel]) (by simp)]
      simp [trX, negPair, atomX, atom, ← vlab_quote, atomL, GödelQuote.quote, encode_eqRel, encode_memRel, Matrix.vecHead, Matrix.vecTail]
    | 2, .mem =>
      rw [Semiformula.quote_nrel, tr_nrel (by simp [GödelQuote.quote, encode_eqRel, encode_memRel]) (by simp)]
      simp [trX, negPair, atomX, atom, ← vlab_quote, atomL, GödelQuote.quote, encode_eqRel, encode_memRel, Matrix.vecHead, Matrix.vecTail]
  | hand p q ihp ihq =>
    intro e d
    rw [Semiformula.quote_and, tr_and (Semiformula.quote_isSemiformula p).isUFormula
      (Semiformula.quote_isSemiformula q).isUFormula, ihp, ihq]
    simp [trX, posPair]
  | hor p q ihp ihq =>
    intro e d
    rw [Semiformula.quote_or, tr_or (Semiformula.quote_isSemiformula p).isUFormula
      (Semiformula.quote_isSemiformula q).isUFormula, ihp, ihq]
    simp [trX, negPair]
  | hall p ih =>
    intro e d
    rw [Semiformula.quote_all, tr_all (Semiformula.quote_isSemiformula p).isUFormula, step_mk, ih]
    simp [trX, posPair]
  | hexs p ih =>
    intro e d
    rw [Semiformula.quote_ex, tr_exs (Semiformula.quote_isSemiformula p).isUFormula, step_mk, ih]
    simp [trX, negPair]

lemma chiS_quote (m : V) (σ : Sentence ℒₛₑₜ) :
    chiS m (⌜σ⌝ : V) = (trX m 0 0 0 (Rewriting.emb σ : Semiproposition ℒₛₑₜ 0)).1 := by
  rw [chiS, Sentence.quote_def, tr_quote]; simp

end

end ZF192Support.Halting
