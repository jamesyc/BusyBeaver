module
public import Halting.ChiX
public import Internal.Tait.Binder
public import Internal.EqModel
@[expose] public section
/-! # Facts about the translation of standard formulas

* `trX_neg`: negation swaps the two components.
* `pi2_iff`: the second component is C-equivalent to the negation of the first.
* `trX_rew`: a rewriting that renames bound variables is absorbed into the label vector.
* `sub_trX`, `vac_trX`: substitution and vacuity with side conditions only on the labels the
  translation actually binds (`BL`), not on whole label families.
* `lt_trX`: labels bound by the translation are below its code. -/
namespace ZF209.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ZF209.Internal ZF209.Internal.Tait ZF209.CKernel.Generic

section
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (m f : V)

lemma trX_neg : ∀ {n : ℕ} (e d : V) (φ : Semiproposition ℒₛₑₜ n),
    trX m f e d (∼φ) = ((trX m f e d φ).2, (trX m f e d φ).1)
  | _, _, _, .verum => by show trX m f _ _ .falsum = _; simp [trX]
  | _, _, _, .falsum => by show trX m f _ _ .verum = _; simp [trX]
  | _, _, _, .rel _ _ => by simp [trX]
  | _, _, _, .nrel _ _ => by simp [trX]
  | _, e, d, .and p q => by
    show trX m f e d (.or (∼p) (∼q)) = _; simp [trX, trX_neg e d p, trX_neg e d q]
  | _, e, d, .or p q => by
    show trX m f e d (.and (∼p) (∼q)) = _; simp [trX, trX_neg e d p, trX_neg e d q]
  | _, e, d, .all p => by
    show trX m f e d (.exs (∼p)) = _; simp [trX, trX_neg _ _ p]
  | _, e, d, .exs p => by
    show trX m f e d (.all (∼p)) = _; simp [trX, trX_neg _ _ p]

/-- Labels bound by the translation at depth `d`. -/
def BL : {n : ℕ} → V → Semiproposition ℒₛₑₜ n → V → Prop
  | _, d, .and p q, l => BL d p l ∨ BL d q l
  | _, d, .or p q, l => BL d p l ∨ BL d q l
  | _, d, .all p, l => l = xlab f d ∨ BL (d + 1) p l
  | _, d, .exs p, l => l = xlab f d ∨ BL (d + 1) p l
  | _, _, _, _ => False

lemma lt_cneg (a : V) : a < cneg a := by
  have h1 : (1 : V) ≤ cantor a 1 := le_cantor_right a 1
  have hpos : (0 : V) < cantor a 1 := lt_of_lt_of_le _root_.zero_lt_one h1
  calc a ≤ cantor a 1 := le_cantor_left a 1
    _ < 4 * cantor a 1 := lt_mul_of_one_lt_left hpos (by norm_num)
    _ = cneg a := rfl

lemma lt_all_label (x a : V) : x < all x a :=
  lt_of_le_of_lt (le_trans (le_cantor_right a x) (le_four_mul _)) (by simp [all])

lemma lt_all_body (x a : V) : a < all x a :=
  lt_of_le_of_lt (le_trans (le_cantor_left a x) (le_four_mul _)) (by simp [all])

lemma lt_trX : ∀ {n : ℕ} (e d : V) (φ : Semiproposition ℒₛₑₜ n) (l : V), BL f d φ l →
    l < (trX m f e d φ).1 ∧ l < (trX m f e d φ).2
  | _, e, d, .and p q, l, h => by
    have k : l < cand (trX m f e d p).1 (trX m f e d q).1 := by
      rcases h with h | h
      · exact lt_of_lt_of_le (lt_trX e d p l h).1 (left_le_cand _ _)
      · exact lt_of_lt_of_le (lt_trX e d q l h).1 (right_le_cand _ _)
    exact ⟨k, lt_trans k (lt_cneg _)⟩
  | _, e, d, .or p q, l, h => by
    have k : l < cand (trX m f e d p).2 (trX m f e d q).2 := by
      rcases h with h | h
      · exact lt_of_lt_of_le (lt_trX e d p l h).2 (left_le_cand _ _)
      · exact lt_of_lt_of_le (lt_trX e d q l h).2 (right_le_cand _ _)
    exact ⟨lt_trans k (lt_cneg _), k⟩
  | _, e, d, .all p, l, h => by
    have k : l < all (xlab f d) (trX m f (xlab f d ∷ e) (d + 1) p).1 := by
      rcases h with rfl | h
      · exact lt_all_label _ _
      · exact lt_trans (lt_trX _ _ p l h).1 (lt_all_body _ _)
    exact ⟨k, lt_trans k (lt_cneg _)⟩
  | _, e, d, .exs p, l, h => by
    have k : l < all (xlab f d) (trX m f (xlab f d ∷ e) (d + 1) p).2 := by
      rcases h with rfl | h
      · exact lt_all_label _ _
      · exact lt_trans (lt_trX _ _ p l h).2 (lt_all_body _ _)
    exact ⟨lt_trans k (lt_cneg _), k⟩

end

section
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (m f : V)

lemma nth_cons_succ (x e : V) (i : ℕ) : (x ∷ e).[((i + 1 : ℕ) : V)] = e.[(i : V)] := by
  simp

lemma tlab_rew {n₁ n₂ : ℕ} (ω : Rew ℒₛₑₜ ℕ n₁ ℕ n₂) (σ : Fin n₁ → Fin n₂)
    (hb : ∀ i, ω #i = #(σ i)) (hf : ∀ j, ω &j = &j) {e e' : V}
    (he : ∀ i : Fin n₁, e'.[((i : ℕ) : V)] = e.[((σ i : ℕ) : V)])
    (t : SyntacticSemiterm ℒₛₑₜ n₁) : tlab e m (ω t) = tlab e' m t := by
  rcases t with i | j | ⟨g, _⟩
  · rw [hb]; simp [tlab, he]
  · rw [hf]; simp [tlab]
  · exact nomatch g

/-- A rewriting renaming bound variables (and fixing free ones) moves into the labels. -/
theorem trX_rew : ∀ {n₁ : ℕ} (φ : Semiproposition ℒₛₑₜ n₁) {n₂ : ℕ} (ω : Rew ℒₛₑₜ ℕ n₁ ℕ n₂)
    (σ : Fin n₁ → Fin n₂), (∀ i, ω #i = #(σ i)) → (∀ j, ω &j = &j) → ∀ (e e' d : V),
    (∀ i : Fin n₁, e'.[((i : ℕ) : V)] = e.[((σ i : ℕ) : V)]) →
    trX m f e d (ω ▹ φ) = trX m f e' d φ
  | _, .verum, _, _, _, _, _, _, _, _, _ => by
    show trX m f _ _ .verum = _; simp [trX]
  | _, .falsum, _, _, _, _, _, _, _, _, _ => by
    show trX m f _ _ .falsum = _; simp [trX]
  | _, .rel R v, _, ω, σ, hb, hf, e, e', d, he => by
    rw [Semiformula.rew_rel]
    match R, v with
    | .eq, v => simp [trX, atomX, tlab_rew m ω σ hb hf he]
    | .mem, v => simp [trX, atomX, tlab_rew m ω σ hb hf he]
  | _, .nrel R v, _, ω, σ, hb, hf, e, e', d, he => by
    rw [Semiformula.rew_nrel]
    match R, v with
    | .eq, v => simp [trX, atomX, tlab_rew m ω σ hb hf he]
    | .mem, v => simp [trX, atomX, tlab_rew m ω σ hb hf he]
  | _, .and p q, _, ω, σ, hb, hf, e, e', d, he => by
    show trX m f e d (.and (ω ▹ p) (ω ▹ q)) = _
    simp [trX, trX_rew p ω σ hb hf e e' d he, trX_rew q ω σ hb hf e e' d he]
  | _, .or p q, _, ω, σ, hb, hf, e, e', d, he => by
    show trX m f e d (.or (ω ▹ p) (ω ▹ q)) = _
    simp [trX, trX_rew p ω σ hb hf e e' d he, trX_rew q ω σ hb hf e e' d he]
  | _, .all p, _, ω, σ, hb, hf, e, e', d, he => by
    have := trX_rew p ω.q (0 :> fun i => (σ i).succ) (fun i => by
        cases i using Fin.cases with
        | zero => simp
        | succ i => simp [hb])
      (fun j => by simp [hf]) (xlab f d ∷ e) (xlab f d ∷ e') (d + 1) (fun i => by
        cases i using Fin.cases with
        | zero => simp
        | succ i => simpa using he i)
    show trX m f e d (.all (ω.q ▹ p)) = _
    simp [trX, this]
  | _, .exs p, _, ω, σ, hb, hf, e, e', d, he => by
    have := trX_rew p ω.q (0 :> fun i => (σ i).succ) (fun i => by
        cases i using Fin.cases with
        | zero => simp
        | succ i => simp [hb])
      (fun j => by simp [hf]) (xlab f d ∷ e) (xlab f d ∷ e') (d + 1) (fun i => by
        cases i using Fin.cases with
        | zero => simp
        | succ i => simpa using he i)
    show trX m f e d (.exs (ω.q ▹ p)) = _
    simp [trX, this]

variable {L : IntLogic V}
open IntLogic

/-- The second component is equivalent to the negation of the first. -/
lemma pi2_iff : ∀ {n : ℕ} (e d : V) (φ : Semiproposition ℒₛₑₜ n),
    L.Pr (ciff (trX m f e d φ).2 (cneg (trX m f e d φ).1))
  | _, _, _, .verum => by
    simp only [trX]; exact iff_refl' _
  | _, _, _, .falsum => by simp only [trX]; exact dneg_iff _
  | _, _, _, .rel _ _ => by
    simp only [trX]; exact iff_refl' _
  | _, _, _, .nrel _ _ => by simp only [trX]; exact dneg_iff _
  | _, _, _, .and _ _ => by
    simp only [trX]; exact iff_refl' _
  | _, _, _, .or _ _ => by simp only [trX]; exact dneg_iff _
  | _, _, _, .all _ => by
    simp only [trX]; exact iff_refl' _
  | _, _, _, .exs _ => by simp only [trX]; exact dneg_iff _
where
  dneg_iff (a : V) : L.Pr (ciff a (cneg (cneg a))) := by
    rw [pr_iff]
    have c : L.S.toLogic.Ctx [] (L.S.iff a (L.S.neg (L.S.neg a))) :=
      Logic.Ctx.iffIntro (Logic.Ctx.deduction (Logic.Ctx.mp (Logic.Ctx.head.up _) Logic.Ctx.head))
        Logic.Ctx.head.dne
    simpa using c.empty

lemma tlab_notRes' {n : ℕ} {e : V} (he : ∀ i : Fin n, NotRes e.[((i : ℕ) : V)])
    (t : SyntacticSemiterm ℒₛₑₜ n) : NotRes (tlab e m t) := by
  rcases t with i | j | ⟨g, _⟩
  · exact he i
  · exact notRes_ylab _
  · exact nomatch g

lemma tlab_sub {n : ℕ} {a b e e' : V}
    (he : ∀ i : Fin n, e.[((i : ℕ) : V)] = e'.[((i : ℕ) : V)] ∨
      (e.[((i : ℕ) : V)] = a ∧ e'.[((i : ℕ) : V)] = b))
    (t : SyntacticSemiterm ℒₛₑₜ n) :
    tlab e m t = tlab e' m t ∨ (tlab e m t = a ∧ tlab e' m t = b) := by
  rcases t with i | j | ⟨g, _⟩
  · exact he i
  · exact Or.inl rfl
  · exact nomatch g

lemma sub_atomX {n k : ℕ} (R : (ℒₛₑₜ).Rel k) (v : Fin k → SyntacticSemiterm ℒₛₑₜ n) {a b e e' : V}
    (ha : NotRes a) (hb : NotRes b) (hn : ∀ i : Fin n, NotRes e.[((i : ℕ) : V)])
    (hn' : ∀ i : Fin n, NotRes e'.[((i : ℕ) : V)])
    (hs : ∀ i : Fin n, e.[((i : ℕ) : V)] = e'.[((i : ℕ) : V)] ∨
      (e.[((i : ℕ) : V)] = a ∧ e'.[((i : ℕ) : V)] = b)) :
    L.SubEq a b (atomX e m R v) (atomX e' m R v) :=
  match k, R, v with
  | 2, .eq, _ => sub_atomL 0 ha hb (tlab_notRes' m hn' _) (tlab_notRes' m hn _)
      (tlab_sub m hs _) (tlab_sub m hs _)
  | 2, .mem, _ => sub_atomL 1 ha hb (tlab_notRes' m hn' _) (tlab_notRes' m hn _)
      (tlab_sub m hs _) (tlab_sub m hs _)

lemma vac_atomX {n k : ℕ} (R : (ℒₛₑₜ).Rel k) (v : Fin k → SyntacticSemiterm ℒₛₑₜ n) {e z : V}
    (hz : NotRes z) (ht : ∀ i, tlab e m (v i) ≠ z) : L.Vac z (atomX e m R v) :=
  match k, R, v with
  | 2, .eq, _ => vac_atomL hz (Ne.symm (ht 0)) (Ne.symm (ht 1))
  | 2, .mem, _ => vac_atomL hz (Ne.symm (ht 0)) (Ne.symm (ht 1))

/-- Substitution in translations, with conditions only on the bound labels. -/
theorem sub_trX : ∀ {n : ℕ} (φ : Semiproposition ℒₛₑₜ n) (a b e e' d : V),
    (∀ i : Fin n, e.[((i : ℕ) : V)] = e'.[((i : ℕ) : V)] ∨
      (e.[((i : ℕ) : V)] = a ∧ e'.[((i : ℕ) : V)] = b)) →
    (∀ l, BL f d φ l → l ≠ a ∧ l ≠ b) → NotRes a → NotRes b →
    (∀ i : Fin n, NotRes e.[((i : ℕ) : V)]) → (∀ i : Fin n, NotRes e'.[((i : ℕ) : V)]) →
    L.SubEq a b (trX m f e d φ).1 (trX m f e' d φ).1 ∧
      L.SubEq a b (trX m f e d φ).2 (trX m f e' d φ).2
  | _, .verum, _, _, _, _, _, _, _, _, _, _, _ => ⟨sub_refl _ _ _, sub_refl _ _ _⟩
  | _, .falsum, _, _, _, _, _, _, _, _, _, _, _ => ⟨sub_refl _ _ _, sub_refl _ _ _⟩
  | _, .rel R v, a, b, e, e', d, hs, _, ha, hb, hn, hn' => by
    have hA := sub_atomX (L := L) m R v ha hb hn hn' hs
    exact ⟨hA, sub_neg hA⟩
  | _, .nrel R v, a, b, e, e', d, hs, _, ha, hb, hn, hn' => by
    have hA := sub_atomX (L := L) m R v ha hb hn hn' hs
    exact ⟨sub_neg hA, hA⟩
  | _, .and p q, a, b, e, e', d, hs, hl, ha, hb, hn, hn' => by
    have h₁ := sub_trX p a b e e' d hs (fun l h => hl l (Or.inl h)) ha hb hn hn'
    have h₂ := sub_trX q a b e e' d hs (fun l h => hl l (Or.inr h)) ha hb hn hn'
    exact ⟨sub_and h₁.1 h₂.1, sub_neg (sub_and h₁.1 h₂.1)⟩
  | _, .or p q, a, b, e, e', d, hs, hl, ha, hb, hn, hn' => by
    have h₁ := sub_trX p a b e e' d hs (fun l h => hl l (Or.inl h)) ha hb hn hn'
    have h₂ := sub_trX q a b e e' d hs (fun l h => hl l (Or.inr h)) ha hb hn hn'
    exact ⟨sub_neg (sub_and h₁.2 h₂.2), sub_and h₁.2 h₂.2⟩
  | _, .all p, a, b, e, e', d, hs, hl, ha, hb, hn, hn' => by
    have hx := hl (xlab f d) (Or.inl rfl)
    have h := sub_trX p a b (xlab f d ∷ e) (xlab f d ∷ e') (d + 1)
      (fun i => by
        cases i using Fin.cases with
        | zero => simp
        | succ i => simpa using hs i)
      (fun l h => hl l (Or.inr h)) ha hb
      (fun i => by
        cases i using Fin.cases with
        | zero => simpa using notRes_xlab f d
        | succ i => simpa using hn i)
      (fun i => by
        cases i using Fin.cases with
        | zero => simpa using notRes_xlab f d
        | succ i => simpa using hn' i)
    have hA := sub_all (xlab f d) (notRes_xlab f d).1 hx.1 hx.2 h.1
    exact ⟨hA, sub_neg hA⟩
  | _, .exs p, a, b, e, e', d, hs, hl, ha, hb, hn, hn' => by
    have hx := hl (xlab f d) (Or.inl rfl)
    have h := sub_trX p a b (xlab f d ∷ e) (xlab f d ∷ e') (d + 1)
      (fun i => by
        cases i using Fin.cases with
        | zero => simp
        | succ i => simpa using hs i)
      (fun l h => hl l (Or.inr h)) ha hb
      (fun i => by
        cases i using Fin.cases with
        | zero => simpa using notRes_xlab f d
        | succ i => simpa using hn i)
      (fun i => by
        cases i using Fin.cases with
        | zero => simpa using notRes_xlab f d
        | succ i => simpa using hn' i)
    have hA := sub_all (xlab f d) (notRes_xlab f d).1 hx.1 hx.2 h.2
    exact ⟨sub_neg hA, hA⟩

lemma emb_all' {n : ℕ} (p : Semisentence ℒₛₑₜ (n + 1)) :
    (Rewriting.emb (Semiformula.all p) : Semiproposition ℒₛₑₜ n) =
      Semiformula.all (Rewriting.emb p) := by
  change (Rewriting.emb (∀¹ p) : Semiproposition ℒₛₑₜ n) = ∀¹ (Rewriting.emb p)
  simp [Rewriting.emb]

lemma emb_exs' {n : ℕ} (p : Semisentence ℒₛₑₜ (n + 1)) :
    (Rewriting.emb (Semiformula.exs p) : Semiproposition ℒₛₑₜ n) =
      Semiformula.exs (Rewriting.emb p) := by
  change (Rewriting.emb (∃¹ p) : Semiproposition ℒₛₑₜ n) = ∃¹ (Rewriting.emb p)
  simp [Rewriting.emb]

/-- Vacuity of translations of formulas without free variables, with conditions only on the
labels the translation uses. -/
theorem vac_trX : ∀ {n : ℕ} (φ : Semisentence ℒₛₑₜ n) (e d z : V), NotRes z → z ≠ 0 →
    (∀ i : Fin n, e.[((i : ℕ) : V)] ≠ z) → (∀ l, BL f d (Rewriting.emb φ) l → l ≠ z) →
    L.Vac z (trX m f e d (Rewriting.emb φ)).1 ∧ L.Vac z (trX m f e d (Rewriting.emb φ)).2
  | _, .verum, _, _, _, _, hz0, _, _ => by
    show L.Vac _ (trX m f _ _ .verum).1 ∧ L.Vac _ (trX m f _ _ .verum).2
    exact ⟨vac_neg (vac_bot hz0), vac_neg (vac_neg (vac_bot hz0))⟩
  | _, .falsum, _, _, _, _, hz0, _, _ => by
    show L.Vac _ (trX m f _ _ .falsum).1 ∧ L.Vac _ (trX m f _ _ .falsum).2
    exact ⟨vac_neg (vac_neg (vac_bot hz0)), vac_neg (vac_bot hz0)⟩
  | _, .rel R v, e, d, z, hz, _, he, _ => by
    have hA : L.Vac z (atomX e m R (Rew.emb ∘ v)) := vac_atomX m R _ hz fun i => by
      rcases h : v i with j | j | ⟨g, _⟩
      · simpa [tlab, h] using he j
      · exact j.elim
      · exact nomatch g
    show L.Vac _ (trX m f _ _ (.rel R (Rew.emb ∘ v))).1 ∧ L.Vac _ (trX m f _ _ (.rel R (Rew.emb ∘ v))).2
    exact ⟨hA, vac_neg hA⟩
  | _, .nrel R v, e, d, z, hz, _, he, _ => by
    have hA : L.Vac z (atomX e m R (Rew.emb ∘ v)) := vac_atomX m R _ hz fun i => by
      rcases h : v i with j | j | ⟨g, _⟩
      · simpa [tlab, h] using he j
      · exact j.elim
      · exact nomatch g
    show L.Vac _ (trX m f _ _ (.nrel R (Rew.emb ∘ v))).1 ∧ L.Vac _ (trX m f _ _ (.nrel R (Rew.emb ∘ v))).2
    exact ⟨vac_neg hA, hA⟩
  | _, .and p q, e, d, z, hz, hz0, he, hl => by
    have h₁ := vac_trX p e d z hz hz0 he (fun l h => hl l (Or.inl h))
    have h₂ := vac_trX q e d z hz hz0 he (fun l h => hl l (Or.inr h))
    show L.Vac _ (trX m f _ _ (.and (Rewriting.emb p) (Rewriting.emb q))).1 ∧
      L.Vac _ (trX m f _ _ (.and (Rewriting.emb p) (Rewriting.emb q))).2
    exact ⟨vac_and h₁.1 h₂.1, vac_neg (vac_and h₁.1 h₂.1)⟩
  | _, .or p q, e, d, z, hz, hz0, he, hl => by
    have h₁ := vac_trX p e d z hz hz0 he (fun l h => hl l (Or.inl h))
    have h₂ := vac_trX q e d z hz hz0 he (fun l h => hl l (Or.inr h))
    show L.Vac _ (trX m f _ _ (.or (Rewriting.emb p) (Rewriting.emb q))).1 ∧
      L.Vac _ (trX m f _ _ (.or (Rewriting.emb p) (Rewriting.emb q))).2
    exact ⟨vac_neg (vac_and h₁.2 h₂.2), vac_and h₁.2 h₂.2⟩
  | _, .all p, e, d, z, hz, hz0, he, hl => by
    rw [emb_all'] at hl ⊢
    have hx : xlab f d ≠ z := hl _ (Or.inl rfl)
    have h := vac_trX p (xlab f d ∷ e) (d + 1) z hz hz0
      (fun i => by
        cases i using Fin.cases with
        | zero => simpa using hx
        | succ i => simpa using he i)
      (fun l h => hl l (Or.inr h))
    simp only [trX]
    exact ⟨vac_all _ h.1, vac_neg (vac_all _ h.1)⟩
  | _, .exs p, e, d, z, hz, hz0, he, hl => by
    rw [emb_exs'] at hl ⊢
    have hx : xlab f d ≠ z := hl _ (Or.inl rfl)
    have h := vac_trX p (xlab f d ∷ e) (d + 1) z hz hz0
      (fun i => by
        cases i using Fin.cases with
        | zero => simpa using hx
        | succ i => simpa using he i)
      (fun l h => hl l (Or.inr h))
    simp only [trX]
    exact ⟨vac_neg (vac_all _ h.2), vac_all _ h.2⟩

end

end ZF209.Halting
