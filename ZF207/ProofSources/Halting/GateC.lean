module
public import Halting.GateAtom
public import Halting.GateFound
@[expose] public section
/-! # C proves the translated gate sentences

For a relation `φ` with `k` parameters, `gateSent k φ` says: for all parameters and all `b`, `a`,
not every `C` fails the hull property of `φ` started at `(b, a)`. Its translation is a C-theorem:

1. the machine's gate with labels `a = xlab 0 (k+1)`, `b = xlab 0 k` and relation code
   `c = gRf b a` gives the gate-shaped formula `gateGF a b c` with raw membership;
2. `alpha` renames its binders to the translation's labels and replaces raw membership by
   membership up to `≈`;
3. `trX_toFound` identifies the result with the translation of `gateSent k φ`.

The relation code is the translation of `φ` in a separate label family, padded with a closed
theorem whose binders include every label the gate must avoid, so that the code exceeds them. -/
namespace ZF207.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ZF207.Internal ZF207.Internal.Tait ZF207.CKernel.Generic

/-- The machine's gate `¬∀c gateBody(c, b, a)`; variable `0` is `a`, variable `1` is `b`. -/
def gateGF {α : Type} (a b c : α) : GF α 2 :=
  .imp (.all c (.imp
    (.all a (.imp (.mem 0 1) (.imp
      (.all b (.imp (.rel 0 1) (.imp
        (.all b (.imp
          (.all c (.imp (.mem 0 1) (.mem 0 3)))
          (.all a (.imp (.rel 1 0) (.imp
            (.all a (.imp (.rel 2 0) (.imp (.mem 0 5) .bot)))
            .bot)))))
        .bot)))
      .bot)))
    (.imp (.imp (.rel 2 1) (.mem 1 0)) .bot))) .bot

lemma gateGF_depth {α : Type} (a b c : α) : (gateGF a b c).depth = 6 := rfl

/-- The gate sentence of a relation with `k` parameters. -/
def gateSent (k : ℕ) (φ : Semisentence ℒₛₑₜ (k + 2)) : Sentence ℒₛₑₜ :=
  ∀¹* GF.toFound k φ (gateGF () () ())

section
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma lt_numeral : ∀ (N : ℕ) (i : V), i < (N : V) → ∃ l < N, i = (l : V)
  | 0, i, h => absurd h (by simp)
  | N + 1, i, h => by
    rw [Nat.cast_succ, lt_succ_iff_le] at h
    rcases lt_or_eq_of_le h with h | rfl
    · obtain ⟨l, hl, rfl⟩ := lt_numeral N i h
      exact ⟨l, by omega, rfl⟩
    · exact ⟨N, by omega, rfl⟩

lemma BL_xlab {f : V} : ∀ {n : ℕ} (d : V) (ψ : Semiproposition ℒₛₑₜ n) (l : V), BL f d ψ l →
    ∃ d', l = xlab f d'
  | _, d, .and p q, l, h => h.elim (BL_xlab d p l) (BL_xlab d q l)
  | _, d, .or p q, l, h => h.elim (BL_xlab d p l) (BL_xlab d q l)
  | _, d, .all p, l, h => h.elim (fun h => ⟨d, h⟩) (BL_xlab _ p l)
  | _, d, .exs p, l, h => h.elim (fun h => ⟨d, h⟩) (BL_xlab _ p l)
  | _, _, .verum, _, h => h.elim
  | _, _, .falsum, _, h => h.elim
  | _, _, .rel _ _, _, h => h.elim
  | _, _, .nrel _ _, _, h => h.elim

/-! ## The padding -/

/-- A closed theorem whose binders are the reserved labels and `xlab 0 j` for `j < N`. -/
noncomputable def padCode : ℕ → V
  | 0 => all (rlab 0) (all (rlab 1) (all (rlab 2) (imp 1 1)))
  | j + 1 => all (xlab 0 (j : V)) (padCode j)

lemma pad_prov : ∀ N, (KL (V := V)).S.Prov (padCode N : V)
  | 0 => by
    have h := (KL (V := V)).S.toLogic.identity (1 : V)
    simpa [padCode] using (KL (V := V)).S.gen _ ((KL (V := V)).S.gen _ ((KL (V := V)).S.gen _
      (by simpa using h)))
  | N + 1 => by simpa [padCode] using (KL (V := V)).S.gen _ (pad_prov N)

lemma pad_vac {z : V} (hz : z ≠ 0) : ∀ N, (KL (V := V)).Vac z (padCode N : V)
  | 0 => IntLogic.vac_all _ (IntLogic.vac_all _ (IntLogic.vac_all _
      (IntLogic.vac_imp (IntLogic.vac_bot hz) (IntLogic.vac_bot hz))))
  | N + 1 => IntLogic.vac_all _ (pad_vac hz N)

lemma rlab_lt_pad (i : V) (hi : i = 0 ∨ i = 1 ∨ i = 2) : ∀ N, rlab i < (padCode N : V)
  | 0 => by
    rcases hi with rfl | rfl | rfl
    · exact lt_all_label _ _
    · exact lt_trans (lt_all_label _ _) (lt_all_body _ _)
    · exact lt_trans (lt_all_label _ _) (lt_trans (lt_all_body _ _) (lt_all_body _ _))
  | N + 1 => lt_trans (rlab_lt_pad i hi N) (lt_all_body _ _)

lemma xlab_lt_pad (j : ℕ) : ∀ N, j < N → xlab 0 (j : V) < (padCode N : V)
  | 0, h => absurd h (by omega)
  | N + 1, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · exact lt_trans (xlab_lt_pad j N h) (lt_all_body _ _)
    · exact lt_all_label _ _

/-! ## The relation code -/

variable (k : ℕ) (φ : Semisentence ℒₛₑₜ (k + 2))

/-- The relation code: the translation of `φ` in family `1`, padded. -/
noncomputable def gRf (d h : V) : V :=
  cand (trX 0 1 (d ∷ h ∷ PL k) 0 (Rewriting.emb φ)).1 (padCode (k + 10))

/-- Labels foreign to the relation codes. -/
def gFr (z : V) : Prop :=
  z ≠ 0 ∧ (∀ l, BL 1 0 (Rewriting.emb φ : Semiproposition ℒₛₑₜ (k + 2)) l → l ≠ z) ∧
    ∀ l : Fin k, (PL k : V).[((l : ℕ) : V)] ≠ z

lemma PL_nth' (l : Fin k) : (PL k : V).[((l : ℕ) : V)] = xlab 0 ((k - 1 - l : ℕ) : V) :=
  PL_nth k l l.2

lemma notRes_PL (l : Fin k) : NotRes ((PL k : V).[((l : ℕ) : V)]) := by
  rw [PL_nth']; exact notRes_xlab _ _

lemma notRes_PL' (j : ℕ) (hj : j < k) : NotRes ((PL k : V).[(j : V)]) := by
  rw [PL_nth k j hj]; exact notRes_xlab _ _

lemma env3_val {d h : V} (i : Fin (k + 2)) :
    (d ∷ h ∷ PL k : V).[((i : ℕ) : V)] =
      if (i : ℕ) = 0 then d else if (i : ℕ) = 1 then h else (PL k : V).[(((i : ℕ) - 2 : ℕ) : V)] := by
  obtain ⟨i, hi⟩ := i
  rcases i with _ | _ | i
  · simp
  · simp
  · simp only [show i + 1 + 1 ≠ 0 by omega, show i + 1 + 1 ≠ 1 by omega, ite_false,
      show i + 1 + 1 - 2 = i by omega]
    rw [show ((i + 1 + 1 : ℕ) : V) = (i : V) + 1 + 1 by simp, nth_adjoin_succ, nth_adjoin_succ]

theorem gRelOK : RelOK (KL (V := V)) (gRf k φ) (gFr k φ) where
  sub a b d h d' h' ha hb fa fb hd hh hd' hh' h₀ h₁ := by
    refine IntLogic.sub_and (sub_trX 0 1 (Rewriting.emb φ) a b _ _ 0 ?_ ?_ ha hb ?_ ?_).1
      (IntLogic.sub_refl _ _ _)
    · intro i; rw [env3_val, env3_val]
      split_ifs
      · exact h₀
      · exact h₁
      · exact Or.inl rfl
    · exact fun l hl => ⟨fa.2.1 l hl, fb.2.1 l hl⟩
    · intro i; rw [env3_val]
      split_ifs
      · exact hd
      · exact hh
      · exact notRes_PL' k _ (by omega)
    · intro i; rw [env3_val]
      split_ifs
      · exact hd'
      · exact hh'
      · exact notRes_PL' k _ (by omega)
  vac z d h hz fz hzd hzh := by
    refine IntLogic.vac_and (vac_trX 0 1 φ _ 0 z hz fz.1 ?_ fz.2.1).1 (pad_vac fz.1 _)
    intro i; rw [env3_val]
    split_ifs
    · exact Ne.symm hzd
    · exact Ne.symm hzh
    · have := fz.2.2 ⟨(i : ℕ) - 2, by omega⟩
      simpa using this

/-- Labels allowed at depth `t` in the translation. -/
def GOk (x : V) (t : ℕ) : Prop := NotRes x ∧ Unbound x (t : V) 0 ∧ Unbound x 0 1

lemma unbound_xlab {f f' j t : V} (h : f ≠ f' ∨ j < t) : Unbound (xlab f j) t f' := by
  intro d' _ hd e
  rcases xlab_inj.mp e with ⟨rfl, rfl⟩
  rcases h with h | h
  · exact h rfl
  · exact absurd hd (not_le.mpr h)

lemma gRf_iff (d h : V) (t : ℕ) (ht : k + 2 ≤ t) (hd : GOk d t) (hh : GOk h t) :
    (KL (V := V)).Pr (ciff (trX 0 0 (d ∷ h ∷ PL k) (t : V) (Rewriting.emb φ)).1 (gRf k φ d h)) := by
  have hq := (Semiformula.quote_isSemiformula (V := V) (Rewriting.emb φ :
    Semiproposition ℒₛₑₜ (k + 2))).isUFormula
  have hlen : len (d ∷ h ∷ PL k : V) = ((k + 2 : ℕ) : V) := by simp [len_PL]; ring
  have entry : ∀ i < len (d ∷ h ∷ PL k : V), GOk ((d ∷ h ∷ PL k : V).[i]) t := by
    intro i hi
    rw [hlen] at hi
    obtain ⟨l, hl, rfl⟩ := lt_numeral _ i hi
    have := env3_val (d := d) (h := h) k ⟨l, hl⟩
    simp only at this; rw [this]
    split_ifs with h0 h1
    · exact hd
    · exact hh
    · rw [PL_nth k _ (by omega)]
      refine ⟨notRes_xlab _ _, unbound_xlab (Or.inr ?_), unbound_xlab (Or.inl (by simp))⟩
      exact_mod_cast (show k - 1 - (l - 2) < t by omega)
  have hA := (tr_alpha (KL (V := V)) hq (d ∷ h ∷ PL k) (t : V) 0 0 0 1 (by simp)
    (fun i hi => ⟨(entry i hi).2.1, (entry i hi).2.2⟩) (fun i hi => (entry i hi).1)).1
  rw [tr_quote, tr_quote] at hA
  simp only [pi₁_pair] at hA
  refine IntLogic.iff_trans' hA ?_
  rw [IntLogic.pr_iff]
  have c : (KL (V := V)).S.toLogic.Ctx [] ((KL (V := V)).S.iff
      (trX 0 1 (d ∷ h ∷ PL k) 0 (Rewriting.emb φ)).1
      ((KL (V := V)).S.and (trX 0 1 (d ∷ h ∷ PL k) 0 (Rewriting.emb φ)).1 (padCode (k + 10)))) :=
    Logic.Ctx.iffIntro (Logic.Ctx.andIntro Logic.Ctx.head (.thm (pad_prov _)))
      Logic.Ctx.head.andLeft
  simpa [gRf] using c.empty

/-! ## Well-scopedness of the gate -/

lemma WS_gate {Fr : V → Prop} {κ : ℕ → V} {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (na : NotRes a) (nb : NotRes b) (nc : NotRes c) (fa : Fr a) (fb : Fr b) (fc : Fr c)
    (a0 : a ≠ 0) (b0 : b ≠ 0) (c0 : c ≠ 0) (ka : ∀ d, κ d ≠ a) (kb : ∀ d, κ d ≠ b)
    (kc : ∀ d, d < 6 → κ d ≠ c) : WS Fr κ 6 (gateGF a b c) ![a, b] 0 := by
  have hba := Ne.symm hab; have hca := Ne.symm hac; have hcb := Ne.symm hbc
  simp only [WS, gateGF, GF.occ, Fin.forall_fin_succ, IsEmpty.forall_iff,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one]
  simp (config := { decide := true }) [*]
  exact ⟨fun d' _ h => kc d' h, fun d' _ h => kc d' h⟩

/-! ## The translated gate sentence -/

lemma chi_allClosure : ∀ (N : ℕ) (ψ : Semiproposition ℒₛₑₜ N),
    (KL (V := V)).S.Prov (trX 0 0 (PL N) (N : V) ψ).1 →
    (KL (V := V)).S.Prov (trX 0 0 0 0 (∀¹* ψ)).1
  | 0, ψ, h => by simpa [PL] using h
  | N + 1, ψ, h => by
    rw [allClosure_succ]
    refine chi_allClosure N _ ?_
    show (KL (V := V)).S.Prov (trX 0 0 (PL N) (N : V) (Semiformula.all ψ)).1
    simp only [trX]
    simpa using (KL (V := V)).S.gen (xlab 0 (N : V)) (by simpa [PL] using h)

lemma canon_gate {α β γ : Type} (κ : ℕ → γ) (a b c : α) (a' b' c' : β) (d : ℕ) :
    GF.canon κ (gateGF a b c) d = GF.canon κ (gateGF a' b' c') d := rfl

lemma gOk_step (x : V) (t : ℕ) (h : GOk x t) : GOk x (t + 1) :=
  ⟨h.1, by simpa using h.2.1.step, h.2.2⟩

lemma gOk_new (t : ℕ) : GOk (xlab 0 (t : V)) (t + 1) :=
  ⟨notRes_xlab _ _, unbound_xlab (Or.inr (by simp)), unbound_xlab (Or.inl (by simp))⟩

lemma gOk_xlab {j t : ℕ} (h : j < t) : GOk (xlab 0 (j : V)) t :=
  ⟨notRes_xlab _ _, unbound_xlab (Or.inr (by exact_mod_cast h)), unbound_xlab (Or.inl (by simp))⟩

lemma xlab_ne_xlab0 {i j : ℕ} (h : i ≠ j) : xlab 0 (i : V) ≠ xlab 0 (j : V) := by
  simpa using h

/-- C proves the translation of every gate sentence. -/
theorem gate_D : D.val.Evalb ![chiS (0 : V) ⌜gateSent k φ⌝] := by
  set a : V := xlab 0 ((k + 1 : ℕ) : V)
  set b : V := xlab 0 (k : V)
  set c : V := gRf k φ b a with hc
  set P : V := padCode (k + 10)
  set X : V := (trX 0 1 (b ∷ a ∷ PL k) 0 (Rewriting.emb φ)).1
  -- the relation code exceeds the padding and its own bound labels
  have hXc : imp X (cneg P) < c := lt_cneg _
  have hPc : P < c := lt_of_lt_of_le (lt_cneg P) (le_trans (right_le_imp X (cneg P)) hXc.le)
  have hBc : ∀ l, BL 1 0 (Rewriting.emb φ : Semiproposition ℒₛₑₜ (k + 2)) l → l < c := fun l hl =>
    lt_of_lt_of_le (lt_trX 0 1 _ _ _ l hl).1 (le_trans (left_le_imp X (cneg P)) hXc.le)
  have hxc : ∀ j < k + 10, xlab 0 (j : V) ≠ c := fun j hj =>
    ne_of_lt (lt_trans (xlab_lt_pad j _ hj) hPc)
  have hc0 : c ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le hPc)
  have hnc : NotRes c := ⟨fun h => absurd (h ▸ rlab_lt_pad 0 (Or.inl rfl) _) (not_lt.mpr hPc.le),
    fun h => absurd (h ▸ rlab_lt_pad 1 (Or.inr (Or.inl rfl)) _) (not_lt.mpr hPc.le),
    fun h => absurd (h ▸ rlab_lt_pad 2 (Or.inr (Or.inr rfl)) _) (not_lt.mpr hPc.le)⟩
  have hca : c ≠ a := Ne.symm (hxc (k + 1) (by omega))
  have hcb : c ≠ b := Ne.symm (hxc k (by omega))
  have hab : a ≠ b := xlab_ne_xlab0 (by omega)
  -- freshness
  have hBL : ∀ (j : ℕ) l, BL 1 0 (Rewriting.emb φ : Semiproposition ℒₛₑₜ (k + 2)) l →
      l ≠ xlab 0 (j : V) := fun j l hl => by
    obtain ⟨d', rfl⟩ := BL_xlab _ _ _ hl
    simp
  have hPL : ∀ (j : ℕ), k ≤ j → ∀ l : Fin k, (PL k : V).[((l : ℕ) : V)] ≠ xlab 0 (j : V) :=
    fun j hj l => by rw [PL_nth']; exact xlab_ne_xlab0 (by omega)
  have fxj : ∀ j : ℕ, k ≤ j → gFr k φ (xlab 0 (j : V)) := fun j hj =>
    ⟨xlab_ne_zero _ _, fun l hl => hBL j l hl, hPL j hj⟩
  have fc : gFr k φ c := ⟨hc0, fun l hl => ne_of_lt (hBc l hl), fun l => by
    rw [PL_nth']; exact hxc _ (by omega)⟩
  -- the gate, renamed
  set κ : ℕ → V := fun d => xlab 0 ((k + 2 + d : ℕ) : V)
  have hbundle : (KL (V := V)).S.Prov (enc mem (gRf k φ) (gateGF a b c) ![a, b]) :=
    (provRules (M := V)).sys.notQGate a b c hca hcb
  have hal := alpha (L := KL (V := V)) (fun x y hxy hx hy => ((KL (V := V)).pr_iff _).mpr
      (mem_iff_atomL hxy hx hy)) (gRelOK k φ) (κ := κ)
    (fun d d' h => by simpa [κ] using h)
    (fun d => ⟨notRes_xlab _ _, fxj _ (by omega), xlab_ne_zero _ _⟩) 6 (gateGF a b c) ![a, b] 0
    (by simp [gateGF_depth])
    (WS_gate hab (Ne.symm hca) (Ne.symm hcb) (notRes_xlab _ _) (notRes_xlab _ _) hnc
      (fxj _ (by omega)) (fxj _ (by omega)) fc (xlab_ne_zero _ _) (xlab_ne_zero _ _) hc0
      (fun d => xlab_ne_xlab0 (by omega)) (fun d => xlab_ne_xlab0 (by omega))
      (fun d hd => hxc _ (by omega)))
    (fun i => by
      cases i using Fin.cases with
      | zero => exact ⟨notRes_xlab _ _, fun d' _ _ => xlab_ne_xlab0 (by omega)⟩
      | succ i =>
        rw [Subsingleton.elim i 0]
        exact ⟨notRes_xlab _ _, fun d' _ _ => xlab_ne_xlab0 (by omega)⟩)
  rw [IntLogic.pr_iff] at hal
  have hcan : (KL (V := V)).S.Prov (enc (atomL 1) (gRf k φ)
      (GF.canon (fun t => xlab 0 (t : V)) (gateGF () () ()) (k + 2)) ![a, b]) := by
    have e : GF.canon κ (gateGF a b c) 0 =
        GF.canon (fun t => xlab 0 (t : V)) (gateGF () () ()) (k + 2) := by
      rw [canon_gate κ a b c () () ()]
      exact GF.canon_shift (fun t => xlab 0 (t : V)) (k + 2) (gateGF () () ()) 0
    rw [← e]
    exact Logic.Ctx.empty (Logic.Ctx.iffMp (.thm (by simpa using hal)) (.thm hbundle))
  -- the translation
  have htr := trX_toFound (L := KL (V := V)) k φ (gRf k φ) (k + 2) GOk gOk_step
    (fun t _ => gOk_new t) (fun d h t ht hd hh => gRf_iff k φ d h t ht hd hh) (gateGF () () ())
    ![a, b] (PL (k + 2)) (k + 2) le_rfl
    (fun i => by
      cases i using Fin.cases with
      | zero => simp [PL, a]
      | succ i =>
        rw [Subsingleton.elim i 0]
        simp [PL, b])
    (fun l => by
      simp only [PL]
      rw [show ((2 + (l : ℕ) : ℕ) : V) = (l : V) + 1 + 1 by push_cast; ring, nth_adjoin_succ,
        nth_adjoin_succ])
    (fun i => by
      cases i using Fin.cases with
      | zero => exact gOk_xlab (by omega)
      | succ i =>
        rw [Subsingleton.elim i 0]
        exact gOk_xlab (by omega))
  rw [IntLogic.pr_iff] at htr
  have hbody : (KL (V := V)).S.Prov
      (trX 0 0 (PL (k + 2)) ((k + 2 : ℕ) : V) (Rewriting.emb (GF.toFound k φ (gateGF () () ())))).1 :=
    Logic.Ctx.empty (Logic.Ctx.iffMpr (.thm (by simpa using htr)) (.thm hcan))
  rw [D_iff_S, chiS_quote, gateSent, Rewriting.emb_allClosure]
  exact chi_allClosure _ _ hbody

end

end ZF207.Halting
