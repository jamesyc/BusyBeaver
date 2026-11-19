module
public import Halting.GateAlpha
public import Halting.GateChi
@[expose] public section
/-! # Gate-shaped formulas as set-theory formulas

For a relation `φ` with `k` parameters (`#0`, `#1` its arguments, `#(l+2)` parameter `l`),
`toFound k φ p` reads a gate-shaped formula `p : GF α n` as a formula with `k + n` bound
variables: the `n` variables of `p` innermost, the parameters outside them.

* `trX_toFound`: the translation of `toFound k φ p`, at depth `t` with the labels `xlab 0 t'` of
  the translation's own binders, is C-equivalent to the code of `p` with those labels, provided the
  translation of `φ` at the relevant labels is equivalent to the relation code `Rf`.
* `eval_toFound`: its meaning in a structure is the evident reading of `p`. -/
namespace ZF207.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ZF207.Internal ZF207.Internal.Tait ZF207.CKernel.Generic

namespace GF
variable {α : Type} (k : ℕ)

/-- Where the arguments and parameters of a relation instance `rel i j` live. -/
def relIdx {n : ℕ} (i j : Fin n) : Fin (k + 2) → Fin (k + n) :=
  Fin.cases (Fin.castLE (by omega) i) (Fin.cases (Fin.castLE (by omega) j)
    fun l => ⟨n + l, by omega⟩)

variable (φ : Semisentence ℒₛₑₜ (k + 2))

/-- The set-theory formula of a gate-shaped formula. -/
def toFound : {n : ℕ} → GF α n → Semisentence ℒₛₑₜ (k + n)
  | _, mem i j => Semiformula.rel Language.Set.Rel.mem
      ![#(Fin.castLE (by omega) i), #(Fin.castLE (by omega) j)]
  | _, rel i j => φ ⇜ fun l => #(relIdx k i j l)
  | _, bot => ⊥
  | _, imp p q => toFound p 🡒 toFound q
  | _, all _ p => ∀¹ (toFound p)

lemma canon_shift {β : Type} (κ : ℕ → β) (s : ℕ) : ∀ {n : ℕ} (p : GF α n) (d : ℕ),
    canon (fun d => κ (s + d)) p d = canon κ p (s + d)
  | _, mem _ _, _ => rfl
  | _, rel _ _, _ => rfl
  | _, bot, _ => rfl
  | _, imp p q, d => by simp only [canon, canon_shift κ s p d, canon_shift κ s q d]
  | _, all _ p, d => by simp only [canon, canon_shift κ s p (d + 1)]; rfl

end GF

section
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The labels of the outermost `j` binders of a translated sentence, innermost first. -/
noncomputable def PL : ℕ → V
  | 0 => 0
  | j + 1 => xlab 0 (j : V) ∷ PL j

end

section
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma PL_nth : ∀ (j l : ℕ), l < j → (PL j : V).[(l : V)] = xlab 0 ((j - 1 - l : ℕ) : V)
  | 0, _, h => absurd h (by omega)
  | j + 1, 0, _ => by simp [PL]
  | j + 1, l + 1, h => by
    have := PL_nth j l (by omega)
    simp only [PL, Nat.cast_add, Nat.cast_one, nth_adjoin_succ, this]
    congr 2; omega

lemma len_PL : ∀ j : ℕ, len (PL j : V) = j
  | 0 => by simp [PL]
  | j + 1 => by simp [PL, len_PL j]

variable {L : IntLogic V}
open IntLogic

lemma iff_symm' {A B : V} (h : L.Pr (ciff A B)) : L.Pr (ciff B A) := by
  rw [pr_iff] at *
  simpa using (Logic.Ctx.iffSymm (S := L.S.toLogic) (Γ := []) (.thm (by simpa using h))).empty

lemma dneg_iff' (a : V) : L.Pr (ciff (cneg (cneg a)) a) := by
  rw [pr_iff]
  have c : L.S.toLogic.Ctx [] (L.S.iff (L.S.neg (L.S.neg a)) a) :=
    Logic.Ctx.iffIntro Logic.Ctx.head.dne
      (Logic.Ctx.deduction (Logic.Ctx.mp (Logic.Ctx.head.up _) Logic.Ctx.head))
  simpa using c.empty

lemma imp_shape {A A' B B' B₂ : V} (hA : L.Pr (ciff A A')) (hB : L.Pr (ciff B B'))
    (h₂ : L.Pr (ciff B₂ (cneg B))) : L.Pr (ciff (cneg (cand A B₂)) (imp A' B')) := by
  rw [pr_iff] at *
  have hA' : L.S.toLogic.Ctx [] (L.S.iff A A') := .thm (by simpa using hA)
  have hB' : L.S.toLogic.Ctx [] (L.S.iff B B') := .thm (by simpa using hB)
  have h₂' : L.S.toLogic.Ctx [] (L.S.iff B₂ (L.S.neg B)) := .thm (by simpa using h₂)
  -- `¬(A ∧ B₂)` is `¬¬(A → ¬B₂)`
  have e1 : L.S.toLogic.Ctx [] (L.S.iff (L.S.neg (L.S.and A B₂)) (L.S.imp A (L.S.neg B₂))) :=
    Logic.Ctx.iffIntro Logic.Ctx.head.dne
      (Logic.Ctx.deduction (Logic.Ctx.mp (Logic.Ctx.head.up _) Logic.Ctx.head))
  have hnb : L.S.toLogic.Ctx [] (L.S.iff (L.S.neg B₂) B) := by
    have e : L.S.toLogic.Ctx [] (L.S.iff (L.S.neg B₂) (L.S.neg (L.S.neg B))) := Logic.Ctx.negCongr h₂'
    refine Logic.Ctx.iffTrans e (Logic.Ctx.iffIntro Logic.Ctx.head.dne ?_)
    exact Logic.Ctx.deduction (Logic.Ctx.mp (Logic.Ctx.head.up _) Logic.Ctx.head)
  have e2 := Logic.Ctx.impCongr hA' (Logic.Ctx.iffTrans hnb hB')
  simpa using (Logic.Ctx.iffTrans e1 e2).empty

lemma emb_imp' {n : ℕ} (p q : Semisentence ℒₛₑₜ n) :
    (Rewriting.emb (p 🡒 q) : Semiproposition ℒₛₑₜ n) =
      Semiformula.or (∼(Rewriting.emb p)) (Rewriting.emb q) := by
  simp [Semiformula.imp_eq]; rfl

lemma emb_bot' {n : ℕ} :
    (Rewriting.emb (⊥ : Semisentence ℒₛₑₜ n) : Semiproposition ℒₛₑₜ n) = Semiformula.falsum := by
  simp; rfl

variable (k : ℕ) (φ : Semisentence ℒₛₑₜ (k + 2)) (Rf : V → V → V)

/-- The translation of a gate-shaped formula is its code with the translation's labels. -/
theorem trX_toFound {α : Type} (T₀ : ℕ) (Ok : V → ℕ → Prop)
    (hstep : ∀ x t, Ok x t → Ok x (t + 1))
    (hnew : ∀ t : ℕ, T₀ ≤ t → Ok (xlab 0 (t : V)) (t + 1))
    (hRf : ∀ d h (t : ℕ), T₀ ≤ t → Ok d t → Ok h t →
      L.Pr (ciff (trX 0 0 (d ∷ h ∷ PL k) (t : V) (Rewriting.emb φ)).1 (Rf d h))) :
    ∀ {n : ℕ} (p : GF α n) (ρ : Fin n → V) (e : V) (t : ℕ), T₀ ≤ t →
    (∀ i : Fin n, e.[((i : ℕ) : V)] = ρ i) →
    (∀ l : Fin k, e.[((n + l : ℕ) : V)] = (PL k : V).[((l : ℕ) : V)]) → (∀ i, Ok (ρ i) t) →
    L.Pr (ciff (trX 0 0 e (t : V) (Rewriting.emb (GF.toFound k φ p))).1
      (enc (atomL 1) Rf (GF.canon (fun t => xlab 0 (t : V)) p t) ρ))
  | _, .mem i j, ρ, e, t, _, he, _, _ => by
    have hv : (Rewriting.emb (GF.toFound k φ (.mem i j : GF α _)) : Semiproposition ℒₛₑₜ _) =
        Semiformula.rel Language.Set.Rel.mem
          ![#(Fin.castLE (by omega) i), #(Fin.castLE (by omega) j)] := by
      simp [GF.toFound, Rewriting.emb]
    rw [hv]
    simp only [trX, atomX, tlab, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.val_castLE, he]
    exact iff_refl' _
  | _, .rel i j, ρ, e, t, ht, he, hp, hok => by
    have hv : (Rewriting.emb (GF.toFound k φ (.rel i j : GF α _)) : Semiproposition ℒₛₑₜ _) =
        Rew.subst (fun l => #(GF.relIdx k i j l)) ▹ (Rewriting.emb φ : Semiproposition ℒₛₑₜ _) := by
      simp only [GF.toFound]
      rw [Rewriting.emb_subst_eq_subst_emb]; rfl
    rw [hv, trX_rew 0 0 (Rewriting.emb φ) _ (GF.relIdx k i j) (fun l => by simp) (fun l => by simp)
      e (ρ i ∷ ρ j ∷ PL k) t (fun l => by
        cases l using Fin.cases with
        | zero => simp [GF.relIdx, he]
        | succ l =>
          cases l using Fin.cases with
          | zero =>
            simp only [GF.relIdx, Fin.cases_succ, Fin.cases_zero, Fin.val_succ, Fin.val_zero,
              Fin.val_castLE]
            rw [show ((0 + 1 : ℕ) : V) = 0 + 1 by simp, nth_adjoin_succ, nth_adjoin_zero, he]
          | succ l =>
            have := hp l
            simp only [GF.relIdx, Fin.cases_succ, Fin.val_succ] at this ⊢
            rw [show ((l + 1 + 1 : ℕ) : V) = (l : V) + 1 + 1 by simp, nth_adjoin_succ,
              nth_adjoin_succ, this])]
    exact hRf _ _ t ht (hok i) (hok j)
  | _, .bot, ρ, e, t, _, _, _, _ => by
    rw [show (GF.toFound k φ (.bot : GF α _)) = ⊥ from rfl, emb_bot']
    simp only [trX]
    exact dneg_iff' 1
  | _, .imp p q, ρ, e, t, ht, he, hp, hok => by
    rw [show GF.toFound k φ (.imp p q) = (GF.toFound k φ p 🡒 GF.toFound k φ q) from rfl, emb_imp']
    simp only [trX, trX_neg]
    exact imp_shape (trX_toFound T₀ Ok hstep hnew hRf p ρ e t ht he hp hok)
      (trX_toFound T₀ Ok hstep hnew hRf q ρ e t ht he hp hok) (pi2_iff 0 0 e (t : V) _)
  | n, .all x p, ρ, e, t, ht, he, hp, hok => by
    rw [show GF.toFound k φ (.all x p) = Semiformula.all (n := k + n) (GF.toFound k φ p) from rfl,
      emb_all']
    simp only [trX]
    have ih := trX_toFound T₀ Ok hstep hnew hRf p (xlab 0 (t : V) :> ρ) (xlab 0 (t : V) ∷ e) (t + 1)
      (by omega)
      (fun i => by
        cases i using Fin.cases with
        | zero => simp
        | succ i => simpa using he i)
      (fun l => by
        have := hp l
        rw [show ((n + 1 + (l : ℕ) : ℕ) : V) = ((n + (l : ℕ) : ℕ) : V) + 1 by push_cast; ring,
          nth_adjoin_succ, this])
      (fun i => by
        cases i using Fin.cases with
        | zero => exact hnew t ht
        | succ i => exact hstep _ _ (hok i))
    rw [Nat.cast_succ] at ih
    exact iff_all' _ ih

end

/-! ## Meaning -/

section Sem
variable {W : Type*} [SetStructure W]

lemma cons_castLE_zero {β : Type*} {m n : ℕ} (x : β) (b : Fin (m + n) → β) (h : n + 1 ≤ m + (n + 1)) :
    (x :> b) (Fin.castLE h 0) = x := by
  rw [show (Fin.castLE h 0 : Fin (m + n + 1)) = 0 from Fin.ext rfl]; simp

lemma cons_castLE_succ {β : Type*} {m n : ℕ} (x : β) (b : Fin (m + n) → β) (i : Fin n)
    (h : n + 1 ≤ m + (n + 1)) :
    (x :> b) (Fin.castLE h i.succ) = b (Fin.castLE (by omega) i) := by
  rw [show (Fin.castLE h i.succ : Fin (m + n + 1)) = (Fin.castLE (by omega) i).succ from
    Fin.ext (by simp)]
  simp

lemma cons_param {β : Type*} {m n : ℕ} (x : β) (b : Fin (m + n) → β) (l : Fin m)
    (h : n + 1 + l < m + (n + 1)) :
    (x :> b) ⟨n + 1 + l, h⟩ = b ⟨n + l, by omega⟩ := by
  rw [show (⟨n + 1 + l, h⟩ : Fin (m + n + 1)) = (⟨n + l, by omega⟩ : Fin (m + n)).succ from
    Fin.ext (by simp; omega)]
  simp

/-- The meaning of a gate-shaped formula for a relation `R`. -/
def semG {α : Type} (R : W → W → Prop) : {n : ℕ} → GF α n → (Fin n → W) → Prop
  | _, .mem i j, v => v i ∈ v j
  | _, .rel i j, v => R (v i) (v j)
  | _, .bot, _ => False
  | _, .imp p q, v => semG R p v → semG R q v
  | _, .all _ p, v => ∀ x, semG R p (x :> v)

theorem eval_toFound {α : Type} (k : ℕ) (φ : Semisentence ℒₛₑₜ (k + 2)) (ps : Fin k → W) :
    ∀ {n : ℕ} (p : GF α n) (b : Fin (k + n) → W) (v : Fin n → W),
    (∀ i, b (Fin.castLE (by omega) i) = v i) → (∀ l : Fin k, b ⟨n + l, by omega⟩ = ps l) →
    ((GF.toFound k φ p).Eval b Empty.elim ↔
      semG (fun D H => φ.Eval (D :> H :> ps) Empty.elim) p v)
  | _, .mem i j, b, v, hb, _ => by
    simp [GF.toFound, semG, Semiformula.eval_rel, hb]; rfl
  | _, .rel i j, b, v, hb, hp => by
    simp only [GF.toFound, semG, Semiformula.eval_substs]
    have e : (Semiterm.val (L := ℒₛₑₜ) b Empty.elim ∘ fun l => #(GF.relIdx k i j l)) = (v i :> v j :> ps) := by
      funext l
      cases l using Fin.cases with
      | zero => simp [GF.relIdx, hb]
      | succ l =>
        cases l using Fin.cases with
        | zero =>
          simp only [Function.comp, GF.relIdx, Fin.cases_succ, Fin.cases_zero, Semiterm.val_bvar, hb,
            Matrix.cons_val_succ, Matrix.cons_val_zero]
        | succ l => simp [GF.relIdx, hp]
    rw [e]
  | _, .bot, _, _, _, _ => by simp [GF.toFound, semG]
  | _, .imp p q, b, v, hb, hp => by
    simp only [GF.toFound, semG, LogicalConnective.HomClass.map_imply,
      LogicalConnective.Prop.arrow_eq, eval_toFound k φ ps p b v hb hp,
      eval_toFound k φ ps q b v hb hp]
  | _, .all _ p, b, v, hb, hp => by
    simp only [GF.toFound, semG, Semiformula.eval_all]
    refine forall_congr' fun x => eval_toFound k φ ps p (x :> b) (x :> v) ?_ ?_
    · intro i; cases i using Fin.cases with
      | zero => rw [cons_castLE_zero]; simp
      | succ i => rw [cons_castLE_succ]; simp [hb]
    · intro l; rw [cons_param]; exact hp l

end Sem

end ZF207.Halting
