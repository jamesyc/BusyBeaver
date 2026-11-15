module
public import Halting.GateC
public import Independence.Theory
@[expose] public section
/-! # Models of `U` carry pointed hulls

`U` proves every gate sentence (`U_gate`), so in a model `W` of `U` every relation defined with
parameters has a pointed hull. A relation defined in the indiscernibility quotient `NQ W` is
defined in `W` by the same formula with equality replaced by indiscernibility (`elimEq`); its hull
in `W` projects to a hull in `NQ W`. -/
namespace ZF209.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory FFL.Entailment
open ZF209.GateModel

instance eq_weaker_U : (𝗘𝗤 ℒₛₑₜ : Theory ℒₛₑₜ) ⪯ theoryU :=
  WeakerThan.ofAxm! fun {_} hσ => U_proves_eq hσ

/-- `U` proves the gate sentences. -/
theorem U_gate (k : ℕ) (φ : Semisentence ℒₛₑₜ (k + 2)) : theoryU ⊢ gateSent k φ :=
  U_of_cprov (gate_D (V := ℕ) k φ)

section Hull
variable {W : Type*} [SetStructure W]

lemma hull_of_semG {R : W → W → Prop} {u v : W} (h : semG R (gateGF () () ()) ![v, u]) :
    ∃ C, IsHull R u v C := by
  simp only [semG, gateGF] at h
  by_contra hne
  refine h fun C hX hY => hne ⟨C, hY, fun z hz => ?_⟩
  have hz' := hX z hz
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hz'
  obtain ⟨p, hp, hw⟩ : ∃ p, R p z ∧ ∀ b'', (∀ c', c' ∈ b'' → c' ∈ z) → ∀ a'', R b'' a'' →
      (∀ a''', R b'' a''' → a''' ∈ C → False) → False := by
    by_contra hn
    push Not at hn
    exact hz' fun p hp hw => by
      obtain ⟨b'', hb, a'', ha, hc⟩ := hn p hp
      exact hw b'' (by simpa using hb) a'' (by simpa using ha) (by simpa using hc.1)
  refine ⟨⟨p, hp⟩, fun u' hu' ⟨v', hv'⟩ => ?_⟩
  by_contra hn
  push Not at hn
  exact hw u' (fun c' hc' => hu' c' hc') v' hv' fun w hw₁ hw₂ => hn w hw₂ hw₁

variable [Nonempty W] [W↓[ℒₛₑₜ] ⊧* theoryU]

/-- In a model of `U`, relations defined with parameters have pointed hulls. -/
lemma hull_of_U (k : ℕ) (φ : Semisentence ℒₛₑₜ (k + 2)) (ps : Fin k → W) (u v : W) :
    ∃ C, IsHull (fun D H => φ.Eval (D :> H :> ps) Empty.elim) u v C := by
  have h := models_of_provable (inferInstance : W↓[ℒₛₑₜ] ⊧* theoryU) (U_gate k φ)
  simp only [models_iff, gateSent, Semiformula.eval_allClosure] at h
  refine hull_of_semG ((eval_toFound k φ ps (gateGF () () ()) (v :> u :> ps) ![v, u] ?_ ?_).mp
    (h _))
  · intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => rw [Subsingleton.elim i 0]; rfl
  · intro l
    rw [show (⟨2 + l, by omega⟩ : Fin (k + 2)) = (⟨l, l.2⟩ : Fin k).succ.succ from
      Fin.ext (by simp; omega)]
    simp

end Hull

/-! ## Eliminating equality -/

/-- Indiscernibility of two terms. -/
def indiscF {n : ℕ} (t u : Semiterm ℒₛₑₜ Empty n) : Semisentence ℒₛₑₜ n :=
  (∀¹ ((Semiformula.rel Language.Set.Rel.mem ![#0, Rew.bShift t]) 🡘
      (Semiformula.rel Language.Set.Rel.mem ![#0, Rew.bShift u]))) ⋏
    (∀¹ ((Semiformula.rel Language.Set.Rel.mem ![Rew.bShift t, #0]) 🡘
      (Semiformula.rel Language.Set.Rel.mem ![Rew.bShift u, #0])))

/-- Replace equality atoms by indiscernibility. -/
def elimEq : {n : ℕ} → Semisentence ℒₛₑₜ n → Semisentence ℒₛₑₜ n
  | _, .verum => .verum
  | _, .falsum => .falsum
  | _, @Semiformula.rel _ _ _ k R v =>
    match k, R, v with
    | 2, .eq, v => indiscF (v 0) (v 1)
    | 2, .mem, v => .rel .mem v
  | _, @Semiformula.nrel _ _ _ k R v =>
    match k, R, v with
    | 2, .eq, v => ∼indiscF (v 0) (v 1)
    | 2, .mem, v => .nrel .mem v
  | _, .and p q => .and (elimEq p) (elimEq q)
  | _, .or p q => .or (elimEq p) (elimEq q)
  | _, .all p => .all (elimEq p)
  | _, .exs p => .exs (elimEq p)

section Elim
variable {W : Type*} [SetStructure W]

local notation "NQW" => NQ (fun x y : W => x ∈ y)
local notation "clsW" => cls (fun x y : W => x ∈ y)

lemma val_cls {n : ℕ} (b : Fin n → W) (t : Semiterm ℒₛₑₜ Empty n) :
    (t.val (clsW ∘ b) Empty.elim : NQW) = clsW (t.val b Empty.elim) := by
  rcases t with i | x | ⟨g, _⟩
  · simp
  · exact x.elim
  · exact nomatch g

lemma rel_mem_iff (v : Fin 2 → W) :
    Tarski.Structure.rel (L := ℒₛₑₜ) (M := W) Language.Set.Rel.mem v ↔ v 0 ∈ v 1 := Iff.rfl

lemma eval_indiscF {n : ℕ} (b : Fin n → W) (t u : Semiterm ℒₛₑₜ Empty n) :
    (indiscF t u).Eval b Empty.elim ↔
      Indisc (fun x y : W => x ∈ y) (t.val b Empty.elim) (u.val b Empty.elim) := by
  simp only [indiscF, LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq,
    Semiformula.eval_all, LogicalConnective.HomClass.map_iff, LogicalConnective.Prop.iff_eq,
    Semiformula.eval_rel]
  simp only [Indisc, Function.comp_def, rel_mem_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Semiterm.val_bShift, Semiterm.val_bvar, Matrix.cons_val_zero]
  exact ⟨fun h z => ⟨h.1 z, h.2 z⟩, fun h => ⟨fun z => (h z).1, fun z => (h z).2⟩⟩

lemma cls_comp_cons {n : ℕ} (x : W) (b : Fin n → W) : clsW ∘ (x :> b) = (clsW x :> clsW ∘ b) := by
  funext i; cases i using Fin.cases <;> simp

/-- Eliminating equality reads a formula of the quotient in the structure itself. -/
theorem eval_elimEq : ∀ {n : ℕ} (φ : Semisentence ℒₛₑₜ n) (b : Fin n → W),
    (elimEq φ).Eval b Empty.elim ↔ (φ.Eval (clsW ∘ b) Empty.elim : Prop)
  | _, .verum, _ => Iff.rfl
  | _, .falsum, _ => Iff.rfl
  | _, @Semiformula.rel _ _ _ k R v, b => by
    match k, R, v with
    | 2, .eq, v =>
      show (indiscF (v 0) (v 1)).Eval b Empty.elim ↔
        ((v 0).val (clsW ∘ b) Empty.elim = (v 1).val (clsW ∘ b) Empty.elim)
      rw [eval_indiscF, val_cls, val_cls, cls_eq]
    | 2, .mem, v =>
      show (v 0).val b Empty.elim ∈ (v 1).val b Empty.elim ↔
        ((v 0).val (clsW ∘ b) Empty.elim ∈ (v 1).val (clsW ∘ b) Empty.elim)
      rw [val_cls, val_cls]; rfl
  | _, @Semiformula.nrel _ _ _ k R v, b => by
    match k, R, v with
    | 2, .eq, v =>
      show (Semiformula.Eval b Empty.elim) (∼indiscF (v 0) (v 1)) ↔
        ¬((v 0).val (clsW ∘ b) Empty.elim = (v 1).val (clsW ∘ b) Empty.elim)
      simp only [LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
      rw [eval_indiscF, val_cls, val_cls, cls_eq]
    | 2, .mem, v =>
      show ¬(v 0).val b Empty.elim ∈ (v 1).val b Empty.elim ↔
        ¬((v 0).val (clsW ∘ b) Empty.elim ∈ (v 1).val (clsW ∘ b) Empty.elim)
      rw [val_cls, val_cls]; rfl
  | _, .and p q, b => by
    show (elimEq p).Eval b Empty.elim ∧ (elimEq q).Eval b Empty.elim ↔
      (p.Eval (clsW ∘ b) Empty.elim ∧ q.Eval (clsW ∘ b) Empty.elim)
    rw [eval_elimEq p b, eval_elimEq q b]
  | _, .or p q, b => by
    show (elimEq p).Eval b Empty.elim ∨ (elimEq q).Eval b Empty.elim ↔
      (p.Eval (clsW ∘ b) Empty.elim ∨ q.Eval (clsW ∘ b) Empty.elim)
    rw [eval_elimEq p b, eval_elimEq q b]
  | _, .all p, b => by
    show (∀ x, (elimEq p).Eval (x :> b) Empty.elim) ↔ ∀ X, p.Eval (X :> clsW ∘ b) Empty.elim
    constructor
    · intro h X
      obtain ⟨x, rfl⟩ := cls_surj _ X
      rw [← cls_comp_cons]; exact (eval_elimEq p _).mp (h x)
    · intro h x
      exact (eval_elimEq p _).mpr (by rw [cls_comp_cons]; exact h _)
  | _, .exs p, b => by
    show (∃ x, (elimEq p).Eval (x :> b) Empty.elim) ↔ ∃ X, p.Eval (X :> clsW ∘ b) Empty.elim
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨clsW x, by rw [← cls_comp_cons]; exact (eval_elimEq p _).mp hx⟩
    · rintro ⟨X, hX⟩
      obtain ⟨x, rfl⟩ := cls_surj _ X
      exact ⟨x, (eval_elimEq p _).mpr (by rw [cls_comp_cons]; exact hX)⟩

end Elim

/-! ## Parameters as bound variables -/

/-- Read free variables below `K` as the bound variables after the two arguments. -/
def bindParams (K : ℕ) : Rew ℒₛₑₜ ℕ 2 Empty (K + 2) :=
  Rew.bind (fun i => #(Fin.castLE (by omega) i))
    (fun x => if h : x < K then #⟨x + 2, by omega⟩ else #0)

lemma eval_bindParams {M : Type*} [SetStructure M] {K : ℕ} (ψ : Semiformula ℒₛₑₜ ℕ 2)
    (f : ℕ → M) (hK : ∀ x, ψ.FVar? x → x < K) (D H : M) :
    (bindParams K ▹ ψ).Eval (D :> H :> fun l : Fin K => f l) Empty.elim ↔ ψ.Eval ![D, H] f := by
  rw [Semiformula.eval_rew]
  have e1 : (Semiterm.val (L := ℒₛₑₜ) (D :> H :> fun l : Fin K => f l) Empty.elim ∘
      ⇑(bindParams K) ∘ Semiterm.bvar) = ![D, H] := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => rw [Subsingleton.elim i 0]; rfl
  rw [e1]
  refine Semiformula.eval_iff_of_funEqOn ψ fun x hx => ?_
  have hx' := hK x hx
  simp only [Function.comp_apply, bindParams, Rew.bind_fvar, hx', dite_true, Semiterm.val_bvar]
  rw [show (⟨x + 2, by omega⟩ : Fin (K + 2)) = (⟨x, hx'⟩ : Fin K).succ.succ from
    Fin.ext (by simp)]
  simp

/-! ## Hulls in the quotient -/

/-- Models of `U` carry pointed hulls on their indiscernibility quotient. -/
theorem gateHull_of_U {W : Type} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* theoryU] :
    GateHull (NQ (fun x y : W => x ∈ y)) := by
  classical
  refine ⟨fun R hR u₀ v₀ => ?_⟩
  have : Inhabited (NQ (fun x y : W => x ∈ y)) := ⟨cls _ (Classical.arbitrary W)⟩
  obtain ⟨φ, hφ⟩ := hR.definable
  let ψ := Rew.rewriteMap φ.idxOfFVar ▹ φ
  let f := φ.enumerateFVar
  have hψ : ∀ v, ψ.Eval v f ↔ R (v 0) (v 1) := fun v => by
    rw [Semiformula.eval_rewriteMap, Semiformula.eval_enumerateFVar_idxOfFVar_eq_id]
    exact hφ v
  let K := ψ.fvSup
  let φ' : Semisentence ℒₛₑₜ (K + 2) := bindParams K ▹ ψ
  have hφ' : ∀ D H, φ'.Eval (D :> H :> fun l : Fin K => f l) Empty.elim ↔ R D H := fun D H => by
    rw [eval_bindParams ψ f (fun x hx => Semiformula.lt_fvSup_of_fvar? hx), hψ]; rfl
  let ps : Fin K → W := fun l => (cls_surj _ (f l)).choose
  have hps : (cls (fun x y : W => x ∈ y)) ∘ ps = fun l : Fin K => f l :=
    funext fun l => (cls_surj _ (f l)).choose_spec
  have hRW : ∀ D H : W, (elimEq φ').Eval (D :> H :> ps) Empty.elim ↔
      R (cls _ D) (cls _ H) := fun D H => by
    rw [eval_elimEq, cls_comp_cons, cls_comp_cons, hps, hφ']
  obtain ⟨u, rfl⟩ := cls_surj _ u₀
  obtain ⟨v, rfl⟩ := cls_surj _ v₀
  obtain ⟨C, hC₁, hC₂⟩ := hull_of_U K (elimEq φ') ps u v
  refine ⟨cls _ C, fun h => ?_, fun Z hZ => ?_⟩
  · exact hC₁ ((hRW u v).mpr h)
  obtain ⟨z, rfl⟩ := cls_surj _ Z
  obtain ⟨⟨p, hp⟩, hcov⟩ := hC₂ z hZ
  refine ⟨⟨cls _ p, (hRW p z).mp hp⟩, fun U hU ⟨V', hUV⟩ => ?_⟩
  obtain ⟨u', rfl⟩ := cls_surj _ U
  obtain ⟨v', rfl⟩ := cls_surj _ V'
  obtain ⟨w, hw, hwR⟩ := hcov u' (fun w hw => hU (cls _ w) hw) ⟨v', (hRW u' v').mpr hUV⟩
  exact ⟨cls _ w, hw, (hRW u' w).mp hwR⟩

/-- Models of `U` have an object with no members. -/
lemma empty_of_U {W : Type} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* theoryU] :
    ∃ e : W, ∀ y, y ∉ e := by
  have := gateHull_of_U (W := W)
  obtain ⟨E, hE⟩ := exists_isEmpty (V := NQ (fun x y : W => x ∈ y))
  obtain ⟨e, rfl⟩ := cls_surj _ E
  exact ⟨e, fun y hy => hE (cls _ y) hy⟩

end ZF209.Halting
