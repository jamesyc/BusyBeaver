module
public import I3_380.Calibration.ArithmeticInterpretation.StandardSyntax
@[expose] public section
/-! # Meaning of the marker translation

If at the marker value `e` the templates read an ℒₒᵣ-structure `A` through a surjection
`pr : W → A` (the domain template is trivially true), then `Jx ι ε p` holds in `W` exactly when
`p` holds in `A` at the projected assignment (`eval_Jx`). -/
namespace PalomarI3380.Calibration.ArithmeticInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

variable (ι : PalomarI3380.Calibration.ArithmeticInterpretation.Interp)

/-- The templates at `e` read `A` through `pr`. -/
structure Reads {W A : Type*} [Tarski.Structure GraphLanguage W] [ORingStructure A] (e : W) (pr : W → A) : Prop where
  surj : Function.Surjective pr
  dom : ∀ x, W ⊧/![e, x] ι.dom
  eq : ∀ x y, W ⊧/![e, x, y] ι.eq ↔ pr x = pr y
  lt : ∀ x y, W ⊧/![e, x, y] ι.lt ↔ pr x < pr y
  zero : ∀ y, W ⊧/![e, y] ι.zero ↔ pr y = 0
  one : ∀ y, W ⊧/![e, y] ι.one ↔ pr y = 1
  add : ∀ a b y, W ⊧/![e, a, b, y] ι.add ↔ pr a + pr b = pr y
  mul : ∀ a b y, W ⊧/![e, a, b, y] ι.mul ↔ pr a * pr b = pr y

variable {ι}
variable {W A : Type*} [Tarski.Structure GraphLanguage W] [ORingStructure A] {e : W} {pr : W → A}

lemma eval_tpl {k n : ℕ} (φ : Semisentence GraphLanguage k) (w : Fin k → Semiterm GraphLanguage ℕ n)
    (b : Fin n → W) (f : ℕ → W) :
    (tpl φ w).Eval b f ↔ W ⊧/(fun i => (w i).val b f) φ := by
  simp [tpl, Semiformula.eval_substs, Semiformula.eval_emb]; rfl

lemma eval_pushV3 {n : ℕ} (c a y : W) (b : Fin n → W) (f : ℕ → W) (k : Fin (n + 3)) :
    (fun i => (pushV 3 k i).val (c :> a :> y :> b) f) = (c :> a :> y :> b) k :> b := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pushV]
  · have hj : j.addNat 3 = j.succ.succ.succ := Fin.ext (by simp)
    simp [pushV, hj]

lemma eval_pushV2 {n : ℕ} (c a : W) (b : Fin n → W) (f : ℕ → W) (k : Fin (n + 2)) :
    (fun i => (pushV 2 k i).val (c :> a :> b) f) = (c :> a :> b) k :> b := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pushV]
  · have hj : j.addNat 2 = j.succ.succ := Fin.ext (by simp)
    simp [pushV, hj]

lemma eval_pushV3' {n : ℕ} (c a y : W) (b : Fin n → W) (f : ℕ → W) (k : Fin (n + 3)) :
    (Semiterm.val (c :> a :> y :> b) f ∘ pushV 3 k) = (c :> a :> y :> b) k :> b :=
  eval_pushV3 c a y b f k

lemma eval_pushV2' {n : ℕ} (c a : W) (b : Fin n → W) (f : ℕ → W) (k : Fin (n + 2)) :
    (Semiterm.val (c :> a :> b) f ∘ pushV 2 k) = (c :> a :> b) k :> b :=
  eval_pushV2 c a b f k

theorem eval_Gx (h : Reads ι e pr) {n : ℕ} (ε : Semiterm GraphLanguage ℕ n) (t : Semiterm ℒₒᵣ ℕ n)
    (b : Fin n → W) (f : ℕ → W) (he : ε.val b f = e) (y : W) :
    (Gx ι ε t).Eval (y :> b) f ↔ pr y = t.val (pr ∘ b) (pr ∘ f) := by
  induction t generalizing y with
  | bvar z =>
    have hv : (fun i => Semiterm.val (y :> b) f (![Rew.bShift ε, #0, #z.succ] i)) = ![e, y, b z] := by
      funext i; refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ fun j => j.elim0)) i <;> simp [he]
    simp only [Gx, eval_tpl, hv, h.eq]; simp
  | fvar x =>
    have hv : (fun i => Semiterm.val (y :> b) f (![Rew.bShift ε, #0, &x] i)) = ![e, y, f x] := by
      funext i; refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ fun j => j.elim0)) i <;> simp [he]
    simp only [Gx, eval_tpl, hv, h.eq]; simp
  | func g v ih =>
    cases g with
    | zero =>
      have hv : (fun i => Semiterm.val (y :> b) f (![Rew.bShift ε, #0] i)) = ![e, y] := by
        funext i; refine Fin.cases ?_ (Fin.cases ?_ fun j => j.elim0) i <;> simp [he]
      simp only [Gx, eval_tpl, hv, h.zero]
      simp [Semiterm.val_func]; rfl
    | one =>
      have hv : (fun i => Semiterm.val (y :> b) f (![Rew.bShift ε, #0] i)) = ![e, y] := by
        funext i; refine Fin.cases ?_ (Fin.cases ?_ fun j => j.elim0) i <;> simp [he]
      simp only [Gx, eval_tpl, hv, h.one]
      simp [Semiterm.val_func]; rfl
    | add =>
      have hv : ∀ x x₁ : W, (fun i => Semiterm.val (x₁ :> x :> y :> b) f
          (![Rew.bShift (Rew.bShift (Rew.bShift ε)), #1, #0, #2] i)) = ![e, x, x₁, y] := by
        intro x x₁; funext i
        refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ fun j => j.elim0))) i <;> simp [he]
      simp only [Gx, Semiformula.eval_ex, LogicalConnective.HomClass.map_and, eval_tpl,
        Semiformula.eval_substs, eval_pushV3', hv, h.add, ih, LogicalConnective.Prop.and_eq]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
      show (∃ x x₁ : W, (pr x = _ ∧ pr x₁ = _) ∧ pr x + pr x₁ = pr y) ↔ pr y = _ + _
      constructor
      · rintro ⟨x, x₁, ⟨h₁, h₂⟩, h₃⟩; rw [← h₃, h₁, h₂]
      · intro hy
        obtain ⟨x, hx⟩ := h.surj (Semiterm.val (pr ∘ b) (pr ∘ f) (v 0))
        obtain ⟨x₁, hx₁⟩ := h.surj (Semiterm.val (pr ∘ b) (pr ∘ f) (v 1))
        exact ⟨x, x₁, ⟨hx, hx₁⟩, by rw [hx, hx₁, hy]⟩
    | mul =>
      have hv : ∀ x x₁ : W, (fun i => Semiterm.val (x₁ :> x :> y :> b) f
          (![Rew.bShift (Rew.bShift (Rew.bShift ε)), #1, #0, #2] i)) = ![e, x, x₁, y] := by
        intro x x₁; funext i
        refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ fun j => j.elim0))) i <;> simp [he]
      simp only [Gx, Semiformula.eval_ex, LogicalConnective.HomClass.map_and, eval_tpl,
        Semiformula.eval_substs, eval_pushV3', hv, h.mul, ih, LogicalConnective.Prop.and_eq]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
      show (∃ x x₁ : W, (pr x = _ ∧ pr x₁ = _) ∧ pr x * pr x₁ = pr y) ↔ pr y = _ * _
      constructor
      · rintro ⟨x, x₁, ⟨h₁, h₂⟩, h₃⟩; rw [← h₃, h₁, h₂]
      · intro hy
        obtain ⟨x, hx⟩ := h.surj (Semiterm.val (pr ∘ b) (pr ∘ f) (v 0))
        obtain ⟨x₁, hx₁⟩ := h.surj (Semiterm.val (pr ∘ b) (pr ∘ f) (v 1))
        exact ⟨x, x₁, ⟨hx, hx₁⟩, by rw [hx, hx₁, hy]⟩

lemma comp_cons_pr {n : ℕ} (x : W) (b : Fin n → W) : (pr ∘ (x :> b)) = pr x :> (pr ∘ b) := by
  funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

lemma eval_atomJx (h : Reads ι e pr) {n : ℕ} (ε : Semiterm GraphLanguage ℕ n) (r : Language.ORing.Rel 2)
    (v : Fin 2 → Semiterm ℒₒᵣ ℕ n) (b : Fin n → W) (f : ℕ → W) (he : ε.val b f = e) :
    (atomJx ι ε r (v 0) (v 1)).Eval b f ↔ (Semiformula.rel r v).Eval (pr ∘ b) (pr ∘ f) := by
  have hv : ∀ x x₁ : W, (fun i => Semiterm.val (x₁ :> x :> b) f
      (![Rew.bShift (Rew.bShift ε), #1, #0] i)) = ![e, x, x₁] := by
    intro x x₁; funext i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ fun j => j.elim0)) i <;> simp [he]
  simp only [atomJx, Semiformula.eval_ex, LogicalConnective.HomClass.map_and, eval_tpl,
    Semiformula.eval_substs, eval_pushV2', hv, eval_Gx h _ _ b f he, LogicalConnective.Prop.and_eq]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
  cases r
  · simp only [relTx, h.eq]
    rw [show (Semiformula.Eval (pr ∘ b) (pr ∘ f)) (Semiformula.rel Language.ORing.Rel.eq v) ↔
      Semiterm.val (pr ∘ b) (pr ∘ f) (v 0) = Semiterm.val (pr ∘ b) (pr ∘ f) (v 1) by
        simp [Semiformula.eval_rel]; rfl]
    constructor
    · rintro ⟨x, x₁, ⟨h₁, h₂⟩, h₃⟩; rw [← h₁, ← h₂]; exact h₃
    · intro hr
      obtain ⟨x, hx⟩ := h.surj (Semiterm.val (pr ∘ b) (pr ∘ f) (v 0))
      obtain ⟨x₁, hx₁⟩ := h.surj (Semiterm.val (pr ∘ b) (pr ∘ f) (v 1))
      exact ⟨x, x₁, ⟨hx, hx₁⟩, by rw [hx, hx₁]; exact hr⟩
  · simp only [relTx, h.lt]
    rw [show (Semiformula.Eval (pr ∘ b) (pr ∘ f)) (Semiformula.rel Language.ORing.Rel.lt v) ↔
      Semiterm.val (pr ∘ b) (pr ∘ f) (v 0) < Semiterm.val (pr ∘ b) (pr ∘ f) (v 1) by
        simp [Semiformula.eval_rel]; rfl]
    constructor
    · rintro ⟨x, x₁, ⟨h₁, h₂⟩, h₃⟩; rw [← h₁, ← h₂]; exact h₃
    · intro hr
      obtain ⟨x, hx⟩ := h.surj (Semiterm.val (pr ∘ b) (pr ∘ f) (v 0))
      obtain ⟨x₁, hx₁⟩ := h.surj (Semiterm.val (pr ∘ b) (pr ∘ f) (v 1))
      exact ⟨x, x₁, ⟨hx, hx₁⟩, by rw [hx, hx₁]; exact hr⟩

theorem eval_Jx (h : Reads ι e pr) {n : ℕ} (p : Semiformula ℒₒᵣ ℕ n) :
    ∀ (ε : Semiterm GraphLanguage ℕ n) (b : Fin n → W) (f : ℕ → W), ε.val b f = e →
      ((Jx ι ε p).Eval b f ↔ p.Eval (pr ∘ b) (pr ∘ f)) := by
  induction p using Semiformula.rec' with
  | hverum => intro ε b f he; simp [Jx]
  | hfalsum => intro ε b f he; simp [Jx]
  | hrel r v =>
    intro ε b f he
    rename_i k
    match k, r with
    | 2, r => exact eval_atomJx h ε r v b f he
  | hnrel r v =>
    intro ε b f he
    rename_i k
    match k, r with
    | 2, r =>
      simp only [Jx, LogicalConnective.HomClass.map_neg, Semiformula.eval_nrel,
        LogicalConnective.Prop.neg_eq]
      exact not_congr ((eval_atomJx h ε r v b f he).trans (by simp [Semiformula.eval_rel]))
  | hand p q ihp ihq =>
    intro ε b f he; simp [Jx, ihp ε b f he, ihq ε b f he]
  | hor p q ihp ihq =>
    intro ε b f he; simp [Jx, ihp ε b f he, ihq ε b f he]
  | hall p ih =>
    intro ε b f he
    have hd : ∀ x : W, (fun i => Semiterm.val (x :> b) f (![Rew.bShift ε, #0] i)) = ![e, x] := by
      intro x; funext i; refine Fin.cases ?_ (Fin.cases ?_ fun j => j.elim0) i <;> simp [he]
    simp only [Jx, Semiformula.eval_all, LogicalConnective.HomClass.map_or,
      LogicalConnective.HomClass.map_neg, eval_tpl, hd]
    simp only [h.dom, LogicalConnective.Prop.neg_eq, LogicalConnective.Prop.or_eq, not_true,
      false_or]
    simp only [fun x : W => ih (Rew.bShift ε) (x :> b) f (by simp [he]), comp_cons_pr]
    exact ⟨fun H a => by obtain ⟨x, rfl⟩ := h.surj a; exact H x, fun H x => H _⟩
  | hexs p ih =>
    intro ε b f he
    have hd : ∀ x : W, (fun i => Semiterm.val (x :> b) f (![Rew.bShift ε, #0] i)) = ![e, x] := by
      intro x; funext i; refine Fin.cases ?_ (Fin.cases ?_ fun j => j.elim0) i <;> simp [he]
    simp only [Jx, Semiformula.eval_ex, LogicalConnective.HomClass.map_and, eval_tpl, hd]
    simp only [h.dom, LogicalConnective.Prop.and_eq, true_and]
    simp only [fun x : W => ih (Rew.bShift ε) (x :> b) f (by simp [he]), comp_cons_pr]
    exact ⟨fun ⟨x, hx⟩ => ⟨_, hx⟩, fun ⟨a, ha⟩ => by obtain ⟨x, rfl⟩ := h.surj a; exact ⟨x, ha⟩⟩

end PalomarI3380.Calibration.ArithmeticInterpretation
