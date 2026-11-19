module
public import CodeSemantics
public import GateModel.ZFModel
@[expose] public section
/-! # From the machine's gate instances to pointed hulls

`CodeGate mem` says that every instance of the machine's pointed gate holds in a
structure: for a formula code `a` and distinct labels, the relation coded by `a`
has a pointed hull. Quotienting by membership-indiscernibility gives a set
structure whose equality is true equality. Each relation definable there is
compiled into a code, with label 0 assigned an object outside itself, so code `1`
acts as falsity. One gate instance then gives its hull. -/
namespace ZF207.GateModel
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

abbrev CF := C207Soundness.Formula
open C207Soundness (Assignment update evalCode)

/-- Formulas without equality atoms. Their meaning does not depend on how a
structure interprets equality. -/
def _root_.C207Soundness.Formula.EqFree : CF → Prop
  | .truth => True
  | .imp p q => p.EqFree ∧ q.EqFree
  | .mem _ _ => True
  | .all _ p => p.EqFree
  | .eq _ _ => False

/-- The machine's gate, read semantically, for equality-free formulas. -/
def CodeGate {W : Type*} (mem : W → W → Prop) : Prop :=
  ∀ A : CF, A.EqFree → ∀ d h : Nat, A.code ≠ d → A.code ≠ h → d ≠ h → ∀ s : Assignment W,
    let a := A.code
    ∃ C, (∀ z, mem z C → ∃ p, evalCode mem a (update (update s d p) h z) ∧
      ∀ u, (∀ w, mem w u → mem w z) → ∀ v, evalCode mem a (update (update s d u) h v) →
        ∃ w, evalCode mem a (update (update s d u) h w) ∧ mem w C) ∧
    (evalCode mem a s → mem (s h) C)

section Indisc
variable {W : Type*} (mem : W → W → Prop)

/-- Indiscernibility by membership. -/
def Indisc (x y : W) : Prop := ∀ z, (mem z x ↔ mem z y) ∧ (mem x z ↔ mem y z)

def indiscSetoid : Setoid W where
  r := Indisc mem
  iseqv := ⟨fun _ _ => ⟨Iff.rfl, Iff.rfl⟩, fun h z => ⟨(h z).1.symm, (h z).2.symm⟩,
    fun h₁ h₂ z => ⟨(h₁ z).1.trans (h₂ z).1, (h₁ z).2.trans (h₂ z).2⟩⟩

/-- The indiscernibility quotient. -/
def NQ := Quotient (indiscSetoid mem)

instance : SetStructure (NQ mem) where
  mem Y X := Quotient.lift₂ (s₁ := indiscSetoid mem) (s₂ := indiscSetoid mem)
    (fun x y => mem x y) (fun _ y₁ x₂ _ hx hy => propext ((hx y₁).2.trans (hy x₂).1)) X Y

/-- The class of an object. -/
def cls (x : W) : NQ mem := Quotient.mk (indiscSetoid mem) x

lemma cls_mem {x y : W} : cls mem x ∈ cls mem y ↔ mem x y := Iff.rfl

lemma cls_eq {x y : W} : cls mem x = cls mem y ↔ Indisc mem x y :=
  Quotient.eq (r := indiscSetoid mem)

lemma cls_surj (X : NQ mem) : ∃ x, cls mem x = X := Quotient.exists_rep X

end Indisc

/-! ## Compiling formulas into codes -/

/-- Falsity, using label 0 for an object outside itself. -/
def cfls : CF := .mem 0 0
def cneg (p : CF) : CF := .imp p cfls
def cand (p q : CF) : CF := cneg (.imp p (cneg q))
def cor (p q : CF) : CF := .imp (cneg p) q
def ciff (p q : CF) : CF := cand (.imp p q) (.imp q p)
def cex (i : Nat) (p : CF) : CF := cneg (.all i (cneg p))
/-- Indiscernibility of labels `a` and `b`, binding the fresh label `z`. -/
def cindisc (a b z : Nat) : CF :=
  cand (.all z (ciff (.mem z a) (.mem z b))) (.all z (ciff (.mem a z) (.mem b z)))

/-- Term labels: bound variables through `σ`, free variable `j` at `2j+1`. -/
def tlab {n : ℕ} (σ : Fin n → Nat) : Semiterm ℒₛₑₜ ℕ n → Nat
  | .bvar i => σ i
  | .fvar j => 2 * j + 1
  | .func f _ => Empty.elim f

/-- Compile a formula; `z` is the next fresh (even) label. -/
def compile : ∀ {n : ℕ}, Semiformula ℒₛₑₜ ℕ n → (Fin n → Nat) → Nat → CF
  | _, .verum, _, _ => .truth
  | _, .falsum, _, _ => cfls
  | _, .rel Language.Set.Rel.eq ts, σ, z => cindisc (tlab σ (ts 0)) (tlab σ (ts 1)) z
  | _, .rel Language.Set.Rel.mem ts, σ, _ => .mem (tlab σ (ts 0)) (tlab σ (ts 1))
  | _, .nrel Language.Set.Rel.eq ts, σ, z => cneg (cindisc (tlab σ (ts 0)) (tlab σ (ts 1)) z)
  | _, .nrel Language.Set.Rel.mem ts, σ, _ => cneg (.mem (tlab σ (ts 0)) (tlab σ (ts 1)))
  | _, .and φ ψ, σ, z => cand (compile φ σ z) (compile ψ σ z)
  | _, .or φ ψ, σ, z => cor (compile φ σ z) (compile ψ σ z)
  | _, .all φ, σ, z => .all z (compile φ (z :> σ) (z + 2))
  | _, .exs φ, σ, z => cex z (compile φ (z :> σ) (z + 2))

lemma compile_eqFree : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n) (σ : Fin n → Nat) (z : Nat),
    (compile φ σ z).EqFree
  | _, .verum, _, _ => trivial
  | _, .falsum, _, _ => trivial
  | _, .rel Language.Set.Rel.eq _, _, _ => by simp [compile, cindisc, cand, cneg, ciff, cfls, C207Soundness.Formula.EqFree]
  | _, .rel Language.Set.Rel.mem _, _, _ => trivial
  | _, .nrel Language.Set.Rel.eq _, _, _ => by simp [compile, cindisc, cand, cneg, ciff, cfls, C207Soundness.Formula.EqFree]
  | _, .nrel Language.Set.Rel.mem _, _, _ => by simp [compile, cneg, cfls, C207Soundness.Formula.EqFree]
  | _, .and φ ψ, σ, z => by
    simp only [compile, cand, cneg, cfls, C207Soundness.Formula.EqFree]
    exact ⟨⟨compile_eqFree φ σ z, compile_eqFree ψ σ z, trivial⟩, trivial⟩
  | _, .or φ ψ, σ, z => by
    simp only [compile, cor, cneg, cfls, C207Soundness.Formula.EqFree]
    exact ⟨⟨compile_eqFree φ σ z, trivial⟩, compile_eqFree ψ σ z⟩
  | _, .all φ, σ, z => by
    simpa only [compile, C207Soundness.Formula.EqFree] using compile_eqFree φ (z :> σ) (z + 2)
  | _, .exs φ, σ, z => by
    simp only [compile, cex, cneg, cfls, C207Soundness.Formula.EqFree]
    exact ⟨⟨compile_eqFree φ (z :> σ) (z + 2), trivial⟩, trivial⟩

section Helpers
variable {W : Type*} {mem : W → W → Prop}

lemma update_ne {s : Assignment W} {i j : Nat} (x : W) (h : j ≠ i) : update s i x j = s j := by
  simp [update, h]

/-- Labels respect the invariant: bound labels are even and below the fresh label. -/
def LabelsOK {n : ℕ} (σ : Fin n → Nat) (z : Nat) : Prop :=
  z % 2 = 0 ∧ 0 < z ∧ ∀ i, σ i % 2 = 0 ∧ 0 < σ i ∧ σ i < z

lemma tlab_ne {n : ℕ} {σ : Fin n → Nat} {z : Nat} (hl : LabelsOK σ z)
    (t : Semiterm ℒₛₑₜ ℕ n) : tlab σ t ≠ z := by
  cases t with
  | bvar i => exact Nat.ne_of_lt (hl.2.2 i).2.2
  | fvar j => have := hl.1; show 2 * j + 1 ≠ z; omega
  | func f _ => exact Empty.elim f

lemma tlab_val {n : ℕ} {σ : Fin n → Nat} {s : Assignment W} {b : Fin n → NQ mem}
    {f : ℕ → NQ mem} (hf : ∀ j, cls mem (s (2 * j + 1)) = f j)
    (hb : ∀ i, cls mem (s (σ i)) = b i) (t : Semiterm ℒₛₑₜ ℕ n) :
    cls mem (s (tlab σ t)) = t.val b f := by
  cases t with
  | bvar i => exact hb i
  | fvar j => exact hf j
  | func f _ => exact Empty.elim f

end Helpers

section Eval
variable {W : Type*} {mem : W → W → Prop} {e : W} (he : ∀ y, ¬ mem y e)
include he

lemma eval_cfls {s : Assignment W} (h0 : s 0 = e) : ¬ cfls.eval mem s := by
  show ¬ mem (s 0) (s 0)
  rw [h0]; exact he e

lemma eval_cneg {s : Assignment W} (h0 : s 0 = e) (p : CF) :
    (cneg p).eval mem s ↔ ¬ p.eval mem s :=
  ⟨fun h hp => eval_cfls he h0 (h hp), fun h hp => (h hp).elim⟩

lemma eval_cand {s : Assignment W} (h0 : s 0 = e) (p q : CF) :
    (cand p q).eval mem s ↔ p.eval mem s ∧ q.eval mem s := by
  unfold cand
  rw [eval_cneg he h0]
  show ¬(p.eval mem s → (cneg q).eval mem s) ↔ _
  rw [eval_cneg he h0]
  tauto

lemma eval_cor {s : Assignment W} (h0 : s 0 = e) (p q : CF) :
    (cor p q).eval mem s ↔ p.eval mem s ∨ q.eval mem s := by
  show ((cneg p).eval mem s → q.eval mem s) ↔ _
  rw [eval_cneg he h0]
  tauto

lemma eval_ciff {s : Assignment W} (h0 : s 0 = e) (p q : CF) :
    (ciff p q).eval mem s ↔ (p.eval mem s ↔ q.eval mem s) := by
  unfold ciff
  rw [eval_cand he h0]
  exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun h => ⟨h.1, h.2⟩⟩

lemma eval_cindisc {s : Assignment W} (h0 : s 0 = e) {a b z : Nat}
    (hz0 : z ≠ 0) (ha : a ≠ z) (hb : b ≠ z) :
    (cindisc a b z).eval mem s ↔ Indisc mem (s a) (s b) := by
  unfold cindisc
  rw [eval_cand he h0]
  have h0' : ∀ w, update s z w 0 = e := fun w => by rw [update_ne w (Ne.symm hz0)]; exact h0
  show ((∀ w, (ciff (.mem z a) (.mem z b)).eval mem (update s z w)) ∧
      ∀ w, (ciff (.mem a z) (.mem b z)).eval mem (update s z w)) ↔ _
  simp only [eval_ciff he (h0' _)]
  show ((∀ w, (mem (update s z w z) (update s z w a) ↔ mem (update s z w z) (update s z w b))) ∧
      ∀ w, (mem (update s z w a) (update s z w z) ↔ mem (update s z w b) (update s z w z))) ↔ _
  simp only [update_ne _ ha, update_ne _ hb]
  simp only [update, if_pos rfl]
  exact ⟨fun ⟨h₁, h₂⟩ w => ⟨h₁ w, h₂ w⟩, fun h => ⟨fun w => (h w).1, fun w => (h w).2⟩⟩

/-- Compilation preserves meaning. -/
theorem eval_compile {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n) (σ : Fin n → Nat) (z : Nat)
    (f : ℕ → NQ mem) (b : Fin n → NQ mem) (s : Assignment W) (hl : LabelsOK σ z)
    (h0 : s 0 = e) (hf : ∀ j, cls mem (s (2 * j + 1)) = f j)
    (hb : ∀ i, cls mem (s (σ i)) = b i) :
    (compile φ σ z).eval mem s ↔ φ.Eval b f := by
  induction φ using Semiformula.rec' generalizing z s with
  | hverum => simp [compile, C207Soundness.Formula.eval]
  | hfalsum =>
    change cfls.eval mem s ↔ False
    exact iff_false_intro (eval_cfls he h0)
  | hrel r ts =>
    cases r with
    | eq =>
      show (cindisc _ _ z).eval mem s ↔ (ts 0).val b f = (ts 1).val b f
      rw [eval_cindisc he h0 (Nat.pos_iff_ne_zero.mp hl.2.1) (tlab_ne hl _) (tlab_ne hl _), ← tlab_val hf hb,
        ← tlab_val hf hb, cls_eq]
    | mem =>
      show mem _ _ ↔ (ts 0).val b f ∈ (ts 1).val b f
      rw [← tlab_val hf hb, ← tlab_val hf hb, cls_mem]
  | hnrel r ts =>
    cases r with
    | eq =>
      show (cneg (cindisc _ _ z)).eval mem s ↔ ¬(ts 0).val b f = (ts 1).val b f
      rw [eval_cneg he h0, eval_cindisc he h0 (Nat.pos_iff_ne_zero.mp hl.2.1) (tlab_ne hl _) (tlab_ne hl _),
        ← tlab_val hf hb, ← tlab_val hf hb, cls_eq]
    | mem =>
      show (cneg (.mem _ _)).eval mem s ↔ ¬(ts 0).val b f ∈ (ts 1).val b f
      rw [eval_cneg he h0, ← tlab_val hf hb, ← tlab_val hf hb, cls_mem]
      rfl
  | hand φ ψ ihφ ihψ =>
    show (cand _ _).eval mem s ↔ _
    rw [eval_cand he h0, ihφ σ z b s hl h0 hf hb, ihψ σ z b s hl h0 hf hb]
    simp
  | hor φ ψ ihφ ihψ =>
    show (cor _ _).eval mem s ↔ _
    rw [eval_cor he h0, ihφ σ z b s hl h0 hf hb, ihψ σ z b s hl h0 hf hb]
    simp
  | hall φ ih =>
    obtain ⟨hz2, hz0, hσ⟩ := hl
    have h0' : ∀ x, update s z x 0 = e := fun x => by
      rw [update_ne x (by omega)]; exact h0
    have hf' : ∀ x j, cls mem (update s z x (2 * j + 1)) = f j := fun x j => by
      rw [update_ne x (by omega)]; exact hf j
    have hb' : ∀ x i, cls mem (update s z x ((z :> σ) i)) = (cls mem x :> b) i := by
      intro x i
      cases i using Fin.cases with
      | zero => simp [update]
      | succ j =>
        simp only [Matrix.cons_val_succ]
        rw [update_ne x (Nat.ne_of_lt (hσ j).2.2)]; exact hb j
    have hl' : LabelsOK (z :> σ) (z + 2) := ⟨by omega, by omega, fun i => by
      cases i using Fin.cases with
      | zero => simp; omega
      | succ j => simp only [Matrix.cons_val_succ]; have := hσ j; omega⟩
    have key := fun x => ih (z :> σ) (z + 2) (cls mem x :> b) (update s z x) hl' (h0' x) (hf' x) (hb' x)
    change (∀ x, (compile φ (z :> σ) (z + 2)).eval mem (update s z x)) ↔ ∀ X, φ.Eval (X :> b) f
    constructor
    · intro h X
      obtain ⟨x, rfl⟩ := cls_surj mem X
      exact (key x).mp (h x)
    · intro h x
      exact (key x).mpr (h (cls mem x))
  | hexs φ ih =>
    obtain ⟨hz2, hz0, hσ⟩ := hl
    have h0' : ∀ x, update s z x 0 = e := fun x => by
      rw [update_ne x (by omega)]; exact h0
    have hf' : ∀ x j, cls mem (update s z x (2 * j + 1)) = f j := fun x j => by
      rw [update_ne x (by omega)]; exact hf j
    have hb' : ∀ x i, cls mem (update s z x ((z :> σ) i)) = (cls mem x :> b) i := by
      intro x i
      cases i using Fin.cases with
      | zero => simp [update]
      | succ j =>
        simp only [Matrix.cons_val_succ]
        rw [update_ne x (Nat.ne_of_lt (hσ j).2.2)]; exact hb j
    have hl' : LabelsOK (z :> σ) (z + 2) := ⟨by omega, by omega, fun i => by
      cases i using Fin.cases with
      | zero => simp; omega
      | succ j => simp only [Matrix.cons_val_succ]; have := hσ j; omega⟩
    have key := fun x => ih (z :> σ) (z + 2) (cls mem x :> b) (update s z x) hl' (h0' x) (hf' x) (hb' x)
    change (cneg (.all z (cneg (compile φ (z :> σ) (z + 2))))).eval mem s ↔ ∃ X, φ.Eval (X :> b) f
    rw [eval_cneg he h0]
    constructor
    · intro h
      by_contra hne
      apply h
      change ∀ x, (cneg (compile φ (z :> σ) (z + 2))).eval mem (update s z x)
      intro x
      rw [eval_cneg he (h0' x)]
      exact fun hx => hne ⟨cls mem x, (key x).mp hx⟩
    · rintro ⟨X, hX⟩ h
      obtain ⟨x, rfl⟩ := cls_surj mem X
      exact (eval_cneg he (h0' x) _).mp (h x) ((key x).mpr hX)

end Eval

/-! ## The bridge -/

universe u

section Bridge
variable {W : Type u} [Nonempty W] {mem : W → W → Prop} {e : W} (he : ∀ y, ¬ mem y e)

include he

/-- The class of the empty object is empty. -/
lemma nq_isEmpty : SetTheory.IsEmpty (cls mem e) := by
  intro Y hY
  obtain ⟨y, rfl⟩ := cls_surj mem Y
  exact he y hY

omit he in
instance : Nonempty (NQ mem) := ⟨cls mem (Classical.arbitrary W)⟩

/-- Gate instances give pointed hulls in the indiscernibility quotient. -/
theorem gateHull_of_codeGate (hg : CodeGate mem) : GateHull (NQ mem) := by
  classical
  refine ⟨fun R hR u₀ v₀ => ?_⟩
  haveI : Inhabited (NQ mem) := ⟨cls mem e⟩
  obtain ⟨φ, hφ⟩ := hR.definable
  let ψ := Rew.rewriteMap φ.idxOfFVar ▹ φ
  let f := φ.enumerateFVar
  have hψ : ∀ v, ψ.Eval v f ↔ R (v 0) (v 1) := fun v => by
    rw [Semiformula.eval_rewriteMap, Semiformula.eval_enumerateFVar_idxOfFVar_eq_id]
    exact hφ v
  let A : CF := compile ψ ![2, 4] 6
  let P : CF := cand A (.imp (.mem 2 4) (.mem 2 4))
  have hlab : 2 < P.code ∧ 4 < P.code := by
    have := P.labels_below_code
    simp only [P, cand, cneg, cfls, C207Soundness.Formula.LabelsLT] at this
    exact this.1.2.1.1
  have hl : LabelsOK ![2, 4] 6 := ⟨rfl, by omega, fun i => by
    cases i using Fin.cases with
    | zero => simp
    | succ j => rw [Subsingleton.elim j 0]; simp⟩
  -- meaning of the code at assignments that fix label 0 and the parameter labels
  let s₁ : Assignment W := fun i => if i = 0 then e else (cls_surj mem (f ((i - 1) / 2))).choose
  have key : ∀ t : Assignment W, t 0 = e → (∀ j, cls mem (t (2 * j + 1)) = f j) →
      (evalCode mem P.code t ↔ R (cls mem (t 2)) (cls mem (t 4))) := by
    intro t h0 hf
    rw [C207Soundness.evalCode_of_formula, eval_cand he h0]
    have hb : ∀ i, cls mem (t ((![2, 4] : Fin 2 → Nat) i)) = (![cls mem (t 2), cls mem (t 4)] : Fin 2 → NQ mem) i := by
      intro i
      cases i using Fin.cases with
      | zero => rfl
      | succ j => rw [Subsingleton.elim j 0]; rfl
    rw [eval_compile he ψ ![2, 4] 6 f _ t hl h0 hf hb, hψ]
    exact ⟨fun h => h.1, fun h => ⟨h, id⟩⟩
  have h₁0 : s₁ 0 = e := by simp [s₁]
  have h₁f : ∀ j, cls mem (s₁ (2 * j + 1)) = f j := fun j => by
    simp only [s₁, if_neg (show 2 * j + 1 ≠ 0 by omega)]
    rw [show (2 * j + 1 - 1) / 2 = j by omega]
    exact (cls_surj mem (f j)).choose_spec
  -- assignments obtained by moving labels 2 and 4 keep the invariant
  have upd : ∀ p z : W, (update (update s₁ 2 p) 4 z) 0 = e ∧
      ∀ j, cls mem ((update (update s₁ 2 p) 4 z) (2 * j + 1)) = f j := fun p z =>
    ⟨by simp [update, h₁0], fun j => by
      rw [update_ne z (by omega), update_ne p (by omega)]; exact h₁f j⟩
  have upd24 : ∀ p z : W, (update (update s₁ 2 p) 4 z) 2 = p ∧ (update (update s₁ 2 p) 4 z) 4 = z :=
    fun p z => ⟨by simp [update], by simp [update]⟩
  obtain ⟨u, hu⟩ := cls_surj mem u₀
  obtain ⟨v, hv⟩ := cls_surj mem v₀
  set s := update (update s₁ 2 u) 4 v with hs
  have hfree : P.EqFree := by
    simp only [P, cand, cneg, cfls, C207Soundness.Formula.EqFree]
    exact ⟨⟨compile_eqFree ψ ![2, 4] 6, ⟨trivial, trivial⟩, trivial⟩, trivial⟩
  obtain ⟨C, hC, hstart⟩ := hg P hfree 2 4 (by omega) (by omega) (by decide) s
  refine ⟨cls mem C, fun hR₀ => ?_, fun Z hZ => ?_⟩
  · have := hstart ((key s (upd u v).1 (upd u v).2).mpr
      (by rw [hs, (upd24 u v).1, (upd24 u v).2, hu, hv]; exact hR₀))
    rw [hs, (upd24 u v).2] at this
    rw [← hv]; exact this
  · obtain ⟨z, rfl⟩ := cls_surj mem Z
    have hz : mem z C := hZ
    obtain ⟨p, hp, hcov⟩ := hC z hz
    have hs₂ : update (update s 2 p) 4 z = update (update s₁ 2 p) 4 z := by
      rw [hs, C207Soundness.update_commute _ 4 2 (by decide), C207Soundness.update_same,
        C207Soundness.update_same]
    refine ⟨⟨cls mem p, ?_⟩, fun U hU ⟨V, hUV⟩ => ?_⟩
    · rw [hs₂] at hp
      have := (key _ (upd p z).1 (upd p z).2).mp hp
      rwa [(upd24 p z).1, (upd24 p z).2] at this
    · obtain ⟨u', rfl⟩ := cls_surj mem U
      obtain ⟨v', rfl⟩ := cls_surj mem V
      have hu' : ∀ w, mem w u' → mem w z := fun w hw => hU (cls mem w) hw
      have hs₃ : ∀ y, update (update s 2 u') 4 y = update (update s₁ 2 u') 4 y := fun y => by
        rw [hs, C207Soundness.update_commute _ 4 2 (by decide), C207Soundness.update_same,
          C207Soundness.update_same]
      have hv' : evalCode mem P.code (update (update s 2 u') 4 v') := by
        rw [hs₃, key _ (upd u' v').1 (upd u' v').2, (upd24 u' v').1, (upd24 u' v').2]
        exact hUV
      obtain ⟨w, hw, hwC⟩ := hcov u' hu' v' hv'
      refine ⟨cls mem w, hwC, ?_⟩
      rw [hs₃, key _ (upd u' w).1 (upd u' w).2, (upd24 u' w).1, (upd24 u' w).2] at hw
      exact hw

/-- A structure satisfying the machine's gate, with an object having no members,
contains a model of ZF. -/
theorem codeGate_models_zf (hg : CodeGate mem) :
    ∃ (N : Type u) (_ : SetStructure N) (_ : Nonempty N), N↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  haveI := gateHull_of_codeGate he hg
  exact ⟨WFPart (Q (nq_isEmpty (W := W) (mem := mem) (e := e) he)), inferInstance, inferInstance,
    gate_interprets_zf _⟩

end Bridge

end ZF207.GateModel
