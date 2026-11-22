module
public import ZF192Support.Independence.Gate.Derivation
public import ZF192Support.Independence.Interpretation.MarkedQuotient
@[expose] public section
/-! # Pointed hulls in models of the companion theory -/
namespace ZF192Support.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory FFL.Entailment
open ZF192Support.GateModel ZF192Support.Independence

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

private theorem hulls_of_U {W : Type} [SetStructure W] [Nonempty W]
    [W↓[ℒₛₑₜ] ⊧* theoryU] : GateHull W := by
  refine ⟨fun R hR u v => ?_⟩
  classical
  letI : Inhabited W := ⟨Classical.choice (inferInstance : Nonempty W)⟩
  obtain ⟨φ, hφ⟩ := hR.definable
  let ψ := Rew.rewriteMap φ.idxOfFVar ▹ φ
  let f := φ.enumerateFVar
  have hψ : ∀ a, ψ.Eval a f ↔ R (a 0) (a 1) := fun a => by
    rw [Semiformula.eval_rewriteMap, Semiformula.eval_enumerateFVar_idxOfFVar_eq_id]
    exact hφ a
  let K := ψ.fvSup
  let φ' : Semisentence ℒₛₑₜ (K + 2) := bindParams K ▹ ψ
  have hφ' : (fun D H => φ'.Eval (D :> H :> fun l : Fin K => f l) Empty.elim) = R := by
    funext D H
    apply propext
    rw [eval_bindParams ψ f (fun x hx => Semiformula.lt_fvSup_of_fvar? hx), hψ]; rfl
  rw [← hφ']
  exact hull_of_U K φ' (fun l => f l) u v

/-- Models of `U` carry pointed hulls on their indiscernibility quotient. -/
theorem gateHull_of_U {W : Type} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* theoryU] :
    GateHull (NQ (fun x y : W => x ∈ y)) :=
  gateHull_of_ambient hulls_of_U

/-- Models of `U` have an object with no members. -/
lemma empty_of_U {W : Type} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* theoryU] :
    ∃ e : W, ∀ y, y ∉ e := by
  have := gateHull_of_U (W := W)
  obtain ⟨E, hE⟩ := exists_isEmpty (V := NQ (fun x y : W => x ∈ y))
  obtain ⟨e, rfl⟩ := cls_surj _ E
  exact ⟨e, fun y hy => hE (cls _ y) hy⟩

end ZF192Support.Halting
