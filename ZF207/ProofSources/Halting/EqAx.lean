module
public import Halting.ChiX
public import Halting.Closure
@[expose] public section
/-! # C proves the translations of the equality axioms

`=` translates to the defined equality `ceqv` and `∈` to membership up to `ceqv`; the kernel's
equality logic gives reflexivity (from the witness `∃x E(y,x)`), symmetry, transitivity and the
congruence of the membership atom (`sub_atomL`). -/
namespace ZF207.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ZF207.Internal ZF207.Internal.Tait ZF207.CKernel.Generic ZF207.CKernel.Generic.Logic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]


lemma xlab_ne_rlab (f d k : V) : xlab f d ≠ rlab k := by
  simp only [xlab, rlab, ne_eq, add_left_inj, pair_ext_iff, not_and]
  intro h; exfalso
  have : (2 : V) ≤ f + 2 := le_add_self
  rw [h] at this; simp at this

lemma notRes_xlab' (f d : V) : NotRes (xlab f d) := by
  simp [NotRes, xlab_ne_rlab]

lemma pr_iff' (x : V) : D.val.Evalb ![x] ↔ (KL (V := V)).S.Prov x := D_iff_S x

/-! ## Propositional shapes of the translated axioms -/

lemma shape_imp {A B : V} (h : (KL (V := V)).S.Prov ((KL (V := V)).S.imp A B)) :
    D.val.Evalb ![cneg (cand A (cneg B))] := by
  rw [pr_iff']
  have c : (KL (V := V)).S.toLogic.Ctx [(KL (V := V)).S.and A ((KL (V := V)).S.neg B)] (KL (V := V)).S.bot :=
    .mp (.mp Ctx.head.andLeft (.thm h)) Ctx.head.andRight
  simpa [cneg] using c.deduction.empty

lemma shape_imp2 {A B C : V} (h : (KL (V := V)).S.Prov ((KL (V := V)).S.imp A ((KL (V := V)).S.imp B C))) :
    D.val.Evalb ![cneg (cand A (cand B (cneg C)))] := by
  rw [pr_iff']
  have hA : (KL (V := V)).S.toLogic.Ctx [(KL (V := V)).S.and A ((KL (V := V)).S.and B ((KL (V := V)).S.neg C))] A := Ctx.head.andLeft
  have hB : (KL (V := V)).S.toLogic.Ctx [(KL (V := V)).S.and A ((KL (V := V)).S.and B ((KL (V := V)).S.neg C))] B := Ctx.head.andRight.andLeft
  have hC : (KL (V := V)).S.toLogic.Ctx [(KL (V := V)).S.and A ((KL (V := V)).S.and B ((KL (V := V)).S.neg C))] ((KL (V := V)).S.neg C) :=
    Ctx.head.andRight.andRight
  have c : (KL (V := V)).S.toLogic.Ctx [(KL (V := V)).S.and A ((KL (V := V)).S.and B ((KL (V := V)).S.neg C))] (KL (V := V)).S.bot :=
    .mp (.mp hB (.mp hA (.thm h))) hC
  simpa [cneg] using c.deduction.empty

lemma shape_ext {A B C E : V} (h : (KL (V := V)).S.Prov ((KL (V := V)).S.imp A ((KL (V := V)).S.imp B ((KL (V := V)).S.imp C E)))) :
    D.val.Evalb ![cneg (cand (cand A (cand B (cneg 1))) (cand C (cneg E)))] := by
  rw [pr_iff']
  let H := (KL (V := V)).S.and ((KL (V := V)).S.and A ((KL (V := V)).S.and B ((KL (V := V)).S.neg (KL (V := V)).S.bot))) ((KL (V := V)).S.and C ((KL (V := V)).S.neg E))
  have hA : (KL (V := V)).S.toLogic.Ctx [H] A := Ctx.head.andLeft.andLeft
  have hB : (KL (V := V)).S.toLogic.Ctx [H] B := Ctx.head.andLeft.andRight.andLeft
  have hC : (KL (V := V)).S.toLogic.Ctx [H] C := Ctx.head.andRight.andLeft
  have hE : (KL (V := V)).S.toLogic.Ctx [H] ((KL (V := V)).S.neg E) := Ctx.head.andRight.andRight
  have c : (KL (V := V)).S.toLogic.Ctx [H] (KL (V := V)).S.bot := .mp (.mp hC (.mp hB (.mp hA (.thm h)))) hE
  simpa [H, cneg] using c.deduction.empty

lemma gen_all {x A : V} (h : D.val.Evalb ![A]) : D.val.Evalb ![all x A] := by
  rw [pr_iff'] at h ⊢; simpa using (KL (V := V)).S.gen x h

/-! ## Equality facts -/

lemma ceqv_refl (x : V) (hx : x ≠ rlab 0) : (KL (V := V)).S.Prov ((KL (V := V)).S.E x x) := by
  let y : V := ⟪7, x⟫ + 1
  have hyx : y ≠ x := ne_of_gt (lt_succ_iff_le.mpr (le_pair_right _ _))
  have hy : y ≠ rlab 0 := by simp [y, rlab]
  have okx : (KL (V := V)).S.ok x := ((KL (V := V)).ok_iff _).mpr hx
  have oky : (KL (V := V)).S.ok y := ((KL (V := V)).ok_iff _).mpr hy
  have hm : (KL (V := V)).S.Prov ((KL (V := V)).S.imp ((KL (V := V)).S.E x y) ((KL (V := V)).S.E x x)) := by
    have c : (KL (V := V)).S.toLogic.Ctx [(KL (V := V)).S.E x y] ((KL (V := V)).S.E x x) :=
      .mp (.mp Ctx.head (.thm ((KL (V := V)).S.eSymm x y okx oky)))
        (.mp Ctx.head (.thm ((KL (V := V)).S.eTrans x y x okx oky okx)))
    exact c.deduction.empty
  exact (Ctx.existsElim (Γ := []) y ((KL (V := V)).S.eVac x x y hyx hyx okx okx oky) (.thm ((KL (V := V)).S.gen y hm))
    (.thm ((KL (V := V)).S.witness y x hyx oky okx))).empty

@[simp] lemma atomL0 (a b : V) : atomL 0 a b = ceqv a b := by simp [atomL]

@[simp] lemma nth_three (a b c d : V) : (a ∷ b ∷ c ∷ d ∷ (0 : V)).[3] = d := by
  rw [show (3 : V) = 0 + 1 + 1 + 1 by norm_num, nth_adjoin_succ, nth_adjoin_succ, nth_adjoin_succ,
    nth_adjoin_zero]

lemma okL (x : V) (hx : x ≠ rlab 0) : (KL (V := V)).S.ok x := ((KL (V := V)).ok_iff _).mpr hx

local macro "eqsimp" : tactic => `(tactic| (rw [chiS_quote]; simp [trX, atomX, tlab,
  Semiformula.Operator.eq_def, Semiformula.Operator.mem_def, Matrix.conj, Semiformula.imp_eq,
  allClosure_succ, Matrix.vecTail, Fin.addCast, Fin.addNat, Function.comp_def, atomL0, nth_three, atomL]))

theorem eqRefl_D : D.val.Evalb ![chiS (0 : V) ⌜(Theory.Eq.refl ℒₛₑₜ)⌝] := by
  eqsimp
  exact gen_all ((pr_iff' _).mpr (by simpa using ceqv_refl _ (xlab_ne_rlab _ _ _)))

theorem eqSymm_D : D.val.Evalb ![chiS (0 : V) ⌜(Theory.Eq.symm ℒₛₑₜ)⌝] := by
  eqsimp
  have o := okL (V := V)
  exact gen_all (gen_all (shape_imp (by
    simpa using (KL (V := V)).S.eSymm (xlab 0 0) (xlab 0 1) (o _ (xlab_ne_rlab _ _ _)) (o _ (xlab_ne_rlab _ _ _)))))

theorem eqTrans_D : D.val.Evalb ![chiS (0 : V) ⌜(Theory.Eq.trans ℒₛₑₜ)⌝] := by
  eqsimp
  have o := okL (V := V)
  exact gen_all (gen_all (gen_all (shape_imp2 (by
    simpa using (KL (V := V)).S.eTrans (xlab 0 0) (xlab 0 1) (xlab 0 (1 + 1)) (o _ (xlab_ne_rlab _ _ _))
      (o _ (xlab_ne_rlab _ _ _)) (o _ (xlab_ne_rlab _ _ _))))))

theorem eqExtEq_D : D.val.Evalb ![chiS (0 : V) ⌜(Theory.Eq.relExt (L := ℒₛₑₜ) (k := 2) Language.Set.Rel.eq)⌝] := by
  eqsimp
  have o := okL (V := V)
  set X0 := xlab (0 : V) 0; set X1 := xlab (0 : V) 1; set X2 := xlab (0 : V) (1 + 1)
  set X3 := xlab (0 : V) (1 + 1 + 1)
  have o0 := o X0 (xlab_ne_rlab _ _ _); have o1 := o X1 (xlab_ne_rlab _ _ _)
  have o2 := o X2 (xlab_ne_rlab _ _ _); have o3 := o X3 (xlab_ne_rlab _ _ _)
  refine gen_all (gen_all (gen_all (gen_all (shape_ext ?_))))
  have c : (KL (V := V)).S.toLogic.Ctx [(KL (V := V)).S.E X3 X2, (KL (V := V)).S.E X2 X0, (KL (V := V)).S.E X3 X1] ((KL (V := V)).S.E X1 X0) := by
    have h31 : (KL (V := V)).S.toLogic.Ctx [(KL (V := V)).S.E X3 X2, (KL (V := V)).S.E X2 X0, (KL (V := V)).S.E X3 X1] ((KL (V := V)).S.E X3 X1) :=
      .hyp (by simp)
    have h20 : (KL (V := V)).S.toLogic.Ctx [(KL (V := V)).S.E X3 X2, (KL (V := V)).S.E X2 X0, (KL (V := V)).S.E X3 X1] ((KL (V := V)).S.E X2 X0) :=
      .hyp (by simp)
    have h32 : (KL (V := V)).S.toLogic.Ctx [(KL (V := V)).S.E X3 X2, (KL (V := V)).S.E X2 X0, (KL (V := V)).S.E X3 X1] ((KL (V := V)).S.E X3 X2) :=
      Ctx.head
    have h13 := Ctx.mp h31 (.thm ((KL (V := V)).S.eSymm X3 X1 o3 o1))
    have h30 := Ctx.mp h20 (Ctx.mp h32 (.thm ((KL (V := V)).S.eTrans X3 X2 X0 o3 o2 o0)))
    exact Ctx.mp h30 (Ctx.mp h13 (.thm ((KL (V := V)).S.eTrans X1 X3 X0 o1 o3 o0)))
  simpa using c.deduction.deduction.deduction.empty

theorem eqExtMem_D : D.val.Evalb ![chiS (0 : V) ⌜(Theory.Eq.relExt (L := ℒₛₑₜ) (k := 2) Language.Set.Rel.mem)⌝] := by
  rw [chiS_quote]; simp [trX, atomX, tlab,
    Semiformula.Operator.eq_def, Semiformula.Operator.mem_def, Matrix.conj, Semiformula.imp_eq,
    allClosure_succ, Matrix.vecTail, Fin.addCast, Fin.addNat, Function.comp_def, atomL0, nth_three]
  have o := okL (V := V)
  set X0 := xlab (0 : V) 0; set X1 := xlab (0 : V) 1; set X2 := xlab (0 : V) (1 + 1)
  set X3 := xlab (0 : V) (1 + 1 + 1)
  have n0 := notRes_xlab' (0 : V) 0; have n1 := notRes_xlab' (0 : V) 1
  have n2 := notRes_xlab' (0 : V) (1 + 1); have n3 := notRes_xlab' (0 : V) (1 + 1 + 1)
  have s1 : (KL (V := V)).SubEq X3 X1 (atomL 1 X3 X2) (atomL 1 X1 X2) :=
    IntLogic.sub_atomL 1 n3 n1 n1 n2 (Or.inr ⟨rfl, rfl⟩) (Or.inl rfl)
  have s2 : (KL (V := V)).SubEq X2 X0 (atomL 1 X1 X2) (atomL 1 X1 X0) :=
    IntLogic.sub_atomL 1 n2 n0 n1 n2 (Or.inl rfl) (Or.inr ⟨rfl, rfl⟩)
  refine gen_all (gen_all (gen_all (gen_all (shape_ext ?_))))
  have m1 := IntLogic.sub_mp s1
  have m2 := IntLogic.sub_mp s2
  have c : (KL (V := V)).S.toLogic.Ctx [atomL 1 X3 X2, (KL (V := V)).S.E X2 X0, (KL (V := V)).S.E X3 X1] (atomL 1 X1 X0) := by
    have h31 : (KL (V := V)).S.toLogic.Ctx [atomL 1 X3 X2, (KL (V := V)).S.E X2 X0, (KL (V := V)).S.E X3 X1] ((KL (V := V)).S.E X3 X1) :=
      .hyp (by simp)
    have h20 : (KL (V := V)).S.toLogic.Ctx [atomL 1 X3 X2, (KL (V := V)).S.E X2 X0, (KL (V := V)).S.E X3 X1] ((KL (V := V)).S.E X2 X0) :=
      .hyp (by simp)
    have hA : (KL (V := V)).S.toLogic.Ctx [atomL 1 X3 X2, (KL (V := V)).S.E X2 X0, (KL (V := V)).S.E X3 X1] (atomL 1 X3 X2) :=
      Ctx.head
    exact Ctx.mp (Ctx.mp hA (Ctx.mp h31 (.thm m1))) (Ctx.mp h20 (.thm m2))
  simpa using c.deduction.deduction.deduction.empty

/-- `U` proves the equality axioms of `ℒₛₑₜ`. -/
theorem U_proves_eq {σ : Sentence ℒₛₑₜ} (h : σ ∈ (𝗘𝗤 ℒₛₑₜ : Theory ℒₛₑₜ)) : theoryU ⊢ σ := by
  cases h with
  | refl => exact U_of_cprov (eqRefl_D (V := ℕ))
  | symm => exact U_of_cprov (eqSymm_D (V := ℕ))
  | trans => exact U_of_cprov (eqTrans_D (V := ℕ))
  | funcExt f => exact nomatch f
  | relExt r =>
    rename_i k
    match k, r with
    | 2, .eq => exact U_of_cprov (eqExtEq_D (V := ℕ))
    | 2, .mem => exact U_of_cprov (eqExtMem_D (V := ℕ))

end ZF207.Halting
