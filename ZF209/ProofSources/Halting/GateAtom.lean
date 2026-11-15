module
public import Halting.EqAx
@[expose] public section
/-! # Raw membership is membership up to the defined equality

For distinct non-reserved labels, C proves `x ∈ y ↔ ∃r₁∃r₂ (x ≈ r₁ ∧ y ≈ r₂ ∧ r₁ ∈ r₂)`. Forward:
the witnesses come from head 5 (`∃r (x = r)`) and primitive transport. Backward: each conjunct of
`≈` is used at a label introduced by head 5, with backward transport for the primitive equality, so
no instantiation of a bound label at itself is needed. -/
namespace ZF209.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ZF209.Internal ZF209.Internal.Tait ZF209.CKernel.Generic ZF209.CKernel.Generic.Logic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- The machine's calculus read in `V`. -/
noncomputable abbrev SY (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] : Sys V :=
  (provRules (M := V)).sys

/-- Backward transport into a member position, for distinct labels. -/
lemma rawIn (a b w : V) (hab : a ≠ b) (haw : a ≠ w) :
    (SY V).Prov ((SY V).imp ((SY V).eq a b) ((SY V).imp ((SY V).mem w b) ((SY V).mem w a))) := by
  obtain ⟨ha, hb, hw⟩ := relIn_gt (V := V) a b w
  exact (provRules (M := V)).sys.backIn a b w ((codes : Codes V).relIn a b w + 1) hab haw ha.ne'
    hb.ne' hw.ne' (ne_of_lt (lt_add_one _)) (ne_of_gt (lt_trans ha (by simp)))
    (ne_of_gt (lt_trans hb (by simp))) (ne_of_gt (lt_trans hw (by simp)))

/-- Backward transport out of a member position, for distinct labels. -/
lemma rawOut (a b w : V) (hab : a ≠ b) (haw : a ≠ w) :
    (SY V).Prov ((SY V).imp ((SY V).eq a b) ((SY V).imp ((SY V).mem b w) ((SY V).mem a w))) := by
  obtain ⟨ha, hb, hw⟩ := relOut_gt (V := V) a b w
  exact (provRules (M := V)).sys.backOut a b w ((codes : Codes V).relOut a b w + 1) hab haw ha.ne'
    hb.ne' hw.ne' (ne_of_lt (lt_add_one _)) (ne_of_gt (lt_trans ha (by simp)))
    (ne_of_gt (lt_trans hb (by simp))) (ne_of_gt (lt_trans hw (by simp)))

lemma rlab_ne {i j : V} (h : i ≠ j) : rlab i ≠ rlab j := by simpa using h

lemma ceqv_sys (a b : V) : ceqv a b = (SY V).ceq (rlab 0) a b := rfl

lemma atomL_one_sys (a b : V) : atomL 1 a b = (SY V).ex (rlab 1) ((SY V).ex (rlab 2)
    ((SY V).and ((SY V).and ((SY V).ceq (rlab 0) a (rlab 1)) ((SY V).ceq (rlab 0) b (rlab 2)))
      ((SY V).mem (rlab 1) (rlab 2)))) := by
  simp only [atomL, _root_.one_ne_zero, ite_false]; rfl

/-- Raw membership is membership up to `≈`. -/
theorem mem_iff_atomL {x y : V} (hxy : x ≠ y) (hx : NotRes x) (hy : NotRes y) :
    (KL (V := V)).S.Prov (ciff (mem x y) (atomL 1 x y)) := by
  set r0 : V := rlab 0; set r1 : V := rlab 1; set r2 : V := rlab 2
  have h01 : r0 ≠ r1 := rlab_ne (by simp)
  have h02 : r0 ≠ r2 := rlab_ne (by simp)
  have h12 : r1 ≠ r2 := rlab_ne (by
    intro h; have := congrArg (· + 1) h; simp at this)
  obtain ⟨hx0, hx1, hx2⟩ := hx
  obtain ⟨hy0, hy1, hy2⟩ := hy
  let B : V := (SY V).and ((SY V).and ((SY V).ceq r0 x r1) ((SY V).ceq r0 y r2)) ((SY V).mem r1 r2)
  -- forward
  have fw : (SY V).toLogic.Ctx [(SY V).mem x y] ((SY V).ex r1 ((SY V).ex r2 B)) := by
    have i2 : (SY V).toLogic.Ctx [(SY V).eq y r2, (SY V).eq x r1, (SY V).mem x y] B := by
      have ex1 : (SY V).toLogic.Ctx [(SY V).eq y r2, (SY V).eq x r1, (SY V).mem x y] ((SY V).eq x r1) := .hyp (by simp)
      have ey2 : (SY V).toLogic.Ctx [(SY V).eq y r2, (SY V).eq x r1, (SY V).mem x y] ((SY V).eq y r2) := Ctx.head
      have mxy : (SY V).toLogic.Ctx [(SY V).eq y r2, (SY V).eq x r1, (SY V).mem x y] ((SY V).mem x y) := .hyp (by simp)
      have c1 := Ctx.mp ex1 (.thm ((SY V).eq_ceq (z := r0) (Ne.symm hx0) h01
        (rawIn x r1 r0 hx1 hx0) (rawOut x r1 r0 hx1 hx0)))
      have c2 := Ctx.mp ey2 (.thm ((SY V).eq_ceq (z := r0) (Ne.symm hy0) h02
        (rawIn y r2 r0 hy2 hy0) (rawOut y r2 r0 hy2 hy0)))
      have m1 : (SY V).toLogic.Ctx [(SY V).eq y r2, (SY V).eq x r1, (SY V).mem x y] ((SY V).mem r1 y) :=
        .mp ex1 (.mp mxy (.thm ((SY V).h3 x y r1)))
      have m2 : (SY V).toLogic.Ctx [(SY V).eq y r2, (SY V).eq x r1, (SY V).mem x y] ((SY V).mem r1 r2) :=
        .mp m1 (.mp ey2 (.thm ((SY V).h4 y r2 r1)))
      exact Ctx.andIntro (Ctx.andIntro c1 c2) m2
    have i1 : (SY V).toLogic.Ctx [(SY V).eq x r1, (SY V).mem x y] ((SY V).ex r2 B) := by
      refine Ctx.exMp r2 (i2.deduction.generalize r2 fun h hh => ?_) (.thm ((SY V).h5 r2 y))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl
      · exact (SY V).eqVacuity x r1 r2 (Ne.symm hx2) (Ne.symm h12)
      · exact (SY V).memVacuity x y r2 (Ne.symm hx2) (Ne.symm hy2)
    refine Ctx.exMp r1 (i1.deduction.generalize r1 fun h hh => ?_) (.thm ((SY V).h5 r1 x))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl
    exact (SY V).memVacuity x y r1 (Ne.symm hx1) (Ne.symm hy1)
  -- backward
  have core : (SY V).Prov ((SY V).imp B ((SY V).mem x y)) := by
    have H : (SY V).toLogic.Ctx [B] B := Ctx.head
    -- x ∈ r₂ from r₁ ∈ r₂ and the second conjunct of x ≈ r₁, used at r₂
    have tA : (SY V).Prov ((SY V).all r0 ((SY V).imp ((SY V).mem r1 r2) ((SY V).imp ((SY V).iff ((SY V).mem x r0) ((SY V).mem r1 r0))
        ((SY V).imp ((SY V).eq r2 r0) ((SY V).mem x r2))))) := by
      refine (SY V).gen r0 ?_
      have c : (SY V).toLogic.Ctx [(SY V).eq r2 r0, (SY V).iff ((SY V).mem x r0) ((SY V).mem r1 r0), (SY V).mem r1 r2]
          ((SY V).mem x r2) := by
        have e : (SY V).toLogic.Ctx [(SY V).eq r2 r0, (SY V).iff ((SY V).mem x r0) ((SY V).mem r1 r0), (SY V).mem r1 r2]
            ((SY V).eq r2 r0) := Ctx.head
        have m0 := Ctx.mp (.hyp (by simp)) (Ctx.mp e (.thm ((SY V).h4 r2 r0 r1)))
        have hi : (SY V).toLogic.Ctx [(SY V).eq r2 r0, (SY V).iff ((SY V).mem x r0) ((SY V).mem r1 r0),
            (SY V).mem r1 r2] ((SY V).iff ((SY V).mem x r0) ((SY V).mem r1 r0)) := .hyp (by simp)
        have mx0 := Ctx.iffMpr hi m0
        exact Ctx.mp mx0 (Ctx.mp e (.thm (rawIn r2 r0 x (Ne.symm h02) (Ne.symm hx2))))
      exact c.deduction.deduction.deduction.empty
    have am : (SY V).toLogic.Ctx [B] ((SY V).all r0 ((SY V).mem r1 r2)) :=
      .mp H.andRight (.thm ((SY V).memVacuity r1 r2 r0 h01 h02))
    have mxr2 : (SY V).toLogic.Ctx [B] ((SY V).mem x r2) :=
      Ctx.existsElim r0 ((SY V).memVacuity x r2 r0 (Ne.symm hx0) h02)
        (Ctx.forallMp r0 H.andLeft.andLeft.andRight (Ctx.forallMp r0 am (.thm tA)))
        (.thm ((SY V).h5 r0 r2))
    -- x ∈ y from x ∈ r₂ and the first conjunct of y ≈ r₂, used at x
    have tB : (SY V).Prov ((SY V).all r0 ((SY V).imp ((SY V).mem x r2) ((SY V).imp ((SY V).iff ((SY V).mem r0 y) ((SY V).mem r0 r2))
        ((SY V).imp ((SY V).eq x r0) ((SY V).mem x y))))) := by
      refine (SY V).gen r0 ?_
      have c : (SY V).toLogic.Ctx [(SY V).eq x r0, (SY V).iff ((SY V).mem r0 y) ((SY V).mem r0 r2), (SY V).mem x r2]
          ((SY V).mem x y) := by
        have e : (SY V).toLogic.Ctx [(SY V).eq x r0, (SY V).iff ((SY V).mem r0 y) ((SY V).mem r0 r2), (SY V).mem x r2]
            ((SY V).eq x r0) := Ctx.head
        have m02 := Ctx.mp e (Ctx.mp (.hyp (by simp)) (.thm ((SY V).h3 x r2 r0)))
        have hi : (SY V).toLogic.Ctx [(SY V).eq x r0, (SY V).iff ((SY V).mem r0 y) ((SY V).mem r0 r2),
            (SY V).mem x r2] ((SY V).iff ((SY V).mem r0 y) ((SY V).mem r0 r2)) := .hyp (by simp)
        have m0y := Ctx.iffMpr hi m02
        exact Ctx.mp m0y (Ctx.mp e (.thm (rawOut x r0 y hx0 hxy)))
      exact c.deduction.deduction.deduction.empty
    have am' : (SY V).toLogic.Ctx [B] ((SY V).all r0 ((SY V).mem x r2)) :=
      .mp mxr2 (.thm ((SY V).memVacuity x r2 r0 (Ne.symm hx0) h02))
    exact (Ctx.existsElim r0 ((SY V).memVacuity x y r0 (Ne.symm hx0) (Ne.symm hy0))
      (Ctx.forallMp r0 H.andLeft.andRight.andLeft (Ctx.forallMp r0 am' (.thm tB)))
      (.thm ((SY V).h5 r0 x))).deduction.empty
  have bw2c : (SY V).toLogic.Ctx [(SY V).ex r2 B] ((SY V).mem x y) :=
    Ctx.existsElim r2 ((SY V).memVacuity x y r2 (Ne.symm hx2) (Ne.symm hy2))
      (.thm ((SY V).gen r2 core)) Ctx.head
  have bw2 : (SY V).Prov ((SY V).imp ((SY V).ex r2 B) ((SY V).mem x y)) := bw2c.deduction.empty
  have bw : (SY V).toLogic.Ctx [(SY V).ex r1 ((SY V).ex r2 B)] ((SY V).mem x y) :=
    Ctx.existsElim r1 ((SY V).memVacuity x y r1 (Ne.symm hx1) (Ne.symm hy1))
      (.thm ((SY V).gen r1 bw2)) Ctx.head
  have : (SY V).Prov ((SY V).iff ((SY V).mem x y) ((SY V).ex r1 ((SY V).ex r2 B))) := (Ctx.iffIntro fw bw).empty
  rw [atomL_one_sys]
  exact this

end ZF209.Halting
