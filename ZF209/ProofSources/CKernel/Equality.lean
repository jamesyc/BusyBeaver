module
public import CKernel.Generic
@[expose] public section
/-! # Equality in the machine's calculus

The heads transport membership forward along primitive equality only. The
pointed gate gives the backward direction: to show `a = b → w ∈ b → w ∈ a`,
assume `w ∉ a` and take the hull `C` of the relation `R z := w ∉ z` (the gate's
own label is the code of `R`). Then `a ∈ C`, hence `b ∈ C`; every member of `C`
omits `w`, and a witness `z` with `b = z` carries both `b ∈ C` and `w ∈ b`
forward to `z`, a contradiction. Only forward transport is ever used.

With both directions, primitive equality implies the defined equality
`ceq z a b := ∀z (z ∈ a ↔ z ∈ b) ∧ ∀z (a ∈ z ↔ b ∈ z)`, which is symmetric
and transitive by pure quantifier reasoning; this gives `EqLogic`. -/
namespace ZF209.CKernel.Generic

universe u

namespace Codes
variable {X : Type u} (K : Codes X)

/-- The defined equality, binding `z`. -/
def ceq (z a b : X) : X :=
  K.and (K.all z (K.iff (K.mem z a) (K.mem z b))) (K.all z (K.iff (K.mem a z) (K.mem b z)))

/-- The relations whose hulls give backward transport. -/
def relIn (a b w : X) : X := K.and (K.neg (K.mem w a)) (K.imp (K.mem b b) (K.mem b b))
def relOut (a b w : X) : X := K.and (K.neg (K.mem a w)) (K.imp (K.mem b b) (K.mem b b))

/-- The body of the gate's hull condition. -/
def hullBody (A D H : X) : X :=
  K.imp (K.all A (K.imp (K.mem A D) (K.mem A H)))
    (K.all H (K.imp A (K.neg (K.all H (K.imp A (K.neg (K.mem H A)))))))

lemma gateBody_eq (A D H : X) : K.gateBody A D H =
    K.imp (K.all H (K.imp (K.mem H A) (K.neg (K.all D (K.imp A (K.neg (K.all D
      (K.hullBody A D H))))))))
      (K.neg (K.imp A (K.mem H A))) := rfl

end Codes

namespace Sys
variable {X : Type u} (S : Sys X)
open Logic

/-- The gate without its vacuity parts. -/
theorem notQGate (a b c : X) (hca : c ≠ a) (hcb : c ≠ b) :
    S.Prov (S.neg (S.qGate a b c)) := by
  have g : S.toLogic.Ctx [] (S.bundle a b c) := .thm (S.gate a b c hca hcb)
  have hq : S.toLogic.Ctx [S.qGate a b c]
      (S.imp (S.eqVac a b c) (S.imp (S.memVac a b c) (S.qGate a b c))) :=
    (Ctx.head.lift _).lift _
  exact (Ctx.mp hq (g.up _)).deduction.empty

/-- Members of a hull satisfy the relation, when the relation does not mention
the gate's second label. -/
theorem hull_proj (a β R : X) (hR : S.Prov (S.imp R (S.all β R))) (Z : X) :
    S.Prov (S.imp (S.all a (S.imp (S.mem a R) (S.neg (S.all β (S.imp R (S.neg Z))))))
      (S.all a (S.imp (S.mem a R) R))) := by
  have hn : S.Prov (S.imp (S.neg R) (S.all β (S.neg R))) := S.toLogic.negationVacuity β R hR
  have hk : S.Prov (S.imp (S.all β (S.neg R)) (S.all β (S.imp R (S.neg Z)))) := by
    refine S.toLogic.liftImp β ?_
    have c : S.toLogic.Ctx [R, S.neg R] (S.neg Z) := (Ctx.mp Ctx.head (Ctx.head.up _)).explosion _
    exact c.deduction.deduction.empty
  have hq : S.Prov (S.imp (S.neg (S.all β (S.imp R (S.neg Z)))) R) := by
    have c : S.toLogic.Ctx [S.neg R, S.neg (S.all β (S.imp R (S.neg Z)))] S.bot :=
      Ctx.mp (Ctx.mp (Ctx.mp Ctx.head (.thm hn)) (.thm hk)) (Ctx.head.up _)
    exact c.deduction.dne.deduction.empty
  refine S.toLogic.liftImp a ?_
  have c : S.toLogic.Ctx [S.mem a R, S.imp (S.mem a R) (S.neg (S.all β (S.imp R (S.neg Z))))] R :=
    .mp (.mp Ctx.head (Ctx.head.up _)) (.thm hq)
  exact c.deduction.deduction.empty

/-- Using a hull: inside the hull's scope, its members satisfy `R` and `a ∈ C`
follows from `R`. The label `R` (the code of the relation) must differ from `a`
and `β`, and the context and goal must not mention it. -/
theorem hull_elim {a β R G : X} {Γ : List X} (hca : R ≠ a) (hcb : R ≠ β)
    (hR : S.Prov (S.imp R (S.all β R)))
    (hvac : ∀ h, h ∈ Γ → S.Prov (S.imp h (S.all R h)))
    (hG : S.Prov (S.imp G (S.all R G)))
    (body : S.toLogic.Ctx (S.imp R (S.mem a R) :: S.all a (S.imp (S.mem a R) R) :: Γ) G) :
    S.toLogic.Ctx Γ G := by
  have hb : S.toLogic.Ctx (S.imp R (S.mem a R) ::
      S.all a (S.imp (S.mem a R) (S.neg (S.all β (S.imp R (S.neg (S.all β
        (S.hullBody R β a))))))) :: S.neg G :: Γ) S.bot := by
    have hp : S.toLogic.Ctx (S.imp R (S.mem a R) ::
        S.all a (S.imp (S.mem a R) (S.neg (S.all β (S.imp R (S.neg (S.all β
          (S.hullBody R β a))))))) :: S.neg G :: Γ) (S.all a (S.imp (S.mem a R) R)) :=
      .mp (Ctx.head.up _) (.thm (S.hull_proj a β R hR _))
    have hg : S.toLogic.Ctx (S.imp R (S.mem a R) ::
        S.all a (S.imp (S.mem a R) (S.neg (S.all β (S.imp R (S.neg (S.all β
          (S.hullBody R β a))))))) :: S.neg G :: Γ) G :=
      body.cut fun h hh => by
        rcases List.mem_cons.mp hh with rfl | hh
        · exact Ctx.head
        rcases List.mem_cons.mp hh with rfl | hh
        · exact hp
        · exact .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hh)))
    exact .mp hg ((Ctx.head.up _).up _)
  have hgb : S.toLogic.Ctx (S.neg G :: Γ) (S.gateBody R β a) := by
    rw [Codes.gateBody_eq]; exact hb.deduction.deduction
  have hq : S.toLogic.Ctx (S.neg G :: Γ) (S.qGate a β R) :=
    hgb.generalize R fun h hh => by
      rcases List.mem_cons.mp hh with rfl | hh
      · exact S.toLogic.negationVacuity R G hG
      · exact hvac h hh
  exact Ctx.byContra (.mp hq (.thm (S.notQGate a β R hca hcb)))

/-- A member of a hull omitting `w` from all members cannot contain `w`. -/
theorem hull_omits_in (a b w C : X) (hab : a ≠ b) (haw : a ≠ w) (haC : a ≠ C) :
    S.Prov (S.imp (S.all a (S.imp (S.mem a C) (S.neg (S.mem w a))))
      (S.imp (S.mem b C) (S.imp (S.mem w b) S.bot))) := by
  have t : S.Prov (S.imp (S.mem b C) (S.imp (S.mem w b)
      (S.imp (S.imp (S.mem a C) (S.neg (S.mem w a))) (S.imp (S.eq b a) S.bot)))) := by
    have c : S.toLogic.Ctx [S.eq b a, S.imp (S.mem a C) (S.neg (S.mem w a)), S.mem w b,
        S.mem b C] S.bot := by
      have h1 : S.toLogic.Ctx [S.eq b a, S.imp (S.mem a C) (S.neg (S.mem w a)), S.mem w b,
          S.mem b C] (S.mem a C) := .mp Ctx.head (.mp (((Ctx.head.up _).up _).up _) (.thm (S.h3 b C a)))
      have h2 : S.toLogic.Ctx [S.eq b a, S.imp (S.mem a C) (S.neg (S.mem w a)), S.mem w b,
          S.mem b C] (S.mem w a) := .mp ((Ctx.head.up _).up _) (.mp Ctx.head (.thm (S.h4 b a w)))
      exact .mp h2 (.mp h1 (Ctx.head.up _))
    exact c.deduction.deduction.deduction.deduction.empty
  have c : S.toLogic.Ctx [S.mem w b, S.mem b C, S.all a (S.imp (S.mem a C) (S.neg (S.mem w a)))]
      S.bot := by
    have g : S.toLogic.Ctx [S.mem w b, S.mem b C, S.all a (S.imp (S.mem a C) (S.neg (S.mem w a)))]
        _ := .thm (S.gen a t)
    have v1 : S.toLogic.Ctx [S.mem w b, S.mem b C, S.all a (S.imp (S.mem a C) (S.neg (S.mem w a)))]
        (S.all a (S.mem b C)) := .mp (Ctx.head.up _) (.thm (S.memVacuity b C a hab haC))
    have v2 : S.toLogic.Ctx [S.mem w b, S.mem b C, S.all a (S.imp (S.mem a C) (S.neg (S.mem w a)))]
        (S.all a (S.mem w b)) := .mp Ctx.head (.thm (S.memVacuity w b a haw hab))
    have g3 := Ctx.forallMp a ((Ctx.head.up _).up _) (Ctx.forallMp a v2 (Ctx.forallMp a v1 g))
    exact Ctx.existsElim a (S.toLogic.botVacuity a) g3 (.thm (S.h5 a b))
  exact c.deduction.deduction.deduction.empty

/-- A member of a hull whose members are all outside `w` is not in `w`. -/
theorem hull_omits_out (a b w C : X) (hab : a ≠ b) (haw : a ≠ w) (haC : a ≠ C) :
    S.Prov (S.imp (S.all a (S.imp (S.mem a C) (S.neg (S.mem a w))))
      (S.imp (S.mem b C) (S.imp (S.mem b w) S.bot))) := by
  have t : S.Prov (S.imp (S.mem b C) (S.imp (S.mem b w)
      (S.imp (S.imp (S.mem a C) (S.neg (S.mem a w))) (S.imp (S.eq b a) S.bot)))) := by
    have c : S.toLogic.Ctx [S.eq b a, S.imp (S.mem a C) (S.neg (S.mem a w)), S.mem b w,
        S.mem b C] S.bot := by
      have h1 : S.toLogic.Ctx [S.eq b a, S.imp (S.mem a C) (S.neg (S.mem a w)), S.mem b w,
          S.mem b C] (S.mem a C) := .mp Ctx.head (.mp (((Ctx.head.up _).up _).up _) (.thm (S.h3 b C a)))
      have h2 : S.toLogic.Ctx [S.eq b a, S.imp (S.mem a C) (S.neg (S.mem a w)), S.mem b w,
          S.mem b C] (S.mem a w) := .mp Ctx.head (.mp ((Ctx.head.up _).up _) (.thm (S.h3 b w a)))
      exact .mp h2 (.mp h1 (Ctx.head.up _))
    exact c.deduction.deduction.deduction.deduction.empty
  have c : S.toLogic.Ctx [S.mem b w, S.mem b C, S.all a (S.imp (S.mem a C) (S.neg (S.mem a w)))]
      S.bot := by
    have g : S.toLogic.Ctx [S.mem b w, S.mem b C, S.all a (S.imp (S.mem a C) (S.neg (S.mem a w)))]
        _ := .thm (S.gen a t)
    have v1 : S.toLogic.Ctx [S.mem b w, S.mem b C, S.all a (S.imp (S.mem a C) (S.neg (S.mem a w)))]
        (S.all a (S.mem b C)) := .mp (Ctx.head.up _) (.thm (S.memVacuity b C a hab haC))
    have v2 : S.toLogic.Ctx [S.mem b w, S.mem b C, S.all a (S.imp (S.mem a C) (S.neg (S.mem a w)))]
        (S.all a (S.mem b w)) := .mp Ctx.head (.thm (S.memVacuity b w a hab haw))
    have g3 := Ctx.forallMp a ((Ctx.head.up _).up _) (Ctx.forallMp a v2 (Ctx.forallMp a v1 g))
    exact Ctx.existsElim a (S.toLogic.botVacuity a) g3 (.thm (S.h5 a b))
  exact c.deduction.deduction.deduction.empty

lemma relIn_vac {a b w β : X} (hw : β ≠ w) (ha : β ≠ a) (hb : β ≠ b) :
    S.Prov (S.imp (S.relIn a b w) (S.all β (S.relIn a b w))) :=
  S.toLogic.andVacuity β _ _ (S.toLogic.negationVacuity β _ (S.memVacuity w a β hw ha))
    (S.toLogic.implicationVacuity β _ _ (S.memVacuity b b β hb hb) (S.memVacuity b b β hb hb))

lemma relOut_vac {a b w β : X} (hw : β ≠ w) (ha : β ≠ a) (hb : β ≠ b) :
    S.Prov (S.imp (S.relOut a b w) (S.all β (S.relOut a b w))) :=
  S.toLogic.andVacuity β _ _ (S.toLogic.negationVacuity β _ (S.memVacuity a w β ha hw))
    (S.toLogic.implicationVacuity β _ _ (S.memVacuity b b β hb hb) (S.memVacuity b b β hb hb))

/-- Backward transport into a member position. The gate's labels are the code
`c` of `relIn a b w` and a label `β` foreign to it. -/
theorem backIn (a b w β : X) (hab : a ≠ b) (haw : a ≠ w)
    (hca : S.relIn a b w ≠ a) (hcb : S.relIn a b w ≠ b) (hcw : S.relIn a b w ≠ w)
    (hcβ : S.relIn a b w ≠ β) (hβa : β ≠ a) (hβb : β ≠ b) (hβw : β ≠ w) :
    S.Prov (S.imp (S.eq a b) (S.imp (S.mem w b) (S.mem w a))) := by
  set R := S.relIn a b w
  have body : S.toLogic.Ctx (S.imp R (S.mem a R) :: S.all a (S.imp (S.mem a R) R) ::
      [S.neg (S.mem w a), S.mem w b, S.eq a b]) S.bot := by
    have hR : S.toLogic.Ctx (S.imp R (S.mem a R) :: S.all a (S.imp (S.mem a R) R) ::
        [S.neg (S.mem w a), S.mem w b, S.eq a b]) R :=
      Ctx.andIntro ((Ctx.head.up _).up _) (.thm (S.toLogic.identity _))
    have haR := Ctx.mp hR Ctx.head
    have hbR : S.toLogic.Ctx (S.imp R (S.mem a R) :: S.all a (S.imp (S.mem a R) R) ::
        [S.neg (S.mem w a), S.mem w b, S.eq a b]) (S.mem b R) :=
      .mp ((((Ctx.head.up _).up _).up _).up _) (.mp haR (.thm (S.h3 a R b)))
    have proj : S.Prov (S.imp (S.imp (S.mem a R) R) (S.imp (S.mem a R) (S.neg (S.mem w a)))) := by
      have c : S.toLogic.Ctx [S.mem a R, S.imp (S.mem a R) R] (S.neg (S.mem w a)) :=
        (Ctx.mp Ctx.head (Ctx.head.up _)).andLeft
      exact c.deduction.deduction.empty
    have hall : S.toLogic.Ctx (S.imp R (S.mem a R) :: S.all a (S.imp (S.mem a R) R) ::
        [S.neg (S.mem w a), S.mem w b, S.eq a b])
        (S.all a (S.imp (S.mem a R) (S.neg (S.mem w a)))) :=
      .mp (Ctx.head.up _) (.thm (S.toLogic.liftImp a proj))
    exact .mp (((Ctx.head.up _).up _).up _) (.mp hbR (.mp hall (.thm (S.hull_omits_in a b w R hab haw hca.symm))))
  have h := S.hull_elim hca hcβ (S.relIn_vac hβw hβa hβb) (Γ := [S.neg (S.mem w a), S.mem w b, S.eq a b])
    (fun h hh => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl | rfl
      · exact S.toLogic.negationVacuity R _ (S.memVacuity w a R hcw hca)
      · exact S.memVacuity w b R hcw hcb
      · exact S.eqVacuity a b R hca hcb)
    (S.toLogic.botVacuity R) body
  exact (Ctx.byContra h).deduction.deduction.empty

/-- Backward transport out of a member position. -/
theorem backOut (a b w β : X) (hab : a ≠ b) (haw : a ≠ w)
    (hca : S.relOut a b w ≠ a) (hcb : S.relOut a b w ≠ b) (hcw : S.relOut a b w ≠ w)
    (hcβ : S.relOut a b w ≠ β) (hβa : β ≠ a) (hβb : β ≠ b) (hβw : β ≠ w) :
    S.Prov (S.imp (S.eq a b) (S.imp (S.mem b w) (S.mem a w))) := by
  set R := S.relOut a b w
  have body : S.toLogic.Ctx (S.imp R (S.mem a R) :: S.all a (S.imp (S.mem a R) R) ::
      [S.neg (S.mem a w), S.mem b w, S.eq a b]) S.bot := by
    have hR : S.toLogic.Ctx (S.imp R (S.mem a R) :: S.all a (S.imp (S.mem a R) R) ::
        [S.neg (S.mem a w), S.mem b w, S.eq a b]) R :=
      Ctx.andIntro ((Ctx.head.up _).up _) (.thm (S.toLogic.identity _))
    have haR := Ctx.mp hR Ctx.head
    have hbR : S.toLogic.Ctx (S.imp R (S.mem a R) :: S.all a (S.imp (S.mem a R) R) ::
        [S.neg (S.mem a w), S.mem b w, S.eq a b]) (S.mem b R) :=
      .mp ((((Ctx.head.up _).up _).up _).up _) (.mp haR (.thm (S.h3 a R b)))
    have proj : S.Prov (S.imp (S.imp (S.mem a R) R) (S.imp (S.mem a R) (S.neg (S.mem a w)))) := by
      have c : S.toLogic.Ctx [S.mem a R, S.imp (S.mem a R) R] (S.neg (S.mem a w)) :=
        (Ctx.mp Ctx.head (Ctx.head.up _)).andLeft
      exact c.deduction.deduction.empty
    have hall : S.toLogic.Ctx (S.imp R (S.mem a R) :: S.all a (S.imp (S.mem a R) R) ::
        [S.neg (S.mem a w), S.mem b w, S.eq a b])
        (S.all a (S.imp (S.mem a R) (S.neg (S.mem a w)))) :=
      .mp (Ctx.head.up _) (.thm (S.toLogic.liftImp a proj))
    exact .mp (((Ctx.head.up _).up _).up _) (.mp hbR (.mp hall (.thm (S.hull_omits_out a b w R hab haw hca.symm))))
  have h := S.hull_elim hca hcβ (S.relOut_vac hβw hβa hβb) (Γ := [S.neg (S.mem a w), S.mem b w, S.eq a b])
    (fun h hh => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl | rfl
      · exact S.toLogic.negationVacuity R _ (S.memVacuity a w R hca hcw)
      · exact S.memVacuity b w R hcb hcw
      · exact S.eqVacuity a b R hca hcb)
    (S.toLogic.botVacuity R) body
  exact (Ctx.byContra h).deduction.deduction.empty

/-! ## The defined equality -/

/-- Primitive equality implies the defined one, given backward transport. -/
theorem eq_ceq {z a b : X} (hza : z ≠ a) (hzb : z ≠ b)
    (hin : S.Prov (S.imp (S.eq a b) (S.imp (S.mem z b) (S.mem z a))))
    (hout : S.Prov (S.imp (S.eq a b) (S.imp (S.mem b z) (S.mem a z)))) :
    S.Prov (S.imp (S.eq a b) (S.ceq z a b)) := by
  have v : ∀ h, h ∈ [S.eq a b] → S.Prov (S.imp h (S.all z h)) := fun h hh => by
    rw [List.mem_singleton.mp hh]; exact S.eqVacuity a b z hza hzb
  have i1 : S.toLogic.Ctx [S.eq a b] (S.iff (S.mem z a) (S.mem z b)) :=
    Ctx.iffIntro (.mp Ctx.head (.mp (Ctx.head.up _) (.thm (S.h4 a b z))))
      (.mp Ctx.head (.mp (Ctx.head.up _) (.thm hin)))
  have i2 : S.toLogic.Ctx [S.eq a b] (S.iff (S.mem a z) (S.mem b z)) :=
    Ctx.iffIntro (.mp (Ctx.head.up _) (.mp Ctx.head (.thm (S.h3 a z b))))
      (.mp Ctx.head (.mp (Ctx.head.up _) (.thm hout)))
  exact (Ctx.andIntro (i1.generalize z v) (i2.generalize z v)).deduction.empty

/-- The defined equality is symmetric. -/
theorem ceq_symm (z a b : X) : S.Prov (S.imp (S.ceq z a b) (S.ceq z b a)) := by
  have sw : ∀ p q : X, S.Prov (S.imp (S.all z (S.iff p q)) (S.all z (S.iff q p))) := fun p q =>
    S.toLogic.liftImp z (Ctx.iffSymm (S := S.toLogic) (Γ := [S.iff p q]) Ctx.head).deduction.empty
  have c : S.toLogic.Ctx [S.ceq z a b] (S.ceq z b a) :=
    Ctx.andIntro (.mp Ctx.head.andLeft (.thm (sw _ _))) (.mp Ctx.head.andRight (.thm (sw _ _)))
  exact c.deduction.empty

/-- The defined equality is transitive. -/
theorem ceq_trans (z a b d : X) :
    S.Prov (S.imp (S.ceq z a b) (S.imp (S.ceq z b d) (S.ceq z a d))) := by
  have tr : ∀ p q r : X, S.Prov (S.imp (S.all z (S.iff p q))
      (S.imp (S.all z (S.iff q r)) (S.all z (S.iff p r)))) := fun p q r => by
    have t : S.Prov (S.imp (S.iff p q) (S.imp (S.iff q r) (S.iff p r))) :=
      (Ctx.iffTrans (S := S.toLogic) (Γ := [S.iff q r, S.iff p q]) (Ctx.head.up _) Ctx.head
        |>.deduction.deduction.empty)
    have c : S.toLogic.Ctx [S.all z (S.iff q r), S.all z (S.iff p q)] (S.all z (S.iff p r)) :=
      Ctx.forallMp z Ctx.head (Ctx.forallMp z (Ctx.head.up _) (.thm (S.gen z t)))
    exact c.deduction.deduction.empty
  have c : S.toLogic.Ctx [S.ceq z b d, S.ceq z a b] (S.ceq z a d) :=
    Ctx.andIntro (.mp (Ctx.head.andLeft) (.mp (Ctx.head.up _).andLeft (.thm (tr _ _ _))))
      (.mp (Ctx.head.andRight) (.mp (Ctx.head.up _).andRight (.thm (tr _ _ _))))
  exact c.deduction.deduction.empty

/-- The defined equality is vacuous in labels other than its arguments and `z`. -/
theorem ceq_vac {z a b c : X} (hz : c ≠ z) (ha : c ≠ a) (hb : c ≠ b) :
    S.Prov (S.imp (S.ceq z a b) (S.all c (S.ceq z a b))) :=
  S.toLogic.andVacuity c _ _
    (S.toLogic.universalVacuity c z _ (S.toLogic.iffVacuity c _ _
      (S.memVacuity z a c hz ha) (S.memVacuity z b c hz hb)))
    (S.toLogic.universalVacuity c z _ (S.toLogic.iffVacuity c _ _
      (S.memVacuity a z c ha hz) (S.memVacuity b z c hb hz)))

/-- The calculus with the defined equality, given backward transport for
distinct labels. -/
def toEqLogic (z : X)
    (hin : ∀ a b w, a ≠ b → a ≠ w → b ≠ w →
      S.Prov (S.imp (S.eq a b) (S.imp (S.mem w b) (S.mem w a))))
    (hout : ∀ a b w, a ≠ b → a ≠ w → b ≠ w →
      S.Prov (S.imp (S.eq a b) (S.imp (S.mem b w) (S.mem a w)))) : EqLogic X where
  toLogic := S.toLogic
  E := S.ceq z
  ok x := x ≠ z
  witness x y hxy hx hy := by
    have h : S.Prov (S.imp (S.eq y x) (S.ceq z y x)) :=
      S.eq_ceq (Ne.symm hy) (Ne.symm hx) (hin y x z hxy.symm hy hx) (hout y x z hxy.symm hy hx)
    exact S.mp (S.h5 x y) (S.toLogic.existsMono x h)
  eVac a b c hca hcb _ _ hc := S.ceq_vac hc hca hcb
  memVac := S.memVacuity
  eSymm a b _ _ := S.ceq_symm z a b
  eTrans a b d _ _ _ := S.ceq_trans z a b d

end Sys

end ZF209.CKernel.Generic
