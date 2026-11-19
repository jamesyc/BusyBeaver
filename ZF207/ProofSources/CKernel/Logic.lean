module
public import Mathlib.Data.List.Basic
@[expose] public section
/-! # A portable first-order calculus over an abstract code algebra

`Logic X` packages a provability predicate on a type of codes `X` closed under
modus ponens, generalization, the propositional axioms K, S and Peirce, and the
quantifier axioms: distribution, commutation and `∃x∀x a → a`. Every lemma here
is a fixed proof scheme whose parameters range over `X`, so it holds for
nonstandard codes as well. `EqLogic X` adds the equality witness `∃x (y = x)`,
vacuity of atoms in labels they do not mention, and congruence of atoms under
primitive equality. -/
namespace ZF207.CKernel.Generic

universe u

/-- The code constructors. `all x a` quantifies label `x` in `a`. -/
structure Codes (X : Type u) where
  imp : X → X → X
  mem : X → X → X
  eq : X → X → X
  all : X → X → X
  bot : X

namespace Codes
variable {X : Type u} (K : Codes X)

def neg (a : X) : X := K.imp a K.bot
def and (a b : X) : X := K.neg (K.imp a (K.neg b))
def or (a b : X) : X := K.imp (K.neg a) b
def ex (x a : X) : X := K.neg (K.all x (K.neg a))
def iff (a b : X) : X := K.and (K.imp a b) (K.imp b a)

def head1 (d h : X) : X := K.imp (K.ex d (K.all d h)) h
def head2 (d a h : X) : X := K.imp (K.all d (K.all a h)) (K.all a (K.all d h))
def head3 (h d a : X) : X := K.imp (K.mem h d) (K.imp (K.eq h a) (K.mem a d))
def head4 (h d a : X) : X := K.imp (K.eq h d) (K.imp (K.mem a h) (K.mem a d))
def head5 (d h : X) : X := K.ex d (K.eq h d)
def head6 (d a h : X) : X := K.imp (K.all d a) (K.imp (K.all d (K.imp a h)) (K.all d h))
def rho8 (a b c u : X) : X := K.imp (K.imp (K.imp c u) a) (K.imp (K.imp a c) (K.imp b c))

def eqVac (a b c : X) : X := K.imp (K.eq a b) (K.all c (K.eq a b))
def memVac (a b c : X) : X := K.imp (K.mem a b) (K.all c (K.mem a b))
/-- The body of the pointed Scott-hull gate. -/
def gateBody (a d h : X) : X :=
  K.imp (K.all h (K.imp (K.mem h a) (K.imp (K.all d (K.imp a (K.imp (K.all d (K.imp
    (K.all a (K.imp (K.mem a d) (K.mem a h))) (K.all h (K.imp a (K.imp (K.all h (K.imp a
    (K.imp (K.mem h a) K.bot))) K.bot))))) K.bot))) K.bot))) (K.imp (K.imp a (K.mem h a)) K.bot)
def qGate (a b c : X) : X := K.all c (K.gateBody c b a)
/-- The machine's gate instance; label `c` must differ from `a` and `b`. -/
def bundle (a b c : X) : X := K.neg (K.imp (K.eqVac a b c) (K.imp (K.memVac a b c) (K.qGate a b c)))

end Codes

/-- A calculus with the propositional and quantifier rules. -/
structure Logic (X : Type u) extends Codes X where
  Prov : X → Prop
  mp {a b : X} : Prov a → Prov (imp a b) → Prov b
  gen (x : X) {a : X} : Prov a → Prov (all x a)
  k (a b : X) : Prov (imp a (imp b a))
  s (a b c : X) : Prov (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  peirce (a b : X) : Prov (imp (imp (imp a b) a) a)
  r2 (d a h : X) : Prov (imp (all d (imp a h)) (imp (all d a) (all d h)))
  h1 (d h : X) : Prov (toCodes.head1 d h)
  h2 (d a h : X) : Prov (toCodes.head2 d a h)

namespace Logic
variable {X : Type u} (S : Logic X)

local infixr:60 " ⟹ " => S.imp

theorem identity (a : X) : S.Prov (a ⟹ a) :=
  S.mp (S.k a a) (S.mp (S.k a (a ⟹ a)) (S.s a (a ⟹ a) a))

/-! ## Finite contexts and the deduction theorem -/

/-- Provability from a finite list of hypotheses, without generalization. -/
inductive Ctx (Γ : List X) : X → Prop
  | hyp {a : X} : a ∈ Γ → Ctx Γ a
  | thm {a : X} : S.Prov a → Ctx Γ a
  | mp {a b : X} : Ctx Γ a → Ctx Γ (S.imp a b) → Ctx Γ b

variable {S}

theorem Ctx.cut {Γ Δ : List X} {a : X} (d : S.Ctx Γ a)
    (h : ∀ b, b ∈ Γ → S.Ctx Δ b) : S.Ctx Δ a := by
  induction d with
  | hyp hb => exact h _ hb
  | thm p => exact .thm p
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂

theorem Ctx.close {Γ : List X} {a : X} (d : S.Ctx Γ a) (h : ∀ b, b ∈ Γ → S.Prov b) :
    S.Prov a := by
  induction d with
  | hyp hb => exact h _ hb
  | thm p => exact p
  | mp _ _ ih₁ ih₂ => exact S.mp ih₁ ih₂

theorem Ctx.empty {a : X} (d : S.Ctx [] a) : S.Prov a :=
  d.close fun _ h => absurd h (List.not_mem_nil)

theorem Ctx.lift {Γ : List X} {a : X} (d : S.Ctx Γ a) (h : X) : S.Ctx Γ (S.imp h a) :=
  .mp d (.thm (S.k a h))

theorem Ctx.head {Γ : List X} {a : X} : S.Ctx (a :: Γ) a := .hyp List.mem_cons_self

theorem Ctx.up {Γ : List X} {a : X} (p : S.Ctx Γ a) (h : X) : S.Ctx (h :: Γ) a :=
  p.cut fun _ hb => .hyp (List.mem_cons_of_mem h hb)

theorem Ctx.deduction {Γ : List X} {h a : X} (d : S.Ctx (h :: Γ) a) :
    S.Ctx Γ (S.imp h a) := by
  classical
  induction d with
  | @hyp a ha =>
    by_cases e : a = h
    · subst e; exact .thm (S.identity a)
    · exact (Ctx.hyp ((List.mem_cons.mp ha).resolve_left e)).lift h
  | thm p => exact (Ctx.thm p).lift h
  | @mp b a _ _ ih₁ ih₂ => exact .mp ih₁ (.mp ih₂ (.thm (S.s h b a)))

variable (S)

theorem explosion (a : X) : S.Prov (S.bot ⟹ a) := by
  have h : S.Ctx [S.bot] (S.imp (S.ex S.bot (S.all S.bot a)) a) := .thm (S.h1 S.bot a)
  have hb : S.Ctx [S.bot] S.bot := .hyp (by simp)
  have hk : S.Ctx [S.bot] (S.ex S.bot (S.all S.bot a)) :=
    .mp hb (.thm (S.k S.bot (S.all S.bot (S.neg (S.all S.bot a)))))
  exact (Ctx.mp hk h).deduction.empty

variable {S}

theorem Ctx.explosion {Γ : List X} (a : X) (d : S.Ctx Γ S.bot) : S.Ctx Γ a :=
  .mp d (.thm (S.explosion a))

variable (S)

theorem dne (a : X) : S.Prov (S.neg (S.neg a) ⟹ a) := by
  have p : S.Ctx [S.neg a, S.neg (S.neg a)] (S.neg a) := .hyp (by simp)
  have q : S.Ctx [S.neg a, S.neg (S.neg a)] (S.neg (S.neg a)) := .hyp (by simp)
  have c : S.Ctx [S.neg (S.neg a)] (S.imp (S.neg a) a) :=
    ((Ctx.mp p q).explosion a).deduction
  exact (Ctx.mp c (.thm (S.peirce a S.bot))).deduction.empty

theorem exchange (a b c : X) : S.Prov ((a ⟹ b ⟹ c) ⟹ b ⟹ a ⟹ c) := by
  have pa : S.Ctx [a, b, a ⟹ b ⟹ c] a := .hyp (by simp)
  have pb : S.Ctx [a, b, a ⟹ b ⟹ c] b := .hyp (by simp)
  have pf : S.Ctx [a, b, a ⟹ b ⟹ c] (a ⟹ b ⟹ c) := .hyp (by simp)
  exact (Ctx.mp pb (.mp pa pf)).deduction.deduction.deduction.empty

theorem contraposition (a b : X) : S.Prov ((a ⟹ b) ⟹ S.neg b ⟹ S.neg a) := by
  have pa : S.Ctx [a, S.neg b, S.imp a b] a := .hyp (by simp)
  have pab : S.Ctx [a, S.neg b, S.imp a b] (S.imp a b) := .hyp (by simp)
  have pnb : S.Ctx [a, S.neg b, S.imp a b] (S.neg b) := .hyp (by simp)
  exact (Ctx.mp (.mp pa pab) pnb).deduction.deduction.deduction.empty

variable {S}

theorem Ctx.dne {Γ : List X} {a : X} (p : S.Ctx Γ (S.neg (S.neg a))) : S.Ctx Γ a :=
  .mp p (.thm (S.dne a))

theorem Ctx.byContra {Γ : List X} {a : X} (p : S.Ctx (S.neg a :: Γ) S.bot) : S.Ctx Γ a :=
  p.deduction.dne

theorem Ctx.andIntro {Γ : List X} {a b : X} (p : S.Ctx Γ a) (q : S.Ctx Γ b) :
    S.Ctx Γ (S.and a b) :=
  (Ctx.mp (q.up (S.imp a (S.neg b))) (.mp (p.up (S.imp a (S.neg b))) Ctx.head)).deduction

theorem Ctx.andLeft {Γ : List X} {a b : X} (p : S.Ctx Γ (S.and a b)) : S.Ctx Γ a := by
  have ha : S.Ctx (a :: S.neg a :: Γ) a := .hyp (by simp)
  have hn : S.Ctx (a :: S.neg a :: Γ) (S.neg a) := .hyp (by simp)
  have arrow : S.Ctx (S.neg a :: Γ) (S.imp a (S.neg b)) :=
    ((Ctx.mp ha hn).explosion (S.neg b)).deduction
  exact (Ctx.mp arrow (p.up (S.neg a))).deduction.dne

theorem Ctx.andRight {Γ : List X} {a b : X} (p : S.Ctx Γ (S.and a b)) : S.Ctx Γ b := by
  have hn : S.Ctx (S.neg b :: Γ) (S.neg b) := .hyp (by simp)
  exact (Ctx.mp (hn.lift a) (p.up (S.neg b))).deduction.dne

theorem Ctx.byCases {Γ : List X} (a : X) {c : X}
    (p : S.Ctx (a :: Γ) c) (q : S.Ctx (S.neg a :: Γ) c) : S.Ctx Γ c := by
  have hn : S.Ctx (S.neg c :: Γ) (S.neg c) := .hyp (by simp)
  have hp : S.Ctx (S.neg c :: Γ) (S.imp a c) := p.deduction.up (S.neg c)
  have hna : S.Ctx (S.neg c :: Γ) (S.neg a) := .mp hn (.mp hp (.thm (S.contraposition a c)))
  have hc : S.Ctx (S.neg c :: Γ) c := .mp hna (q.deduction.up (S.neg c))
  exact (Ctx.mp hc hn).deduction.dne

theorem Ctx.orInl {Γ : List X} {a : X} (b : X) (p : S.Ctx Γ a) : S.Ctx Γ (S.or a b) := by
  have h : S.Ctx (S.neg a :: Γ) S.bot := .mp (p.up _) Ctx.head
  exact (h.explosion b).deduction

theorem Ctx.orInr {Γ : List X} (a : X) {b : X} (p : S.Ctx Γ b) : S.Ctx Γ (S.or a b) :=
  p.lift (S.neg a)

theorem Ctx.orElim {Γ : List X} {a b c : X} (p : S.Ctx Γ (S.or a b))
    (qa : S.Ctx (a :: Γ) c) (qb : S.Ctx (b :: Γ) c) : S.Ctx Γ c :=
  Ctx.byCases a qa (qb.cut fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .mp (.hyp (by simp)) (p.up _)
    · exact .hyp (List.mem_cons_of_mem _ hx))

theorem Ctx.iffIntro {Γ : List X} {a b : X} (p : S.Ctx (a :: Γ) b) (q : S.Ctx (b :: Γ) a) :
    S.Ctx Γ (S.iff a b) := Ctx.andIntro p.deduction q.deduction

theorem Ctx.iffMp {Γ : List X} {a b : X} (p : S.Ctx Γ (S.iff a b)) (q : S.Ctx Γ a) :
    S.Ctx Γ b := .mp q p.andLeft

theorem Ctx.iffMpr {Γ : List X} {a b : X} (p : S.Ctx Γ (S.iff a b)) (q : S.Ctx Γ b) :
    S.Ctx Γ a := .mp q p.andRight

/-! ## Quantifiers -/

variable (S)

theorem liftImp (x : X) {a b : X} (p : S.Prov (a ⟹ b)) : S.Prov (S.all x a ⟹ S.all x b) :=
  S.mp (S.gen x p) (S.r2 x a b)

theorem universalVacuity (x y a : X) (h : S.Prov (a ⟹ S.all x a)) :
    S.Prov (S.all y a ⟹ S.all x (S.all y a)) :=
  Ctx.empty ((Ctx.hyp (by simp) : S.Ctx [S.all y a] _).mp
    (.thm (S.liftImp y h)) |>.mp (.thm (S.h2 y x a)) |>.deduction)

theorem negationVacuity (x a : X) (hv : S.Prov (a ⟹ S.all x a)) :
    S.Prov (S.neg a ⟹ S.all x (S.neg a)) := by
  have hc := S.mp hv (S.contraposition a (S.all x a))
  have hl := S.mp (S.gen x hc) (S.r2 x (S.neg (S.all x a)) (S.neg a))
  have hr := S.mp (S.h1 x a) (S.contraposition (S.ex x (S.all x a)) a)
  have hf : S.Prov (S.neg a ⟹ S.all x (S.neg (S.all x a))) :=
    Ctx.empty (((Ctx.hyp (by simp) : S.Ctx [S.neg a] _).mp (.thm hr)).dne.deduction)
  exact Ctx.empty ((Ctx.hyp (by simp) : S.Ctx [S.neg a] _).mp (.thm hf)
    |>.mp (.thm hl) |>.deduction)

theorem implicationVacuity (x a b : X)
    (ha : S.Prov (a ⟹ S.all x a)) (hb : S.Prov (b ⟹ S.all x b)) :
    S.Prov ((a ⟹ b) ⟹ S.all x (a ⟹ b)) := by
  have hbLift : S.Prov (b ⟹ S.all x (a ⟹ b)) :=
    Ctx.empty ((Ctx.hyp (by simp) : S.Ctx [b] _).mp (.thm hb)
      |>.mp (.thm (S.liftImp x (S.k b a))) |>.deduction)
  have hnot : S.Prov (S.neg a ⟹ a ⟹ b) := by
    have hp : S.Ctx [a, S.neg a] a := .hyp (by simp)
    have hn : S.Ctx [a, S.neg a] (S.neg a) := .hyp (by simp)
    exact ((Ctx.mp hp hn).explosion b).deduction.deduction.empty
  have haLift : S.Prov (S.neg a ⟹ S.all x (a ⟹ b)) :=
    Ctx.empty ((Ctx.hyp (by simp) : S.Ctx [S.neg a] _).mp (.thm (S.negationVacuity x a ha))
      |>.mp (.thm (S.liftImp x hnot)) |>.deduction)
  have pc : S.Ctx [a, S.imp a b] (S.all x (a ⟹ b)) :=
    .mp (.mp (a := a) Ctx.head (.hyp (by simp))) (.thm hbLift)
  have pnc : S.Ctx [S.neg a, S.imp a b] (S.all x (a ⟹ b)) := .mp (.hyp (by simp)) (.thm haLift)
  exact (Ctx.byCases a pc pnc).deduction.empty

theorem andVacuity (x a b : X)
    (ha : S.Prov (a ⟹ S.all x a)) (hb : S.Prov (b ⟹ S.all x b)) :
    S.Prov (S.and a b ⟹ S.all x (S.and a b)) :=
  S.negationVacuity x _ (S.implicationVacuity x a _ ha (S.negationVacuity x b hb))

theorem orVacuity (x a b : X)
    (ha : S.Prov (a ⟹ S.all x a)) (hb : S.Prov (b ⟹ S.all x b)) :
    S.Prov (S.or a b ⟹ S.all x (S.or a b)) :=
  S.implicationVacuity x _ b (S.negationVacuity x a ha) hb

theorem iffVacuity (x a b : X)
    (ha : S.Prov (a ⟹ S.all x a)) (hb : S.Prov (b ⟹ S.all x b)) :
    S.Prov (S.iff a b ⟹ S.all x (S.iff a b)) :=
  S.andVacuity x _ _ (S.implicationVacuity x a b ha hb) (S.implicationVacuity x b a hb ha)

theorem botVacuity (x : X) : S.Prov (S.bot ⟹ S.all x S.bot) := S.explosion _

variable {S}

theorem Ctx.forallMp {Γ : List X} (x : X) {a b : X}
    (p : S.Ctx Γ (S.all x a)) (q : S.Ctx Γ (S.all x (S.imp a b))) : S.Ctx Γ (S.all x b) :=
  .mp p (.mp q (.thm (S.r2 x a b)))

/-- Generalization under hypotheses that are vacuous in `x`. -/
theorem Ctx.generalize {Γ : List X} {a : X} (p : S.Ctx Γ a) (x : X)
    (vac : ∀ h, h ∈ Γ → S.Prov (S.imp h (S.all x h))) : S.Ctx Γ (S.all x a) := by
  induction p with
  | hyp h => exact .mp (.hyp h) (.thm (vac _ h))
  | thm d => exact .thm (S.gen x d)
  | mp _ _ ih₁ ih₂ => exact ih₁.forallMp x ih₂

theorem Ctx.existsElim {Γ : List X} (x : X) {a b : X}
    (hv : S.Prov (S.imp b (S.all x b)))
    (p : S.Ctx Γ (S.all x (S.imp a b))) (q : S.Ctx Γ (S.ex x a)) : S.Ctx Γ b := by
  have hnb : S.Ctx (S.neg b :: Γ) (S.all x (S.neg b)) :=
    .mp (.hyp (by simp)) (.thm (S.negationVacuity x b hv))
  have hc : S.Ctx (S.neg b :: Γ) (S.all x (S.imp (S.neg b) (S.neg a))) :=
    (p.up (S.neg b)).forallMp x (.thm (S.gen x (S.contraposition a b)))
  have ha : S.Ctx (S.neg b :: Γ) (S.all x (S.neg a)) := hnb.forallMp x hc
  exact (Ctx.mp ha (q.up (S.neg b))).deduction.dne

variable (S)

theorem existsMono (x : X) {a b : X} (p : S.Prov (a ⟹ b)) :
    S.Prov (S.ex x a ⟹ S.ex x b) :=
  S.mp (S.liftImp x (S.mp p (S.contraposition a b)))
    (S.contraposition (S.all x (S.neg b)) (S.all x (S.neg a)))

/-- `∀` respects a hypothesis-guarded equivalence. -/
theorem allIff (x : X) {a b : X} (p : S.Prov (S.iff a b)) :
    S.Prov (S.iff (S.all x a) (S.all x b)) :=
  Ctx.empty (Ctx.andIntro (.thm (S.liftImp x (Ctx.thm p).andLeft.empty))
    (.thm (S.liftImp x (Ctx.thm p).andRight.empty)))

theorem existsIff (x : X) {a b : X} (p : S.Prov (S.iff a b)) :
    S.Prov (S.iff (S.ex x a) (S.ex x b)) :=
  Ctx.empty (Ctx.andIntro (.thm (S.existsMono x (Ctx.thm p).andLeft.empty))
    (.thm (S.existsMono x (Ctx.thm p).andRight.empty)))

/-! ## Equivalence reasoning under hypotheses -/

variable {S}

theorem Ctx.iffRefl {Γ : List X} (a : X) : S.Ctx Γ (S.iff a a) :=
  Ctx.iffIntro Ctx.head Ctx.head

theorem Ctx.iffSymm {Γ : List X} {a b : X} (p : S.Ctx Γ (S.iff a b)) : S.Ctx Γ (S.iff b a) :=
  Ctx.andIntro p.andRight p.andLeft

theorem Ctx.iffTrans {Γ : List X} {a b c : X} (p : S.Ctx Γ (S.iff a b)) (q : S.Ctx Γ (S.iff b c)) :
    S.Ctx Γ (S.iff a c) :=
  Ctx.iffIntro ((q.up a).iffMp ((p.up a).iffMp Ctx.head))
    ((p.up c).iffMpr ((q.up c).iffMpr Ctx.head))

theorem Ctx.impCongr {Γ : List X} {a a' b b' : X} (p : S.Ctx Γ (S.iff a a'))
    (q : S.Ctx Γ (S.iff b b')) : S.Ctx Γ (S.iff (S.imp a b) (S.imp a' b')) := by
  refine Ctx.iffIntro ?_ ?_
  · refine Ctx.deduction ?_
    exact ((q.up _).up _).iffMp (Ctx.mp (((p.up _).up _).iffMpr Ctx.head) (Ctx.head.up _))
  · refine Ctx.deduction ?_
    exact ((q.up _).up _).iffMpr (Ctx.mp (((p.up _).up _).iffMp Ctx.head) (Ctx.head.up _))

theorem Ctx.negCongr {Γ : List X} {a a' : X} (p : S.Ctx Γ (S.iff a a')) :
    S.Ctx Γ (S.iff (S.neg a) (S.neg a')) := Ctx.impCongr p (Ctx.iffRefl _)

theorem Ctx.andCongr {Γ : List X} {a a' b b' : X} (p : S.Ctx Γ (S.iff a a'))
    (q : S.Ctx Γ (S.iff b b')) : S.Ctx Γ (S.iff (S.and a b) (S.and a' b')) :=
  Ctx.negCongr (Ctx.impCongr p (Ctx.negCongr q))

theorem Ctx.iffOfEq {Γ : List X} {a b : X} (h : a = b) : S.Ctx Γ (S.iff a b) :=
  h ▸ Ctx.iffRefl a

/-- `∀` respects an equivalence proved under hypotheses vacuous in `x`. -/
theorem Ctx.allCongr {Γ : List X} (x : X) {a b : X}
    (vac : ∀ h, h ∈ Γ → S.Prov (S.imp h (S.all x h))) (p : S.Ctx Γ (S.iff a b)) :
    S.Ctx Γ (S.iff (S.all x a) (S.all x b)) := by
  have hab := (p.andLeft).generalize x vac
  have hba := (p.andRight).generalize x vac
  exact Ctx.andIntro (.mp hab (.thm (S.r2 x a b))) (.mp hba (.thm (S.r2 x b a)))

theorem Ctx.exCongr {Γ : List X} (x : X) {a b : X}
    (vac : ∀ h, h ∈ Γ → S.Prov (S.imp h (S.all x h))) (p : S.Ctx Γ (S.iff a b)) :
    S.Ctx Γ (S.iff (S.ex x a) (S.ex x b)) :=
  Ctx.negCongr (Ctx.allCongr x vac (Ctx.negCongr p))

/-- `∃` is monotone under hypotheses. -/
theorem Ctx.exMp {Γ : List X} (x : X) {a b : X}
    (p : S.Ctx Γ (S.all x (S.imp a b))) (q : S.Ctx Γ (S.ex x a)) : S.Ctx Γ (S.ex x b) := by
  have hc : S.Ctx (S.all x (S.neg b) :: Γ) (S.all x (S.imp (S.neg b) (S.neg a))) :=
    (p.up _).forallMp x (.thm (S.gen x (S.contraposition a b)))
  exact (Ctx.mp (Ctx.head.forallMp x hc) (q.up _)).deduction

end Logic

/-- A calculus with a defined equality `E`: a witness `∃x E(y, x)`, vacuity of
atoms in labels they do not mention, and symmetry and transitivity of `E`.
`ok` marks the labels allowed as arguments of `E` (those other than the labels
`E` binds). -/
structure EqLogic (X : Type u) extends Logic X where
  E : X → X → X
  ok : X → Prop
  /-- `∃x E(y, x)`. -/
  witness (x y : X) : x ≠ y → ok x → ok y → Prov (imp (all x (imp (E y x) bot)) bot)
  eVac (a b c : X) : c ≠ a → c ≠ b → ok a → ok b → ok c → Prov (imp (E a b) (all c (E a b)))
  memVac (a b c : X) : c ≠ a → c ≠ b → Prov (imp (mem a b) (all c (mem a b)))
  eSymm (a b : X) : ok a → ok b → Prov (imp (E a b) (E b a))
  eTrans (a b d : X) : ok a → ok b → ok d → Prov (imp (E a b) (imp (E b d) (E a d)))

namespace EqLogic
variable {X : Type u} (S : EqLogic X)

open Logic

/-- `E` is congruent in its first argument. -/
theorem eLeftIff {x y w : X} (hx : S.ok x) (hy : S.ok y) (hw : S.ok w) :
    S.Prov (S.imp (S.E x y) (S.iff (S.E x w) (S.E y w))) := by
  have he : S.Ctx [S.E x y] (S.E x y) := Ctx.head
  have hs : S.Ctx [S.E x y] (S.E y x) := .mp he (.thm (S.eSymm x y hx hy))
  exact (Ctx.iffIntro (.mp Ctx.head (.mp (hs.up _) (.thm (S.eTrans y x w hy hx hw))))
    (.mp Ctx.head (.mp (he.up _) (.thm (S.eTrans x y w hx hy hw))))).deduction.empty

/-- `E` is congruent in its second argument. -/
theorem eRightIff {x y w : X} (hx : S.ok x) (hy : S.ok y) (hw : S.ok w) :
    S.Prov (S.imp (S.E x y) (S.iff (S.E w x) (S.E w y))) := by
  have he : S.Ctx [S.E x y] (S.E x y) := Ctx.head
  have hs : S.Ctx [S.E x y] (S.E y x) := .mp he (.thm (S.eSymm x y hx hy))
  refine (Ctx.iffIntro ?_ ?_).deduction.empty
  · exact .mp (he.up _) (.mp Ctx.head (.thm (S.eTrans w x y hw hx hy)))
  · exact .mp (hs.up _) (.mp Ctx.head (.thm (S.eTrans w y x hw hy hx)))

/-- Specialization of `∀x a` at `y`, given the substitution instance
`E(y, x) → (a → a')` and vacuity of `a'` in `x`. -/
theorem specialize {x y : X} (hxy : x ≠ y) (hx : S.ok x) (hy : S.ok y) {a a' : X}
    (sub : S.Prov (S.imp (S.E y x) (S.imp a a')))
    (vac : S.Prov (S.imp a' (S.all x a'))) : S.Prov (S.imp (S.all x a) a') := by
  have hl : S.Ctx [S.all x a] (S.all x (S.imp a (S.imp (S.E y x) a'))) :=
    .thm (S.gen x (S.mp sub (S.exchange _ _ _)))
  have hm : S.Ctx [S.all x a] (S.all x (S.imp (S.E y x) a')) := Ctx.head.forallMp x hl
  exact (Ctx.existsElim x vac hm (.thm (S.witness x y hxy hx hy))).deduction.empty

/-- Existential introduction at `y`, given `E(y, x) → (a' → a)` and vacuity of
`a'` in `x`. -/
theorem exIntro {x y : X} (hxy : x ≠ y) (hx : S.ok x) (hy : S.ok y) {a a' : X}
    (sub : S.Prov (S.imp (S.E y x) (S.imp a' a)))
    (vac : S.Prov (S.imp a' (S.all x a'))) : S.Prov (S.imp a' (S.ex x a)) := by
  have hv : S.Ctx [a'] (S.all x a') := .mp Ctx.head (.thm vac)
  have hl : S.Ctx [a'] (S.all x (S.imp a' (S.imp (S.E y x) a))) :=
    .thm (S.gen x (S.mp sub (S.exchange _ _ _)))
  exact (Ctx.exMp x (hv.forallMp x hl) (.thm (S.witness x y hxy hx hy))).deduction.empty

end EqLogic

end ZF207.CKernel.Generic
