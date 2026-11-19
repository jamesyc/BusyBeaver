module
public import GateModel.CodeBridge
public import Independence.Relativize
@[expose] public section
/-! # The interpretation `J` of ZF in models of the gate

`J σ` says: for every object `e` with no members, `σ` holds in the model of ZF
built at `e`. That model has three layers, each given by explicit formulas:

* membership-indiscernibility classes of the base structure;
* marked objects modulo marked bisimilarity, with marker `e`;
* the well-founded part.

`eval_J`: in any structure satisfying the machine's gate, `J σ` holds exactly
when `σ` holds in each of those models. -/
namespace ZF207.Independence
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory ZF207.GateModel

/-! ## Formulas for the marked quotient (read in any set structure) -/

def msingF : Semisentence ℒₛₑₜ 3 := “e s a. e ∈ s ∧ ∀ t, ((t ∈ s ∧ e ∈ t) ↔ t = a)”
def mdoubF : Semisentence ℒₛₑₜ 4 :=
  “e s a b. e ∈ s ∧ ∀ t, ((t ∈ s ∧ e ∈ t) ↔ (t = a ∨ t = b))”
def mpairF : Semisentence ℒₛₑₜ 4 :=
  “e p a b. e ∈ p ∧ (∀ t, t ∈ p → e ∈ t → (!msingF e t a ∨ !mdoubF e t a b)) ∧
    (∃ t, t ∈ p ∧ !msingF e t a) ∧ ∃ t, t ∈ p ∧ !mdoubF e t a b”
def pairInF : Semisentence ℒₛₑₜ 4 := “e B a b. ∃ p, p ∈ B ∧ !mpairF e p a b”
def backForthF : Semisentence ℒₛₑₜ 4 :=
  “e B x y. (∀ x', x' ∈ x → e ∈ x' → ∃ y', y' ∈ y ∧ e ∈ y' ∧ (x' = y' ∨ !pairInF e B x' y')) ∧
    ∀ y', y' ∈ y → e ∈ y' → ∃ x', x' ∈ x ∧ e ∈ x' ∧ (x' = y' ∨ !pairInF e B x' y')”
def bisimF : Semisentence ℒₛₑₜ 2 :=
  “e B. ∀ x y, !pairInF e B x y → !backForthF e B x y”
def eqvF : Semisentence ℒₛₑₜ 3 := “e x y. x = y ∨ ∃ B, !bisimF e B ∧ !pairInF e B x y”
def qmemF : Semisentence ℒₛₑₜ 3 := “e x y. ∃ z, z ∈ y ∧ e ∈ z ∧ !eqvF e x z”

section Defined
variable {V : Type*} [SetStructure V]

instance MSing.defined : ℒₛₑₜ-relation₃[V] MSing via msingF :=
  ⟨fun v => by simp [msingF, MSing]⟩
instance MDoub.defined : ℒₛₑₜ-relation₄[V] MDoub via mdoubF :=
  ⟨fun v => by simp [mdoubF, MDoub]⟩
instance MPair.defined : ℒₛₑₜ-relation₄[V] MPair via mpairF :=
  ⟨fun v => by simp [mpairF, MPair]⟩
instance PairIn.defined : ℒₛₑₜ-relation₄[V] PairIn via pairInF :=
  ⟨fun v => by simp [pairInF, PairIn]⟩
instance BackForth.defined : ℒₛₑₜ-relation₄[V] BackForth via backForthF :=
  ⟨fun v => by simp [backForthF, BackForth]⟩
instance Bisim.defined : ℒₛₑₜ-relation[V] Bisim via bisimF :=
  ⟨fun v => by simp [bisimF, Bisim]⟩
instance Eqv.defined : ℒₛₑₜ-relation₃[V] Eqv via eqvF :=
  ⟨fun v => by simp [eqvF, Eqv]⟩
instance QMem.defined : ℒₛₑₜ-relation₃[V] QMem via qmemF :=
  ⟨fun v => by simp [qmemF, QMem]⟩

end Defined

/-! ## Formulas for the well-founded part and for indiscernibility -/

def isTransF : Semisentence ℒₛₑₜ 1 := “T. ∀ y, y ∈ T → ∀ z, z ∈ y → z ∈ T”
def isWFdF : Semisentence ℒₛₑₜ 1 :=
  “T. ∀ S, (∀ z, z ∈ S → z ∈ T) → (∃ z, z ∈ S) → ∃ m, m ∈ S ∧ ∀ z, z ∈ S → z ∉ m”
def isWFF : Semisentence ℒₛₑₜ 1 := “x. ∃ T, x ∈ T ∧ !isTransF T ∧ !isWFdF T”
def indiscF : Semisentence ℒₛₑₜ 2 := “x y. ∀ z, (z ∈ x ↔ z ∈ y) ∧ (x ∈ z ↔ y ∈ z)”
def emptyF : Semisentence ℒₛₑₜ 1 := “e. ∀ y, y ∉ e”

section Defined2
variable {V : Type*} [SetStructure V]

instance IsTransSet.defined : ℒₛₑₜ-predicate[V] IsTransSet via isTransF :=
  ⟨fun v => by simp [isTransF, IsTransSet]⟩
instance IsWFdSet.defined : ℒₛₑₜ-predicate[V] IsWFdSet via isWFdF :=
  ⟨fun v => by simp [isWFdF, IsWFdSet]⟩
instance IsWF.defined : ℒₛₑₜ-predicate[V] IsWF via isWFF :=
  ⟨fun v => by simp [isWFF, IsWF]⟩

lemma eval_indiscF (x y : V) : V ⊧/![x, y] indiscF ↔ Indisc (fun a b : V => a ∈ b) x y := by
  simp [indiscF, Indisc]

lemma eval_emptyF (e : V) : V ⊧/![e] emptyF ↔ ∀ y, y ∉ e := by simp [emptyF]

end Defined2

/-! ## The three layers and `J` -/

def dNQ : RelData0 := ⟨“x. ⊤”, “x y. x ∈ y”, indiscF⟩
def dQ : RelData1 := ⟨“x e. e ∈ x”, “x y e. !qmemF e x y”, “x y e. !eqvF e x y”⟩
def dWF : RelData0 := ⟨isWFF, “x y. x ∈ y”, “x y. x = y”⟩

/-- The interpretation of set sentences in models of the gate. -/
def J (σ : Sentence ℒₛₑₜ) : Sentence ℒₛₑₜ :=
  ∀¹ ((Rew.embSubsts ![#0] ▹ emptyF) 🡒 rel0 dNQ (rel1 dQ (rel0 dWF σ)))

/-! ## Meaning of `J` -/

section Meaning
variable {W : Type*} [SetStructure W] [Nonempty W]

lemma sem_dNQ : Sem0 dNQ (cls (fun x y : W => x ∈ y)) where
  surj y := let ⟨x, hx⟩ := cls_surj _ y; ⟨x, by simp [dNQ], hx⟩
  mem x y _ _ := by simp [dNQ]; rfl
  eq x y _ _ := by
    show W ⊧/![x, y] indiscF ↔ _
    rw [eval_indiscF, cls_eq]

variable [GateHull (NQ (fun x y : W => x ∈ y))]

lemma sem_dQ {e : NQ (fun x y : W => x ∈ y)} (he : SetTheory.IsEmpty e) :
    Sem1 dQ e (Q.cls he) := by
  have hdom : ∀ z, (NQ (fun x y : W => x ∈ y)) ⊧/![z, e] dQ.dom ↔ e ∈ z := fun z => by simp [dQ]
  have hmem : ∀ x y, (NQ (fun x y : W => x ∈ y)) ⊧/![x, y, e] dQ.mem ↔ QMem e x y :=
    fun x y => by simp [dQ]
  have heq : ∀ x y, (NQ (fun x y : W => x ∈ y)) ⊧/![x, y, e] dQ.eq ↔ Eqv e x y :=
    fun x y => by simp [dQ]
  refine ⟨fun y => ?_, fun x y hx hy => ?_, fun x y hx hy => ?_⟩
  · obtain ⟨x, hx, hxy⟩ := (qInterp he).surj y
    exact ⟨x, (hdom x).mpr hx, hxy⟩
  · rw [hmem]; exact (qInterp he).mem_iff x y ((hdom x).mp hx) ((hdom y).mp hy)
  · rw [heq]; exact (qInterp he).eq_iff x y ((hdom x).mp hx) ((hdom y).mp hy)

lemma sem_dWF {e : NQ (fun x y : W => x ∈ y)} (he : SetTheory.IsEmpty e) :
    Sem0 dWF (wfInterp (M := Q he)).π := by
  have hdom : ∀ z : Q he, (Q he) ⊧/![z] dWF.dom ↔ IsWF z := fun z => by simp [dWF]
  have hmem : ∀ x y : Q he, (Q he) ⊧/![x, y] dWF.mem ↔ x ∈ y := fun x y => by simp [dWF]
  have heq : ∀ x y : Q he, (Q he) ⊧/![x, y] dWF.eq ↔ x = y := fun x y => by simp [dWF]
  refine ⟨fun y => ?_, fun x y hx hy => ?_, fun x y hx hy => ?_⟩
  · obtain ⟨x, hx, hxy⟩ := (wfInterp (M := Q he)).surj y
    exact ⟨x, (hdom x).mpr hx, hxy⟩
  · rw [hmem]; exact (wfInterp (M := Q he)).mem_iff x y ((hdom x).mp hx) ((hdom y).mp hy)
  · rw [heq]; exact (wfInterp (M := Q he)).eq_iff x y ((hdom x).mp hx) ((hdom y).mp hy)

lemma vec_one_snoc {α : Type*} (x : α) : (![x] : Fin 1 → α) = Fin.snoc (![] : Fin 0 → α) x := by
  funext i; rw [Subsingleton.elim i (Fin.last 0)]; simp

/-- `J σ` holds exactly when `σ` holds in the ZF model built at every empty object. -/
theorem eval_J (σ : Sentence ℒₛₑₜ) :
    W↓[ℒₛₑₜ] ⊧ J σ ↔ ∀ (e : W) (he : ∀ y, y ∉ e),
      (WFPart (Q (nq_isEmpty (mem := fun x y : W => x ∈ y) he)))↓[ℒₛₑₜ] ⊧ σ := by
  simp only [models_iff, J, Semiformula.Realize, Semiformula.eval_all,
    LogicalConnective.HomClass.map_imply, Semiformula.eval_embSubsts, comp_vec1]
  refine forall_congr' fun e => ?_
  rw [show (Semiterm.val ![e] Empty.elim (#0 : Semiterm ℒₛₑₜ Empty 1)) = e from rfl, eval_emptyF]
  have chain : ∀ he : ∀ y, y ∉ e,
      (rel0 dNQ (rel1 dQ (rel0 dWF σ))).Eval ![e] Empty.elim ↔
        σ.Eval (M := WFPart (Q (nq_isEmpty (mem := fun x y : W => x ∈ y) he))) ![] Empty.elim := by
    intro he
    have h₁ := eval_rel0 (sem_dNQ (W := W)) (rel1 dQ (rel0 dWF σ)) ![e] Empty.elim
      (fun _ => by simp [dNQ]) (fun x => x.elim)
    have he' := nq_isEmpty (mem := fun x y : W => x ∈ y) he
    have h₂ := eval_rel1 (sem_dQ he') (rel0 dWF σ) ![] Empty.elim
      (fun i => i.elim0) (fun x => x.elim)
    have h₃ := eval_rel0 (sem_dWF he') σ ![] Empty.elim (fun i => i.elim0) (fun x => x.elim)
    have hc : (cls (fun x y : W => x ∈ y) ∘ ![e]) = Fin.snoc ![] (cls _ e) := by
      rw [← vec_one_snoc]; funext i; rw [Subsingleton.elim i 0]; rfl
    have hE₁ : (cls (fun x y : W => x ∈ y) ∘ (Empty.elim : Empty → W)) = Empty.elim :=
      funext (·.elim)
    have hE₂ : (Q.cls he' ∘ (Empty.elim : Empty → _)) = Empty.elim := funext (·.elim)
    have hE₃ : ((wfInterp (M := Q he')).π ∘ (Empty.elim : Empty → _)) = Empty.elim :=
      funext (·.elim)
    have hn₂ : (Q.cls he' ∘ (![] : Fin 0 → _)) = ![] := funext (·.elim0)
    have hn₃ : ((wfInterp (M := Q he')).π ∘ (![] : Fin 0 → _)) = ![] := funext (·.elim0)
    rw [hc, hE₁] at h₁
    rw [hE₂, hn₂] at h₂
    rw [hE₃, hn₃] at h₃
    exact h₁.trans (h₂.trans h₃)
  exact ⟨fun H he => (chain he).mp (H he), fun H he => (chain he).mpr (H he)⟩

end Meaning

end ZF207.Independence
