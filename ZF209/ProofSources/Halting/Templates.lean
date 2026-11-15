module
public import Halting.JXSem
public import Independence.Interpretation
public import ConcreteArithmeticTranslation
public import ConcreteArithmeticModelStructure
@[expose] public section
/-! # The templates

At a marker `e` with no members, every object `x` is projected to a natural number of the ZF
model `WFPart (Q e)`: `x` itself when it lies in the three layers and denotes an element of ω,
zero otherwise. The templates relate projections through the relativized formulas of the
ω-translation. At other markers every template holds. The domain template is `⊤`. -/
namespace ZF209.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open ZF209.Independence ZF209.GateModel ZF209.OmegaInterpretation

/-- The three layers, marker last. -/
def lay {k : ℕ} (F : Semisentence ℒₛₑₜ k) : Semisentence ℒₛₑₜ (k + 1) :=
  rel0 dNQ (rel1 dQ (rel0 dWF F))

/-- The first two layers, marker last. -/
def lay2 {k : ℕ} (F : Semisentence ℒₛₑₜ k) : Semisentence ℒₛₑₜ (k + 1) :=
  rel0 dNQ (rel1 dQ F)

/-- `x` lies in the three layers at marker `e`. -/
def goodF : Semisentence ℒₛₑₜ 2 := “x e. e ∈ x ∧ !(lay2 isWFF) x e”

/-- `x` denotes a natural number of the model at `e`. -/
def numF : Semisentence ℒₛₑₜ 2 := “x e. !goodF x e ∧ !(lay domain) x e”

/-- `x'` represents the projection of `x`. -/
def prF : Semisentence ℒₛₑₜ 3 :=
  “x x' e. (!numF x e ∧ x' = x) ∨ (¬!numF x e ∧ !numF x' e ∧ !(lay zeroGraph) x' e)”

def eqG : Semisentence ℒₛₑₜ 2 := “a b. a = b”
def ltG : Semisentence ℒₛₑₜ 2 := “a b. a ∈ b”
def oneG : Semisentence ℒₛₑₜ 1 := arithmeticFuncGraph Language.ORing.Func.one
def addG : Semisentence ℒₛₑₜ 3 := arithmeticFuncGraph Language.ORing.Func.add
def mulG : Semisentence ℒₛₑₜ 3 := arithmeticFuncGraph Language.ORing.Func.mul

/-- The templates. -/
def tmpl : ZF209.Internal.Arith.Interp where
  mark := emptyF
  dom := “e x. ⊤”
  eq := “e x y. !emptyF e → ∃ x', ∃ y', !prF x x' e ∧ !prF y y' e ∧ !(lay eqG) x' y' e”
  lt := “e x y. !emptyF e → ∃ x', ∃ y', !prF x x' e ∧ !prF y y' e ∧ !(lay ltG) x' y' e”
  zero := “e y. !emptyF e → ∃ y', !prF y y' e ∧ !(lay zeroGraph) y' e”
  one := “e y. !emptyF e → ∃ y', !prF y y' e ∧ !(lay oneG) y' e”
  add := “e a b y. !emptyF e → ∃ a', ∃ b', ∃ y', !prF a a' e ∧ !prF b b' e ∧ !prF y y' e ∧
    !(lay addG) y' a' b' e”
  mul := “e a b y. !emptyF e → ∃ a', ∃ b', ∃ y', !prF a a' e ∧ !prF b b' e ∧ !prF y y' e ∧
    !(lay mulG) y' a' b' e”

/-! ## Shapes of the templates -/

section Shapes
variable {W : Type*} [SetStructure W]

lemma tmpl_eq_eval (e x y : W) : W ⊧/![e, x, y] tmpl.eq ↔ (W ⊧/![e] emptyF →
    ∃ x' y', W ⊧/![x, x', e] prF ∧ W ⊧/![y, y', e] prF ∧ W ⊧/![x', y', e] (lay eqG)) := by
  simp [tmpl]

lemma tmpl_lt_eval (e x y : W) : W ⊧/![e, x, y] tmpl.lt ↔ (W ⊧/![e] emptyF →
    ∃ x' y', W ⊧/![x, x', e] prF ∧ W ⊧/![y, y', e] prF ∧ W ⊧/![x', y', e] (lay ltG)) := by
  simp [tmpl]

lemma tmpl_zero_eval (e y : W) : W ⊧/![e, y] tmpl.zero ↔ (W ⊧/![e] emptyF →
    ∃ y', W ⊧/![y, y', e] prF ∧ W ⊧/![y', e] (lay zeroGraph)) := by
  simp [tmpl]

lemma tmpl_one_eval (e y : W) : W ⊧/![e, y] tmpl.one ↔ (W ⊧/![e] emptyF →
    ∃ y', W ⊧/![y, y', e] prF ∧ W ⊧/![y', e] (lay oneG)) := by
  simp [tmpl]

lemma tmpl_add_eval (e a b y : W) : W ⊧/![e, a, b, y] tmpl.add ↔ (W ⊧/![e] emptyF →
    ∃ a' b' y', W ⊧/![a, a', e] prF ∧ W ⊧/![b, b', e] prF ∧ W ⊧/![y, y', e] prF ∧
      W ⊧/![y', a', b', e] (lay addG)) := by
  simp [tmpl]

lemma tmpl_mul_eval (e a b y : W) : W ⊧/![e, a, b, y] tmpl.mul ↔ (W ⊧/![e] emptyF →
    ∃ a' b' y', W ⊧/![a, a', e] prF ∧ W ⊧/![b, b', e] prF ∧ W ⊧/![y, y', e] prF ∧
      W ⊧/![y', a', b', e] (lay mulG)) := by
  simp [tmpl]

end Shapes

/-! ## Reading the layers -/

section Layers
variable {W : Type*} [SetStructure W] [Nonempty W] [GateHull (NQ (fun x y : W => x ∈ y))]
variable {e : W} (he : ∀ y, y ∉ e)

local notation "he'" => nq_isEmpty (mem := fun x y : W => x ∈ y) he

/-- The projection of a layered object into the model at `e`. -/
noncomputable def lp (x : W) : WFPart (Q he') :=
  (wfInterp (M := Q he')).π (Q.cls he' (cls (fun x y : W => x ∈ y) x))

/-- `x` lies in the three layers at `e`. -/
def Good (x : W) : Prop := e ∈ x ∧ IsWF (Q.cls he' (cls (fun x y : W => x ∈ y) x))

lemma cls_comp_snoc {k : ℕ} (b : Fin k → W) :
    (cls (fun x y : W => x ∈ y) ∘ Fin.snoc b e) = Fin.snoc (cls _ ∘ b) (cls _ e) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

lemma eval_lay {k : ℕ} (F : Semisentence ℒₛₑₜ k) (b : Fin k → W) (hb : ∀ i, Good he (b i)) :
    W ⊧/(Fin.snoc b e) (lay F) ↔ (WFPart (Q he')) ⊧/(fun i => lp he (b i)) F := by
  have h₁ := eval_rel0 (sem_dNQ (W := W)) (rel1 dQ (rel0 dWF F)) (Fin.snoc b e) Empty.elim
    (fun _ => by simp [dNQ]) (fun x => x.elim)
  have h₂ := eval_rel1 (sem_dQ he') (rel0 dWF F) (cls (fun x y : W => x ∈ y) ∘ b) Empty.elim
    (fun i => by simpa [dQ] using (cls_mem (mem := fun x y : W => x ∈ y)).mpr (hb i).1) (fun x => x.elim)
  have h₃ := eval_rel0 (sem_dWF he') F (Q.cls he' ∘ cls (fun x y : W => x ∈ y) ∘ b) Empty.elim
    (fun i => by simpa [dWF] using (hb i).2) (fun x => x.elim)
  have hE₁ : (cls (fun x y : W => x ∈ y) ∘ (Empty.elim : Empty → W)) = Empty.elim :=
    funext (·.elim)
  have hE₂ : (Q.cls he' ∘ (Empty.elim : Empty → _)) = Empty.elim := funext (·.elim)
  have hE₃ : ((wfInterp (M := Q he')).π ∘ (Empty.elim : Empty → _)) = Empty.elim :=
    funext (·.elim)
  rw [cls_comp_snoc, hE₁] at h₁
  rw [hE₂] at h₂
  rw [hE₃] at h₃
  exact h₁.trans (h₂.trans h₃)

lemma eval_lay2 {k : ℕ} (F : Semisentence ℒₛₑₜ k) (b : Fin k → W) (hb : ∀ i, e ∈ b i) :
    W ⊧/(Fin.snoc b e) (lay2 F) ↔ (Q he') ⊧/(fun i => Q.cls he' (cls (fun x y : W => x ∈ y) (b i))) F := by
  have h₁ := eval_rel0 (sem_dNQ (W := W)) (rel1 dQ F) (Fin.snoc b e) Empty.elim
    (fun _ => by simp [dNQ]) (fun x => x.elim)
  have h₂ := eval_rel1 (sem_dQ he') F (cls (fun x y : W => x ∈ y) ∘ b) Empty.elim
    (fun i => by simpa [dQ] using (cls_mem (mem := fun x y : W => x ∈ y)).mpr (hb i)) (fun x => x.elim)
  have hE₁ : (cls (fun x y : W => x ∈ y) ∘ (Empty.elim : Empty → W)) = Empty.elim :=
    funext (·.elim)
  have hE₂ : (Q.cls he' ∘ (Empty.elim : Empty → _)) = Empty.elim := funext (·.elim)
  rw [cls_comp_snoc, hE₁] at h₁
  rw [hE₂] at h₂
  exact h₁.trans h₂

lemma snoc_one (x : W) : (Fin.snoc ![x] e : Fin 2 → W) = ![x, e] := by
  funext i; refine Fin.cases ?_ (Fin.cases ?_ fun j => j.elim0) i <;> rfl

lemma good_iff (x : W) : W ⊧/![x, e] goodF ↔ Good he x := by
  have h2 : e ∈ x → (W ⊧/![x, e] (lay2 isWFF) ↔ IsWF (Q.cls he' (cls (fun x y : W => x ∈ y) x))) := by
    intro hx
    have := eval_lay2 he isWFF ![x] (fun i => by rw [Fin.fin_one_eq_zero i]; exact hx)
    rw [snoc_one] at this
    rw [this]; simp
  simp only [goodF, Good]
  constructor
  · intro h
    have h' : e ∈ x ∧ W ⊧/![x, e] (lay2 isWFF) := by simpa using h
    exact ⟨h'.1, (h2 h'.1).mp h'.2⟩
  · rintro ⟨hx, hw⟩
    have : W ⊧/![x, e] (lay2 isWFF) := (h2 hx).mpr hw
    simpa [hx] using this

lemma lp_surj (m : WFPart (Q he')) : ∃ x, Good he x ∧ lp he x = m := by
  obtain ⟨q, hq, rfl⟩ := (sem_dWF he').surj m
  obtain ⟨z, hz, rfl⟩ := (sem_dQ he').surj q
  obtain ⟨x, rfl⟩ := cls_surj (fun x y : W => x ∈ y) z
  exact ⟨x, ⟨(cls_mem (mem := fun x y : W => x ∈ y)).mp (by simpa [dQ] using hz), by simpa [dWF] using hq⟩, rfl⟩

lemma snoc_two (x y : W) : (Fin.snoc ![x, y] e : Fin 3 → W) = ![x, y, e] := by
  funext i; refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ fun j => j.elim0)) i <;> rfl

lemma snoc_three (x y z : W) : (Fin.snoc ![x, y, z] e : Fin 4 → W) = ![x, y, z, e] := by
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ fun j => j.elim0))) i <;> rfl

lemma eval_lay_1 (F : Semisentence ℒₛₑₜ 1) (x : W) (hx : Good he x) :
    W ⊧/![x, e] (lay F) ↔ (WFPart (Q he')) ⊧/![lp he x] F := by
  have := eval_lay he F ![x] (fun i => by rw [Fin.fin_one_eq_zero i]; exact hx)
  have hf : (fun i => lp he (![x] i)) = ![lp he x] := by
    funext i; rw [Fin.fin_one_eq_zero i]; rfl
  rw [snoc_one] at this; rw [this, hf]

lemma eval_lay_2 (F : Semisentence ℒₛₑₜ 2) (x y : W) (hx : Good he x) (hy : Good he y) :
    W ⊧/![x, y, e] (lay F) ↔ (WFPart (Q he')) ⊧/![lp he x, lp he y] F := by
  have := eval_lay he F ![x, y] (fun i => by
    refine Fin.cases ?_ (Fin.cases ?_ fun j => j.elim0) i
    · exact hx
    · exact hy)
  have hf : (fun i => lp he (![x, y] i)) = ![lp he x, lp he y] := by
    funext i; refine Fin.cases ?_ (Fin.cases ?_ fun j => j.elim0) i <;> rfl
  rw [snoc_two] at this; rw [this, hf]

lemma eval_lay_3 (F : Semisentence ℒₛₑₜ 3) (x y z : W) (hx : Good he x) (hy : Good he y)
    (hz : Good he z) :
    W ⊧/![x, y, z, e] (lay F) ↔ (WFPart (Q he')) ⊧/![lp he x, lp he y, lp he z] F := by
  have := eval_lay he F ![x, y, z] (fun i => by
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ fun j => j.elim0)) i
    · exact hx
    · exact hy
    · exact hz)
  have hf : (fun i => lp he (![x, y, z] i)) = ![lp he x, lp he y, lp he z] := by
    funext i; refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ fun j => j.elim0)) i <;> rfl
  rw [snoc_three] at this; rw [this, hf]

end Layers

/-! ## Projections to natural numbers -/

section Numbers
variable {W : Type*} [SetStructure W] [Nonempty W] [GateHull (NQ (fun x y : W => x ∈ y))]
variable {e : W} (he : ∀ y, y ∉ e)

local notation "he'" => nq_isEmpty (mem := fun x y : W => x ∈ y) he

variable [(WFPart (Q (nq_isEmpty (mem := fun x y : W => x ∈ y) he)))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "Aω" => arithmeticTranslation.Model (WFPart (Q he'))

/-- `x` denotes a natural number of the model at `e`. -/
def Num (x : W) : Prop := Good he x ∧ lp he x ∈ (ω : WFPart (Q he'))

lemma num_iff (x : W) : W ⊧/![x, e] numF ↔ Num he x := by
  have hn : W ⊧/![x, e] numF ↔ W ⊧/![x, e] goodF ∧ W ⊧/![x, e] (lay domain) := by
    simp [numF]
  rw [hn, good_iff he]
  constructor
  · rintro ⟨hg, hd⟩; exact ⟨hg, by simpa using (eval_lay_1 he domain x hg).mp hd⟩
  · rintro ⟨hg, hd⟩; exact ⟨hg, (eval_lay_1 he domain x hg).mpr (by simpa using hd)⟩

lemma dom_of_omega {m : WFPart (Q he')} (h : m ∈ (ω : WFPart (Q he'))) :
    arithmeticTranslation.Dom m := by
  simpa [DirectTranslation.Dom, arithmeticTranslation, Semiformula.Operator.val] using h

/-- The projection of an object to a natural number of the model at `e`. -/
noncomputable def pr (x : W) : Aω :=
  open Classical in
  if h : Num he x then ⟨lp he x, dom_of_omega he h.2⟩ else ⟨∅, dom_of_omega he empty_mem_ω⟩

lemma pr_val_num {x : W} (h : Num he x) : (pr he x).val = lp he x := by
  simp [pr, h]

lemma pr_val_not {x : W} (h : ¬Num he x) : (pr he x).val = ∅ := by
  simp [pr, h]

lemma zero_rep : ∃ z, Num he z ∧ lp he z = ∅ := by
  obtain ⟨z, hz, hlz⟩ := lp_surj he ∅
  exact ⟨z, ⟨hz, by rw [hlz]; exact empty_mem_ω⟩, hlz⟩

lemma prF_spec {x x' : W} (h : W ⊧/![x, x', e] prF) : Num he x' ∧ lp he x' = (pr he x).val := by
  have h' : (W ⊧/![x, e] numF ∧ x' = x) ∨
      (¬W ⊧/![x, e] numF ∧ W ⊧/![x', e] numF ∧ W ⊧/![x', e] (lay zeroGraph)) := by
    simpa [prF] using h
  rw [num_iff he, num_iff he] at h'
  rcases h' with ⟨hx, rfl⟩ | ⟨hx, hx', hz⟩
  · exact ⟨hx, (pr_val_num he hx).symm⟩
  · refine ⟨hx', ?_⟩
    rw [pr_val_not he hx]
    simpa using (eval_lay_1 he zeroGraph x' hx'.1).mp hz

include he in
lemma prF_canon (x : W) : ∃ x', W ⊧/![x, x', e] prF := by
  by_cases hx : Num he x
  · exact ⟨x, by simpa [prF, num_iff he] using Or.inl hx⟩
  · obtain ⟨z, hz, hlz⟩ := zero_rep he
    refine ⟨z, ?_⟩
    have : W ⊧/![z, e] (lay zeroGraph) := (eval_lay_1 he zeroGraph z hz.1).mpr (by simpa using hlz)
    simpa [prF, num_iff he, hx, hz] using this

end Numbers

/-! ## Graphs in a model of ZF -/

section Graphs
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

lemma eqG_eval (a b : V) : V ⊧/![a, b] eqG ↔ a = b := by simp [eqG]
lemma ltG_eval (a b : V) : V ⊧/![a, b] ltG ↔ a ∈ b := by simp [ltG]
lemma oneG_eval (z : V) : V ⊧/![z] oneG ↔ z = (1 : V) := by
  simp [oneG, arithmeticFuncGraph, one_def', succ]
lemma addG_eval (z a n : V) : V ⊧/![z, a, n] addG ↔ z = add a n := by
  simp [addG, arithmeticFuncGraph, add_graph_defined.iff]
lemma mulG_eval (z a n : V) : V ⊧/![z, a, n] mulG ↔ z = mul a n := by
  simp [mulG, arithmeticFuncGraph, mul_graph_defined.iff]

end Graphs

/-! ## The templates read the natural numbers of the model at `e` -/

section Reading
variable {W : Type*} [SetStructure W] [Nonempty W] [GateHull (NQ (fun x y : W => x ∈ y))]
variable {e : W} (he : ∀ y, y ∉ e)

local notation "he'" => nq_isEmpty (mem := fun x y : W => x ∈ y) he

variable [Nonempty (WFPart (Q (nq_isEmpty (mem := fun x y : W => x ∈ y) he)))]
  [(WFPart (Q (nq_isEmpty (mem := fun x y : W => x ∈ y) he)))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

include he in
lemma mark_e : W ⊧/![e] emptyF := by simpa [emptyF] using he

lemma one_rep {y : W} (G : Semisentence ℒₛₑₜ 1) (P : WFPart (Q he') → Prop)
    (hG : ∀ a, (WFPart (Q he')) ⊧/![a] G ↔ P a) :
    (∃ y', W ⊧/![y, y', e] prF ∧ W ⊧/![y', e] (lay G)) ↔ P (pr he y).val := by
  constructor
  · rintro ⟨y', hy, hG'⟩
    obtain ⟨ny, ey⟩ := prF_spec he hy
    rw [← ey, ← hG]; exact (eval_lay_1 he G y' ny.1).mp hG'
  · intro hP
    obtain ⟨y', hy⟩ := prF_canon he y
    obtain ⟨ny, ey⟩ := prF_spec he hy
    exact ⟨y', hy, (eval_lay_1 he G y' ny.1).mpr (by rw [hG, ey]; exact hP)⟩

lemma two_reps {x y : W} (G : Semisentence ℒₛₑₜ 2) (P : WFPart (Q he') → WFPart (Q he') → Prop)
    (hG : ∀ a b, (WFPart (Q he')) ⊧/![a, b] G ↔ P a b) :
    (∃ x' y', W ⊧/![x, x', e] prF ∧ W ⊧/![y, y', e] prF ∧ W ⊧/![x', y', e] (lay G)) ↔
      P (pr he x).val (pr he y).val := by
  constructor
  · rintro ⟨x', y', hx, hy, hG'⟩
    obtain ⟨nx, ex⟩ := prF_spec he hx; obtain ⟨ny, ey⟩ := prF_spec he hy
    rw [← ex, ← ey, ← hG]; exact (eval_lay_2 he G x' y' nx.1 ny.1).mp hG'
  · intro hP
    obtain ⟨x', hx⟩ := prF_canon he x; obtain ⟨y', hy⟩ := prF_canon he y
    obtain ⟨nx, ex⟩ := prF_spec he hx; obtain ⟨ny, ey⟩ := prF_spec he hy
    exact ⟨x', y', hx, hy, (eval_lay_2 he G x' y' nx.1 ny.1).mpr (by rw [hG, ex, ey]; exact hP)⟩

lemma three_reps {a b y : W} (G : Semisentence ℒₛₑₜ 3)
    (P : WFPart (Q he') → WFPart (Q he') → WFPart (Q he') → Prop)
    (hG : ∀ z u v, (WFPart (Q he')) ⊧/![z, u, v] G ↔ P z u v) :
    (∃ a' b' y', W ⊧/![a, a', e] prF ∧ W ⊧/![b, b', e] prF ∧ W ⊧/![y, y', e] prF ∧
      W ⊧/![y', a', b', e] (lay G)) ↔ P (pr he y).val (pr he a).val (pr he b).val := by
  constructor
  · rintro ⟨a', b', y', ha, hb, hy, hG'⟩
    obtain ⟨na, ea⟩ := prF_spec he ha; obtain ⟨nb, eb⟩ := prF_spec he hb
    obtain ⟨ny, ey⟩ := prF_spec he hy
    rw [← ea, ← eb, ← ey, ← hG]; exact (eval_lay_3 he G y' a' b' ny.1 na.1 nb.1).mp hG'
  · intro hP
    obtain ⟨a', ha⟩ := prF_canon he a; obtain ⟨b', hb⟩ := prF_canon he b
    obtain ⟨y', hy⟩ := prF_canon he y
    obtain ⟨na, ea⟩ := prF_spec he ha; obtain ⟨nb, eb⟩ := prF_spec he hb
    obtain ⟨ny, ey⟩ := prF_spec he hy
    exact ⟨a', b', y', ha, hb, hy,
      (eval_lay_3 he G y' a' b' ny.1 na.1 nb.1).mpr (by rw [hG, ea, eb, ey]; exact hP)⟩

local notation "Aω" => arithmeticTranslation.Model (WFPart (Q he'))

lemma model_eq_iff (u v : Aω) : u = v ↔ u.val = v.val :=
  ⟨fun h => h ▸ rfl, fun h => DirectTranslation.Model.ext h⟩

theorem reads : Reads tmpl e (pr he) where
  surj a := by
    obtain ⟨x, hx, hlx⟩ := lp_surj he a.val
    have hn : Num he x := ⟨hx, by rw [hlx]; exact model_mem_omega a⟩
    exact ⟨x, DirectTranslation.Model.ext (by rw [pr_val_num he hn, hlx])⟩
  dom x := by simp [tmpl]
  eq x y := by
    rw [tmpl_eq_eval]; simp only [mark_e he, true_implies]
    rw [two_reps he eqG (· = ·) eqG_eval, model_eq_iff he]
  lt x y := by
    rw [tmpl_lt_eval]; simp only [mark_e he, true_implies]
    rw [two_reps he ltG (· ∈ ·) ltG_eval, lt_iff_mem]
  zero y := by
    rw [tmpl_zero_eval]; simp only [mark_e he, true_implies]
    rw [one_rep he zeroGraph (· = ∅) (fun a => by simp), model_eq_iff he, val_zero, zero_def]
  one y := by
    rw [tmpl_one_eval]; simp only [mark_e he, true_implies]
    rw [one_rep he oneG (· = 1) oneG_eval, model_eq_iff he, val_one]
  add a b y := by
    rw [tmpl_add_eval]; simp only [mark_e he, true_implies]
    rw [three_reps he addG (fun z u v => z = add u v) addG_eval, model_eq_iff he, val_add, eq_comm]
  mul a b y := by
    rw [tmpl_mul_eval]; simp only [mark_e he, true_implies]
    rw [three_reps he mulG (fun z u v => z = mul u v) mulG_eval, model_eq_iff he, val_mul, eq_comm]

end Reading

end ZF209.Halting
