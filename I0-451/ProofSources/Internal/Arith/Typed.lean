module
public import Internal.Arith.Quant
@[expose] public section
/-! # Typed views of the translation

`gr t` is the graph of a typed ℒₒᵣ term and `jt p` the translation of a typed
ℒₒᵣ formula, both as typed `ℒₛₑₜ` formulas. They commute with shifts and with
substitutions of variables (every `ℒₛₑₜ` term is a variable; `lv` reads it as
an ℒₒᵣ term). -/
namespace ZF207.Internal.Arith
open I0451.Logic (set_isRel set_no_func set_term_cases)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Every `ℒₛₑₜ` semiterm vector consists of variables. -/
lemma varVec_of_set {n m w : V} (hw : IsSemitermVec ℒₛₑₜ n m w) : VarVec n w :=
  VarVec.of_cases fun i hi => by
    rcases set_term_cases.mp (hw.nth hi) with ⟨z, _, h⟩ | ⟨x, h⟩
    · exact Or.inl ⟨z, h⟩
    · exact Or.inr ⟨x, h⟩

/-- An `ℒₛₑₜ` term read as an ℒₒᵣ term. -/
noncomputable def lv {n : ℕ} (s : Bootstrapping.Semiterm V ℒₛₑₜ n) : Bootstrapping.Semiterm V ℒₒᵣ n :=
  ⟨s.val, by
    rcases set_term_cases.mp s.isSemiterm with ⟨z, hz, h⟩ | ⟨x, h⟩
    · rw [h]; simp [hz]
    · rw [h]; simp⟩

@[simp] lemma lv_val {n : ℕ} (s : Bootstrapping.Semiterm V ℒₛₑₜ n) : (lv s).val = s.val := rfl
@[simp] lemma lv_bvar {n : ℕ} (z : Fin n) :
    lv (Bootstrapping.Semiterm.bvar z : Bootstrapping.Semiterm V ℒₛₑₜ n) = Bootstrapping.Semiterm.bvar z := by ext; simp
@[simp] lemma lv_fvar {n : ℕ} (x : V) :
    lv (Bootstrapping.Semiterm.fvar x : Bootstrapping.Semiterm V ℒₛₑₜ n) = Bootstrapping.Semiterm.fvar x := by ext; simp
@[simp] lemma lv_shift {n : ℕ} (s : Bootstrapping.Semiterm V ℒₛₑₜ n) : lv s.shift = (lv s).shift := by
  rcases set_term_cases.mp s.isSemiterm with ⟨z, _, h⟩ | ⟨x, h⟩ <;> ext <;> simp [h]
@[simp] lemma lv_bShift {n : ℕ} (s : Bootstrapping.Semiterm V ℒₛₑₜ n) : lv s.bShift = (lv s).bShift := by
  rcases set_term_cases.mp s.isSemiterm with ⟨z, _, h⟩ | ⟨x, h⟩ <;> ext <;> simp [h]

lemma lv_vec_val {k n : ℕ} (w : SemitermVec V ℒₛₑₜ k n) : SemitermVec.val (lv ⨟ w) = w.val := rfl

variable (ι : Interp)

/-- A closed `ℒₛₑₜ` term seen with `n` bound variables. -/
noncomputable def cl {n : ℕ} (e : Bootstrapping.Term V ℒₛₑₜ) : Bootstrapping.Semiterm V ℒₛₑₜ n :=
  ⟨e.val, closed_semiterm e.isSemiterm_zero _⟩

@[simp] lemma cl_val {n : ℕ} (e : Bootstrapping.Term V ℒₛₑₜ) :
    (cl e : Bootstrapping.Semiterm V ℒₛₑₜ n).val = e.val := rfl

@[simp] lemma cl_zero (e : Bootstrapping.Term V ℒₛₑₜ) : (cl e : Bootstrapping.Term V ℒₛₑₜ) = e := by
  ext; simp

@[simp] lemma cl_subst {n m : ℕ} (e : Bootstrapping.Term V ℒₛₑₜ)
    (w : SemitermVec V ℒₛₑₜ n m) : (cl e : Bootstrapping.Semiterm V ℒₛₑₜ n).subst w = cl e := by
  ext; simp [subst_closed e.isSemiterm_zero]

@[simp] lemma cl_shift {n : ℕ} (e : Bootstrapping.Term V ℒₛₑₜ) :
    (cl e : Bootstrapping.Semiterm V ℒₛₑₜ n).shift = cl e.shift := by ext; simp

@[simp] lemma cl_bShift {n : ℕ} (e : Bootstrapping.Term V ℒₛₑₜ) :
    (cl e : Bootstrapping.Semiterm V ℒₛₑₜ n).bShift = cl e := by
  ext; simp only [Bootstrapping.Semiterm.val_bShift, cl_val]; exact bs_closed e.isSemiterm_zero

@[simp] lemma bShift_eq_cl (e : Bootstrapping.Term V ℒₛₑₜ) :
    e.bShift = (cl e : Bootstrapping.Semiterm V ℒₛₑₜ 1) := by
  ext; simp only [Bootstrapping.Semiterm.val_bShift, cl_val]; exact bs_closed e.isSemiterm_zero

@[simp] lemma cl_fvar {n : ℕ} (x : V) :
    (cl (Bootstrapping.Semiterm.fvar x) : Bootstrapping.Semiterm V ℒₛₑₜ n) =
      Bootstrapping.Semiterm.fvar x := by ext; simp

/-- The graph of a typed term at a closed marker. -/
noncomputable def gr {n : ℕ} (e : Bootstrapping.Term V ℒₛₑₜ) (t : Bootstrapping.Semiterm V ℒₒᵣ n) :
    Bootstrapping.Semiformula V ℒₛₑₜ (n + 1) :=
  ⟨G ι e.val (n : V) t.val, by
    simpa using G_semiformula ι (closed_semiterm e.isSemiterm_zero _) _ t.isSemiterm⟩

/-- The translation of a typed formula at a closed marker. -/
noncomputable def jt {n : ℕ} (e : Bootstrapping.Term V ℒₛₑₜ)
    (p : Bootstrapping.Semiformula V ℒₒᵣ n) : Bootstrapping.Semiformula V ℒₛₑₜ n :=
  ⟨J ι e.val (n : V) p.val, J_semiformula ι _ _ p.isSemiformula _ (closed_semiterm e.isSemiterm_zero _)⟩

@[simp] lemma gr_val {n : ℕ} (e : Bootstrapping.Term V ℒₛₑₜ) (t : Bootstrapping.Semiterm V ℒₒᵣ n) :
    (gr ι e t).val = G ι e.val (n : V) t.val := rfl
@[simp] lemma jt_val {n : ℕ} (e : Bootstrapping.Term V ℒₛₑₜ) (p : Bootstrapping.Semiformula V ℒₒᵣ n) :
    (jt ι e p).val = J ι e.val (n : V) p.val := rfl

lemma tmpl_val {k : ℕ} (σ : Semisentence ℒₛₑₜ k) :
    (⌜σ⌝ : Bootstrapping.Semiformula V ℒₛₑₜ k).val = (tq σ : V) := by
  rw [tq_eq]; rfl

@[simp] lemma gr_shift {n : ℕ} (e : Bootstrapping.Term V ℒₛₑₜ) (t : Bootstrapping.Semiterm V ℒₒᵣ n) :
    (gr ι e t).shift = gr ι e.shift t.shift := by
  ext; simp [shift_G ι (closed_semiterm e.isSemiterm_zero _) _ t.isSemiterm]

@[simp] lemma jt_shift {n : ℕ} (e : Bootstrapping.Term V ℒₛₑₜ) (p : Bootstrapping.Semiformula V ℒₒᵣ n) :
    (jt ι e p).shift = jt ι e.shift p.shift := by
  ext; simp [J_shift ι _ _ p.isSemiformula _ (closed_semiterm e.isSemiterm_zero _)]

lemma jt_subst {n m : ℕ} (e : Bootstrapping.Term V ℒₛₑₜ) (w : SemitermVec V ℒₛₑₜ n m)
    (p : Bootstrapping.Semiformula V ℒₒᵣ n) :
    (jt ι e p).subst w = jt ι e (p.subst (lv ⨟ w)) := by
  ext
  simp only [Semiformula.val_substs, jt_val]
  have h := J_subst ι _ _ p.isSemiformula _ (closed_semiterm e.isSemiterm_zero _) _ _
    (SemitermVec.isSemitermVec (lv ⨟ w)) (by exact varVec_of_set w.isSemitermVec)
  rw [subst_closed e.isSemiterm_zero] at h
  rw [h, lv_vec_val]

lemma gr_subst {n m : ℕ} (e : Bootstrapping.Term V ℒₛₑₜ) (w : SemitermVec V ℒₛₑₜ n m)
    (t : Bootstrapping.Semiterm V ℒₒᵣ n) :
    (gr ι e t).subst w.q = gr ι e (t.subst (lv ⨟ w)) := by
  ext
  simp only [Semiformula.val_substs, gr_val, Bootstrapping.Semiterm.val_substs]
  have h := G_subst ι (SemitermVec.isSemitermVec (lv ⨟ w)) (by exact varVec_of_set w.isSemitermVec)
    (closed_semiterm e.isSemiterm_zero _) _ t.isSemiterm
  rw [subst_closed e.isSemiterm_zero] at h
  rw [h, lv_vec_val, SemitermVec.q_val_eq_qVec]
  simp [qVec, w.isSemitermVec.lh]

end ZF207.Internal.Arith
