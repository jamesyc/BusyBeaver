module
public import I3_334Support.Equations.Meredith
@[expose] public section

namespace PalomarI3380

namespace MeredithLaws

variable {A : Type} {m : A → A → A} {n : A → A}

def Le (m : A → A → A) (x y : A) : Prop := m x y = x

def sup (m : A → A → A) (n : A → A) (x y : A) : A := n (m (n x) (n y))

def top (m : A → A → A) (n : A → A) (witness : A) : A := sup m n witness (n witness)

def bottom (m : A → A → A) (n : A → A) (witness : A) : A := n (top m n witness)

theorem le_refl (l : MeredithLaws m n) (x : A) : Le m x x := l.idempotent x

theorem le_trans (l : MeredithLaws m n) {x y z : A} (hxy : Le m x y) (hyz : Le m y z) :
    Le m x z := by
  unfold Le at *
  rw [← hxy, l.associative, hyz, hxy]

theorem le_antisymm (l : MeredithLaws m n) {x y : A} (hxy : Le m x y) (hyx : Le m y x) :
    x = y := hxy.symm.trans ((l.commutative x y).trans hyx)

theorem inf_le_left (l : MeredithLaws m n) (x y : A) : Le m (m x y) x := by
  unfold Le
  rw [l.commutative (m x y) x, ← l.associative, l.idempotent]

theorem inf_le_right (l : MeredithLaws m n) (x y : A) : Le m (m x y) y := by
  unfold Le
  rw [l.associative, l.idempotent]

theorem le_inf (l : MeredithLaws m n) {x y z : A} :
    Le m x (m y z) ↔ Le m x y ∧ Le m x z := by
  constructor
  · intro h
    exact ⟨l.le_trans h (l.inf_le_left y z), l.le_trans h (l.inf_le_right y z)⟩
  · rintro ⟨hy, hz⟩
    unfold Le at *
    rw [← l.associative, hy, hz]

theorem sup_comm (l : MeredithLaws m n) (x y : A) : sup m n x y = sup m n y x := by
  unfold sup
  rw [l.commutative]

theorem sup_assoc (l : MeredithLaws m n) (x y z : A) :
    sup m n (sup m n x y) z = sup m n x (sup m n y z) := by
  simp only [sup, l.involution, l.associative]

theorem inf_sup_absorb (l : MeredithLaws m n) (x y : A) : m x (sup m n x y) = x :=
  l.absorption x (n y)

theorem sup_inf_absorb (l : MeredithLaws m n) (x y : A) : sup m n x (m x y) = x := by
  have h := congrArg n (l.inf_sup_absorb (n x) (n y))
  simp only [sup, l.involution] at h ⊢
  exact h

theorem le_iff_sup (l : MeredithLaws m n) (x y : A) : Le m x y ↔ sup m n x y = y := by
  constructor
  · intro h
    have hy : m y x = x := (l.commutative y x).trans h
    have eq := l.sup_inf_absorb y x
    rw [hy] at eq
    exact (l.sup_comm x y).trans eq
  · intro h
    have eq := l.inf_sup_absorb x y
    rwa [h] at eq

theorem neg_order (l : MeredithLaws m n) (x y : A) : Le m (n y) (n x) ↔ Le m x y := by
  rw [l.le_iff_sup]
  simp only [sup, l.involution]
  rw [l.commutative y x]
  constructor
  · intro h
    have eq := congrArg n h
    simpa only [l.involution, Le] using eq
  · exact congrArg n

theorem sup_le (l : MeredithLaws m n) {x y z : A} :
    Le m (sup m n x y) z ↔ Le m x z ∧ Le m y z := by
  rw [← l.neg_order (sup m n x y) z]
  simp only [sup, l.involution, l.le_inf, l.neg_order]

theorem le_sup_left (l : MeredithLaws m n) (a b : A) :
    Le m a (sup m n a b) := l.inf_sup_absorb a b

theorem le_sup_right (l : MeredithLaws m n) (a b : A) :
    Le m b (sup m n a b) := by
  rw [l.sup_comm]
  exact l.le_sup_left b a

theorem inf_mono (l : MeredithLaws m n) {a b c d : A} (h₁ : Le m a c) (h₂ : Le m b d) :
    Le m (m a b) (m c d) :=
  l.le_inf.mpr ⟨l.le_trans (l.inf_le_left a b) h₁, l.le_trans (l.inf_le_right a b) h₂⟩

private theorem sup_contract (l : MeredithLaws m n) (x y : A) :
    sup m n x (m (n x) y) = sup m n x y := by
  unfold sup
  have h := l.complement_meet (n x) y
  rw [l.commutative (n (m (n x) y)), l.commutative (n y)] at h
  exact congrArg n h

theorem le_top (l : MeredithLaws m n) (w x : A) : Le m x (top m n w) := by
  apply (l.le_iff_sup _ _).mpr
  calc
    sup m n x (top m n w) = sup m n (sup m n w (n w)) x := l.sup_comm _ _
    _ = sup m n w (sup m n (n w) x) := l.sup_assoc _ _ _
    _ = sup m n w (m (n w) (sup m n (n w) x)) := (l.sup_contract _ _).symm
    _ = top m n w := by rw [l.inf_sup_absorb]; rfl

theorem bottom_le (l : MeredithLaws m n) (w x : A) : Le m (bottom m n w) x := by
  apply (l.neg_order _ _).mp
  simpa only [bottom, l.involution] using l.le_top w (n x)

theorem bottom_meet (l : MeredithLaws m n) (w x : A) :
    m (bottom m n w) x = bottom m n w := l.bottom_le w x

theorem inf_complement (l : MeredithLaws m n) (w x : A) :
    m x (n x) = bottom m n w := by
  have self : m x (n x) = bottom m n x := by
    simp only [bottom, top, sup, l.involution]
    exact l.commutative _ _
  rw [self]
  exact l.le_antisymm (l.bottom_le x _) (l.bottom_le w _)

theorem disjoint_iff_le (l : MeredithLaws m n) (w x y : A) :
    m x (n y) = bottom m n w ↔ Le m x y := by
  constructor
  · intro h
    have h' := l.complement_meet (n y) x
    rw [l.commutative (n y) x, h, bottom, l.involution] at h'
    have hy : m (top m n w) (n y) = n y :=
      (l.commutative _ _).trans (l.le_top w (n y))
    rw [hy, l.commutative (n x) (n y)] at h'
    exact (l.neg_order x y).mp h'.symm
  · intro h
    have h' := l.complement_meet x y
    change m x y = x at h
    rw [h, l.commutative (n x) x, l.inf_complement w x, l.commutative (n y) x] at h'
    exact h'.symm

theorem inf_residual (l : MeredithLaws m n) (w x y z : A) :
    Le m (m x y) z ↔ Le m x (sup m n (n y) z) := by
  rw [← l.disjoint_iff_le w (m x y) z, ← l.disjoint_iff_le w x (sup m n (n y) z)]
  simp only [sup, l.involution, l.associative]

theorem inf_sup (l : MeredithLaws m n) (w x y z : A) :
    m x (sup m n y z) = sup m n (m x y) (m x z) := by
  have adj (a : A) : Le m (m x (sup m n y z)) a ↔ Le m (sup m n (m x y) (m x z)) a := by
    calc
      _ ↔ Le m (sup m n y z) (sup m n (n x) a) := by
        rw [l.commutative x (sup m n y z), l.inf_residual w]
      _ ↔ Le m y (sup m n (n x) a) ∧ Le m z (sup m n (n x) a) := l.sup_le
      _ ↔ Le m (m x y) a ∧ Le m (m x z) a := by
        rw [← l.inf_residual w y x a, ← l.inf_residual w z x a, l.commutative y x, l.commutative z x]
      _ ↔ _ := l.sup_le.symm
  exact l.le_antisymm ((adj _).mpr (l.le_refl _)) ((adj _).mp (l.le_refl _))

theorem relative_complement (l : MeredithLaws m n) (w e a : A) (he : Le m e a) :
    sup m n e (m a (n e)) = a := by
  change m e a = e at he
  have all : top m n e = top m n w :=
    l.le_antisymm (l.le_top w _) (l.le_top e _)
  have h := l.inf_sup w a e (n e)
  change m a (top m n e) = sup m n (m a e) (m a (n e)) at h
  rw [all, l.le_top w a, l.commutative a e, he] at h
  exact h.symm

theorem sup_bottom (l : MeredithLaws m n) (w x : A) : sup m n x (bottom m n w) = x :=
  (l.sup_comm _ _).trans ((l.le_iff_sup _ _).mp (l.bottom_le w x))

end MeredithLaws
end PalomarI3380
