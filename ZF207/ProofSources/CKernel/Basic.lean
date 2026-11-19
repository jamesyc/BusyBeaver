module
public import ExactHistorySoundness
@[expose] public section
/-! # Derivations in the machine's calculus

The machine searches the numeric calculus `C207Soundness.ExactHistory`. This file
gives the same calculus as derivation trees, in the notation of PA196's logic
kernel (the two calculi share codes, heads and the restricted propositional
axiom; only the gate body differs), and proves that every tree yields an accepted
history. The kernel files that follow are adapted from PA196. -/
namespace ZF207.CKernel
open C207Soundness

def pair (a b : Nat) : Nat := cantor a b

def wim (a b : Nat) := 4 * pair a b
def wel (a b : Nat) := 4 * pair a b + 1
def wal (a b : Nat) := 4 * pair b a + 2
def weq (a b : Nat) := 4 * pair a b + 3
def wn (a : Nat) := wim a 1
def wa (a b : Nat) := wn (wim a (wn b))
def wex (a b : Nat) := wn (wal a (wn b))
def iffCode (a b : Nat) := wa (wim a b) (wim b a)

def head1 (d h : Nat) := wim (wex d (wal d h)) h
def head2 (d a h : Nat) := wim (wal d (wal a h)) (wal a (wal d h))
def head3 (h d a : Nat) := wim (wel h d) (wim (weq h a) (wel a d))
def head4 (h d a : Nat) := wim (weq h d) (wim (wel a h) (wel a d))
def head5 (d h : Nat) := wex d (weq h d)
def head6 (d a h : Nat) := wim (wal d a) (wim (wal d (wim a h)) (wal d h))
def rho8 (a b c u : Nat) := wim (wim (wim c u) a) (wim (wim a c) (wim b c))

def eqVac (a b c : Nat) := wim (weq a b) (wal c (weq a b))
def memVac (a b c : Nat) := wim (wel a b) (wal c (wel a b))
/-- The body of the pointed Scott-hull gate, quantified over label `c`. -/
def qGate (a b c : Nat) : Nat := allCode c (gateBody c b a)
  where gateBody (a d h : Nat) : Nat := (impCode (allCode h (impCode (memCode h a) (impCode (allCode d (impCode a (impCode (allCode d (impCode (allCode a (impCode (memCode a d) (memCode a h))) (allCode h (impCode a (impCode (allCode h (impCode a (impCode (memCode h a) 1))) 1))))) 1))) 1))) (impCode (impCode a (memCode h a)) 1))
def oldGate (a b c : Nat) := wn (wim (memVac a b c) (qGate a b c))
/-- The machine's gate: label `c` must differ from `a` and `b`. -/
def bundle (a b c : Nat) := wn (wim (eqVac a b c) (wim (memVac a b c) (qGate a b c)))

theorem bundle_eq (a b c : Nat) : bundle a b c = pointedGateCode c b a := rfl


inductive Derivation : Nat → Type where
  | mp {a b} : Derivation a → Derivation (wim a b) → Derivation b
  | all (a) {b} : Derivation b → Derivation (wal a b)
  | h1 (d h) : Derivation (head1 d h)
  | h2 (d a h) : Derivation (head2 d a h)
  | h3 (h d a) : Derivation (head3 h d a)
  | h4 (h d a) : Derivation (head4 h d a)
  | h5 (d h) : Derivation (head5 d h)
  | h6 (d a h) : Derivation (head6 d a h)
  | r8 (a b c u) : u ≤ a → Derivation (rho8 a b c u)
  | gate (a b c) : c ≠ a → c ≠ b → Derivation (bundle a b c)

theorem pair_bounds (a b : Nat) : a ≤ pair a b ∧ b ≤ pair a b :=
  ⟨cantor_ge_left a b, cantor_ge_right a b⟩

theorem wim_bounds (a b : Nat) : a ≤ wim a b ∧ b ≤ wim a b := by
  have h := pair_bounds a b
  simp only [wim]
  omega

theorem wel_bounds (a b : Nat) : a < wel a b ∧ b < wel a b := by
  have h := pair_bounds a b
  simp only [wel]
  omega

theorem wn_strict (a : Nat) : a < wn a := by
  have h := pair_bounds a 1
  simp only [wn, wim]
  omega

/-! ## Trees give accepted histories -/

theorem history_append {xs ys : List Nat} (hx : ExactHistory xs) (hy : ExactHistory ys) :
    ExactHistory (xs ++ ys) := by
  induction hx with
  | nil => simpa using hy
  | axRule n xs _ hax ih => exact ExactHistory.axRule n _ ih hax
  | mp b c xs _ hb hi ih =>
    exact ExactHistory.mp b c _ ih (List.mem_append_left _ hb) (List.mem_append_left _ hi)
  | gen i b xs _ hb ih => exact ExactHistory.gen i b _ ih (List.mem_append_left _ hb)

theorem provable_ax {n : Nat} (h : ExactAxiom n) : ExactProvable n :=
  ⟨[n], ExactHistory.axRule n [] ExactHistory.nil h, List.mem_singleton_self n⟩

theorem provable_mp {b c : Nat} (hb : ExactProvable b) (hbc : ExactProvable (impCode b c)) :
    ExactProvable c := by
  obtain ⟨xs, hx, hbx⟩ := hb
  obtain ⟨ys, hy, hcy⟩ := hbc
  refine ⟨c :: (xs ++ ys), ExactHistory.mp b c _ (history_append hx hy)
    (List.mem_append_left _ hbx) (List.mem_append_right _ hcy), List.mem_cons_self⟩

theorem provable_gen {b : Nat} (i : Nat) (hb : ExactProvable b) : ExactProvable (allCode i b) := by
  obtain ⟨xs, hx, hbx⟩ := hb
  exact ⟨allCode i b :: xs, ExactHistory.gen i b xs hx hbx, List.mem_cons_self⟩

/-- Every derivation tree yields a history accepted by the machine's checker. -/
theorem Derivation.provable {n : Nat} (d : Derivation n) : ExactProvable n := by
  induction d with
  | mp _ _ ih₁ ih₂ => exact provable_mp ih₁ ih₂
  | all a _ ih => exact provable_gen a ih
  | h1 d h =>
    exact provable_ax (Or.inr ⟨0, d, h, 0, (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))⟩)
  | h2 d a h =>
    exact provable_ax (Or.inr ⟨a, d, h, 0, (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩)
  | h3 h d a =>
    exact provable_ax (Or.inr ⟨a, d, h, 0, (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩)
  | h4 h d a =>
    exact provable_ax (Or.inr ⟨a, d, h, 0, (Or.inr (Or.inr (Or.inl rfl)))⟩)
  | h5 d h =>
    exact provable_ax (Or.inr ⟨0, d, h, 0, (Or.inr (Or.inl rfl))⟩)
  | h6 d a h =>
    exact provable_ax (Or.inr ⟨a, d, h, 0, (Or.inl rfl)⟩)
  | r8 a b c u hu =>
    exact provable_ax (Or.inr ⟨b, a, c, u, (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, rfl⟩)))))))⟩)
  | gate a b c hca hcb =>
    exact provable_ax (Or.inr ⟨c, b, a, 0, (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hcb, hca, rfl⟩)))))))⟩)

end ZF207.CKernel
