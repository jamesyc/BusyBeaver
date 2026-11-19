module
public import NumericTransform
@[expose] public section
namespace ZFR
open C207Soundness

def sourceCons (a l : Nat) := cantor a l + 1
def sourceSequent (g a : Nat) := cantor 0 (cantor g a)
def sourceBranches (g a b c : Nat) := cantor 1 (cantor g (cantor a (cantor b c)))

/-- Exact Peano-list map of sfShift 0, not a typed encode-image definition. -/
def sourceContextShift (g : Nat) := encodeList (sourceShift 0) (decodeSourceList g)

theorem sourceContextShift_zero : sourceContextShift 0 = 0 := by
 simp [sourceContextShift, decodeSourceList_zero, encodeList]

theorem sourceContextShift_cons (a g : Nat) :
 sourceContextShift (sourceCons a g) = sourceCons (sourceShift 0 a) (sourceContextShift g) := by
 simp only [sourceContextShift, sourceCons, decodeSourceList_cons, encodeList]

theorem encodeList_map (f : β → Nat) (g : α → β) (xs : List α) :
 encodeList f (xs.map g) = encodeList (f ∘ g) xs := by
 induction xs <;> simp_all [encodeList]

theorem sourceContextShift_encode (Γ : Context) :
 sourceContextShift (encodeContext Γ) = encodeContext (shiftContext Γ) := by
 simp only [sourceContextShift, encodeContext, decodeSourceList_encode, shiftContext, encodeList_map]
 have he : sourceShift 0 ∘ encodeFormula = encodeFormula ∘ shift := by
   funext a; exact sourceShift_encode a
 rw [he]

def sourceBase (r : Nat) : Prop := sourceRowWf r ∧
 ((∃ g a, r = sourceSequent g a ∧ sourceMember a g) ∨
  ∃ g a b, r = sourceSequent g (sourceNode 5 (sourceNode 5 (sourceNode 5 a b) a) a))

def sourceUnary (p r : Nat) : Prop := sourceRowWf r ∧ (
 (∃ g a b, r = sourceSequent g (sourceNode 5 a b) ∧ p = sourceSequent (sourceCons a g) b) ∨
 (∃ g a, r = sourceSequent g a ∧ p = sourceSequent g 0) ∨
 (∃ g a b, r = sourceSequent g a ∧ p = sourceSequent g (sourceNode 3 a b)) ∨
 (∃ g a b, r = sourceSequent g b ∧ p = sourceSequent g (sourceNode 3 a b)) ∨
 (∃ g a b, r = sourceSequent g (sourceNode 4 a b) ∧ p = sourceSequent g a) ∨
 (∃ g a b, r = sourceSequent g (sourceNode 4 a b) ∧ p = sourceSequent g b) ∨
 (∃ g h a, r = sourceSequent h a ∧ p = sourceSequent g a ∧ sourceContextSub g h) ∨
 (∃ g a, r = sourceSequent g (sourceNode 6 a 0) ∧ p = sourceSequent (sourceContextShift g) a) ∨
 (∃ g a t, r = sourceSequent g (sourceSubst 0 t a) ∧ p = sourceSequent g (sourceNode 6 a 0)) ∨
 (∃ g a t, r = sourceSequent g (sourceNode 7 a 0) ∧ p = sourceSequent g (sourceSubst 0 t a)))

def sourceBinary (p q r : Nat) : Prop := sourceRowWf r ∧ (
 (∃ g a b, r = sourceSequent g b ∧ p = sourceSequent g (sourceNode 5 a b) ∧ q = sourceSequent g a) ∨
 (∃ g a b, r = sourceSequent g (sourceNode 3 a b) ∧ p = sourceSequent g a ∧ q = sourceSequent g b) ∨
 (∃ g a b c, r = sourceBranches g a b c ∧ p = sourceSequent (sourceCons a g) c ∧ q = sourceSequent (sourceCons b g) c) ∨
 (∃ g a b c, r = sourceSequent g c ∧ p = sourceSequent g (sourceNode 4 a b) ∧ q = sourceBranches g a b c) ∨
 (∃ g a c, r = sourceSequent g c ∧ p = sourceSequent g (sourceNode 7 a 0) ∧ q = sourceSequent (sourceCons a (sourceContextShift g)) (sourceShift 0 c)))

theorem Base.encode {r : Row} (h : Base r) : sourceBase (encodeRow r) := by
 refine ⟨sourceRowWf_encode r, ?_⟩
 cases h with
 | @ctx Γ a ha =>
   left; exact ⟨encodeContext Γ, encodeFormula a, rfl,
     (sourceMember_encode_iff encodeFormula_injective a Γ).mpr ha⟩
 | pc Γ a b => right; exact ⟨encodeContext Γ, encodeFormula a, encodeFormula b, rfl⟩

theorem Unary.encode {p r : Row} (h : Unary p r) : sourceUnary (encodeRow p) (encodeRow r) := by
 refine ⟨sourceRowWf_encode r, ?_⟩
 cases h with
 | @ii Γ a b =>
   left
   refine ⟨encodeContext Γ, encodeFormula a, encodeFormula b, ?_⟩
   simp only [encodeRow, encodeFormula, sourceSequent, sourceBranches, sourceCons,
     sourceContextShift_encode, sourceShift_encode, sourceSubst_encode, encodeContext, encodeList]
   trivial
 | @exp Γ a =>
   right; left
   refine ⟨encodeContext Γ, encodeFormula a, ?_⟩
   try rw [sourceContextShift_encode]
   simp only [encodeRow, encodeFormula, sourceSequent, sourceBranches, sourceCons,
     sourceContextShift_encode, sourceShift_encode, sourceSubst_encode, encodeContext, encodeList]
   trivial
 | @ce1 Γ a b =>
   right; right; left
   refine ⟨encodeContext Γ, encodeFormula a, encodeFormula b, ?_⟩
   simp only [encodeRow, encodeFormula, sourceSequent, sourceBranches, sourceCons,
     sourceContextShift_encode, sourceShift_encode, sourceSubst_encode, encodeContext, encodeList]
   trivial
 | @ce2 Γ a b =>
   right; right; right; left
   refine ⟨encodeContext Γ, encodeFormula a, encodeFormula b, ?_⟩
   simp only [encodeRow, encodeFormula, sourceSequent, sourceBranches, sourceCons,
     sourceContextShift_encode, sourceShift_encode, sourceSubst_encode, encodeContext, encodeList]
   trivial
 | @di1 Γ a b =>
   right; right; right; right; left
   refine ⟨encodeContext Γ, encodeFormula a, encodeFormula b, ?_⟩
   simp only [encodeRow, encodeFormula, sourceSequent, sourceBranches, sourceCons,
     sourceContextShift_encode, sourceShift_encode, sourceSubst_encode, encodeContext, encodeList]
   trivial
 | @di2 Γ a b =>
   right; right; right; right; right; left
   refine ⟨encodeContext Γ, encodeFormula a, encodeFormula b, ?_⟩
   simp only [encodeRow, encodeFormula, sourceSequent, sourceBranches, sourceCons,
     sourceContextShift_encode, sourceShift_encode, sourceSubst_encode, encodeContext, encodeList]
   trivial
 | @wk Γ Δ a hs =>
   right; right; right; right; right; right; left
   refine ⟨encodeContext Γ, encodeContext Δ, encodeFormula a, ?_⟩
   simp only [encodeRow, encodeFormula, sourceSequent, sourceBranches, sourceCons,
     sourceContextShift_encode, sourceShift_encode, sourceSubst_encode, encodeContext, encodeList]
   exact ⟨True.intro,True.intro,(sourceContextSub_encode_iff Γ Δ).mpr hs⟩
 | @allI Γ a =>
   right; right; right; right; right; right; right; left
   refine ⟨encodeContext Γ, encodeFormula a, ?_⟩
   try rw [sourceContextShift_encode]
   simp only [encodeRow, encodeFormula, sourceSequent, sourceBranches, sourceCons,
     sourceContextShift_encode, sourceShift_encode, sourceSubst_encode, encodeContext, encodeList]
   trivial
 | @allE Γ a t =>
   right; right; right; right; right; right; right; right; left
   refine ⟨encodeContext Γ, encodeFormula a, t, ?_⟩
   simp only [encodeRow, encodeFormula, sourceSequent, sourceBranches, sourceCons,
     sourceContextShift_encode, sourceShift_encode, sourceSubst_encode, encodeContext, encodeList]
   trivial
 | @exI Γ a t =>
   right; right; right; right; right; right; right; right; right; 
   refine ⟨encodeContext Γ, encodeFormula a, t, ?_⟩
   simp only [encodeRow, encodeFormula, sourceSequent, sourceBranches, sourceCons,
     sourceContextShift_encode, sourceShift_encode, sourceSubst_encode, encodeContext, encodeList]
   trivial

theorem Binary.encode {p q r : Row} (h : Binary p q r) : sourceBinary (encodeRow p) (encodeRow q) (encodeRow r) := by
 refine ⟨sourceRowWf_encode r, ?_⟩
 cases h with
 | @ie Γ a b =>
   left
   refine ⟨encodeContext Γ, encodeFormula a, encodeFormula b, ?_⟩
   simp only [encodeRow, encodeFormula, sourceSequent, sourceBranches, sourceCons,
     sourceContextShift_encode, sourceShift_encode, sourceSubst_encode, encodeContext, encodeList]
   trivial
 | @ci Γ a b =>
   right; left
   refine ⟨encodeContext Γ, encodeFormula a, encodeFormula b, ?_⟩
   simp only [encodeRow, encodeFormula, sourceSequent, sourceBranches, sourceCons,
     sourceContextShift_encode, sourceShift_encode, sourceSubst_encode, encodeContext, encodeList]
   trivial
 | @branchPair Γ a b c =>
   right; right; left
   refine ⟨encodeContext Γ, encodeFormula a, encodeFormula b, encodeFormula c, ?_⟩
   simp only [encodeRow, encodeFormula, sourceSequent, sourceBranches, sourceCons,
     sourceContextShift_encode, sourceShift_encode, sourceSubst_encode, encodeContext, encodeList]
   trivial
 | @de Γ a b c =>
   right; right; right; left
   refine ⟨encodeContext Γ, encodeFormula a, encodeFormula b, encodeFormula c, ?_⟩
   simp only [encodeRow, encodeFormula, sourceSequent, sourceBranches, sourceCons,
     sourceContextShift_encode, sourceShift_encode, sourceSubst_encode, encodeContext, encodeList]
   trivial
 | @exE Γ a c =>
   right; right; right; right; 
   refine ⟨encodeContext Γ, encodeFormula a, encodeFormula c, ?_⟩
   try rw [sourceContextShift_encode]
   simp only [encodeRow, encodeFormula, sourceSequent, sourceBranches, sourceCons,
     sourceContextShift_encode, sourceShift_encode, sourceSubst_encode, encodeContext, encodeList]
   trivial

end ZFR
