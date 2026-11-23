module
public import I3_334Support.RelationAlgebra.Domain
public import I3_334Support.Search.RewriteVerifier
@[expose] public section

namespace PalomarI3380

/-- The term algebra is countable because a ground term is recovered
from its Polish word. Unrecognised symbols are evaluated at top. -/
def syntaxAlgebra : Algebra ClosedTerm where
  constant := .const
  neg := .neg
  converse := .converse
  choice := .choice
  localRel := .localRel
  nand := .nand
  product := .product
  node := .node

theorem evaluate_syntax (t : ClosedTerm) : syntaxAlgebra.eval Empty.elim t = t := by
  induction t <;> simp only [Algebra.eval, *] <;> try rfl
  case var x => exact x.elim

def enumerateTerm (code : Nat) : ClosedTerm :=
  ((readTree code).map fun r => r.1.evaluate syntaxAlgebra).getD (.const .D)

theorem enumerateTerm_surjective (t : ClosedTerm) : ∃ code, enumerateTerm code = t := by
  refine ⟨t.raw.encode, ?_⟩
  have h := readTree_complete t.raw 0
  unfold enumerateTerm RawTerm.encode
  rw [h]
  change t.raw.evaluate syntaxAlgebra = t
  unfold ClosedTerm.raw
  rw [Term.evaluate_toRaw]
  have hEmpty : (fun v : Empty => (Empty.elim v : RawTerm).evaluate syntaxAlgebra) = Empty.elim :=
    funext (fun v => v.elim)
  rw [hEmpty, evaluate_syntax]

theorem termClasses_countable (E : List Equation) :
    ∃ enumerate : Nat → Derives.Classes E, ∀ x, ∃ n, enumerate n = x := by
  refine ⟨fun n => Derives.classOf E (enumerateTerm n), fun x => ?_⟩
  obtain ⟨t, eq⟩ := Quotient.exists_rep x
  obtain ⟨n, hn⟩ := enumerateTerm_surjective t
  refine ⟨n, ?_⟩
  change Derives.classOf E (enumerateTerm n) = x
  rw [hn]
  exact eq

structure SubidentityUltrafilter {A : Type} (M : Algebra A) where
  member : A → Prop
  subunit : ∀ {x}, member x → M.le x (M.constant .I)
  unit_mem : member (M.constant .I)
  zero_not_mem : ¬ member M.zero
  filter_up : ∀ {x y}, member x → M.le x y → M.le y (M.constant .I) → member y
  filter_inf : ∀ {x y}, member x → member y → member (M.inf x y)
  decide_piece : ∀ x, M.le x (M.constant .I) → member x ∨ member (M.inf (M.constant .I) (M.neg x))

namespace SubidentityUltrafilter

variable {A : Type} {M : Algebra A} (L : RelationLaws M)
include L

open Classical in
noncomputable def descend (M : Algebra A) (enumerate : Nat → A) (seed : A) : Nat → A
  | 0 => seed
  | i + 1 =>
    let previous := descend M enumerate seed i
    let part := M.inf previous (enumerate i)
    if part = M.zero then previous else part

private theorem descend_step (enumerate : Nat → A) (seed : A) (i : Nat) :
    M.le (descend M enumerate seed (i + 1)) (descend M enumerate seed i) := by
  simp only [descend]
  split
  · exact L.bool.le_refl _
  · exact L.bool.inf_le_left _ _

private theorem descend_mono (enumerate : Nat → A) (seed : A) {i j : Nat} (h : i ≤ j) :
    M.le (descend M enumerate seed j) (descend M enumerate seed i) := by
  induction h with
  | refl => exact L.bool.le_refl _
  | step _ ih => exact L.bool.le_trans (descend_step L enumerate seed _) ih

omit L in
private theorem descend_nonzero (enumerate : Nat → A) (seed : A) (hne : seed ≠ M.zero) (i : Nat) :
    descend M enumerate seed i ≠ M.zero := by
  induction i with
  | zero => exact hne
  | succ i ih =>
    simp only [descend]
    split
    · exact ih
    · assumption

/-- A directed descending family generates a proper filter. Deciding
each subidentity makes it an ultrafilter. The index order need not be
the standard natural numbers. -/
noncomputable def ofDescending {I : Type} (before : I → I → Prop) (initial : I)
    (common : ∀ i j, ∃ k, before i k ∧ before j k)
    (chain : I → A) (decreasing : ∀ i j, before i j → M.le (chain j) (chain i))
    (subunit : ∀ i, M.le (chain i) (M.constant .I)) (nonzero : ∀ i, chain i ≠ M.zero)
    (decisions : ∀ x, M.le x (M.constant .I) →
      (∃ i, M.le (chain i) x) ∨ ∃ i, M.le (chain i) (M.inf (M.constant .I) (M.neg x))) :
    SubidentityUltrafilter M where
  member x := M.le x (M.constant .I) ∧ ∃ i, M.le (chain i) x
  subunit h := h.1
  unit_mem := ⟨L.bool.le_refl _,initial,subunit initial⟩
  zero_not_mem := fun ⟨_,i,hi⟩ => nonzero i ((L.le_zero_iff _).mp hi)
  filter_up := fun ⟨_,i,hi⟩ hxy hy => ⟨hy,i,L.bool.le_trans hi hxy⟩
  filter_inf := by
    rintro x y ⟨hx,i,hi⟩ ⟨hy,j,hj⟩
    obtain ⟨k,ik,jk⟩ := common i j
    refine ⟨L.bool.le_trans (L.bool.inf_le_left _ _) hx,k,L.bool.le_inf.mpr ?_⟩
    exact ⟨L.bool.le_trans (decreasing i k ik) hi,L.bool.le_trans (decreasing j k jk) hj⟩
  decide_piece := fun x hx => (decisions x hx).elim
    (fun h => Or.inl ⟨hx,h⟩)
    (fun h => Or.inr ⟨L.bool.inf_le_left _ _,h⟩)

/-- A nonzero subidentity is contained in an ultrafilter. We only need
this for countable algebras, and decide the enumerated elements in order. -/
theorem exists_containing (enumerate : Nat → A) (surjective : ∀ x, ∃ n, enumerate n = x)
    (seed : A) (hSeed : M.le seed (M.constant .I)) (hne : seed ≠ M.zero) :
    ∃ F : SubidentityUltrafilter M, F.member seed := by
  classical
  let chain := descend M enumerate seed
  have subid (i : Nat) : M.le (chain i) (M.constant .I) :=
    L.bool.le_trans (descend_mono L enumerate seed (Nat.zero_le i)) hSeed
  have decision (x : A) (_ : M.le x (M.constant .I)) :
      (∃ i, M.le (chain i) x) ∨ ∃ i, M.le (chain i) (M.inf (M.constant .I) (M.neg x)) := by
    obtain ⟨i,atIndex⟩ := surjective x
    by_cases empty : M.inf (chain i) x = M.zero
    · have hNot : M.le (chain i) (M.neg x) := by
        apply (L.bool.disjoint_iff_le (M.constant .I) _ _).mp
        rw [L.bool.involution,empty]
      exact Or.inr ⟨i,L.bool.le_inf.mpr ⟨subid i,hNot⟩⟩
    · have eqStep : chain (i+1) = M.inf (chain i) x := by
        change descend M enumerate seed (i+1) = M.inf (descend M enumerate seed i) x
        rw [descend]
        simp only [atIndex,show ¬M.inf (descend M enumerate seed i) x = M.zero from empty,↓reduceIte]
      exact Or.inl ⟨i+1,by rw [eqStep]; exact L.bool.inf_le_right _ _⟩
  let F := ofDescending L (fun i j : Nat => i ≤ j) 0
    (fun i j => ⟨max i j,Nat.le_max_left _ _,Nat.le_max_right _ _⟩)
    chain (fun _ _ h => descend_mono L _ _ h) subid
    (descend_nonzero enumerate seed hne) decision
  exact ⟨F,hSeed,0,L.bool.le_refl _⟩

variable {F : SubidentityUltrafilter M}

theorem mem_inf {x y : A} (hx : M.le x (M.constant .I)) (hy : M.le y (M.constant .I)) :
    F.member (M.inf x y) ↔ F.member x ∧ F.member y :=
  ⟨fun h => ⟨F.filter_up h (L.bool.inf_le_left _ _) hx, F.filter_up h (L.bool.inf_le_right _ _) hy⟩,
    fun h => F.filter_inf h.1 h.2⟩

theorem mem_sup {x y : A} (hx : M.le x (M.constant .I)) (hy : M.le y (M.constant .I)) :
    F.member (M.sup x y) ↔ F.member x ∨ F.member y := by
  classical
  constructor
  · intro mem
    by_cases mX : F.member x
    · exact Or.inl mX
    · by_cases mY : F.member y
      · exact Or.inr mY
      · have nx := (F.decide_piece x hx).resolve_left mX
        have ny := (F.decide_piece y hy).resolve_left mY
        let e := M.inf (M.inf (M.constant .I) (M.neg x)) (M.inf (M.constant .I) (M.neg y))
        have below : M.le e (M.neg (M.sup x y)) := by
          have he : M.le e (M.inf (M.neg x) (M.neg y)) :=
            L.bool.inf_mono (L.bool.inf_le_right _ _) (L.bool.inf_le_right _ _)
          simpa only [MeredithLaws.sup, L.bool.involution] using he
        have hZero : M.inf (M.sup x y) e = M.zero :=
          L.inf_under_complement (L.bool.inf_le_left _ _)
            (L.bool.le_trans (L.bool.inf_le_right _ _) below)
        have impossible := F.filter_inf mem (F.filter_inf nx ny)
        change F.member (M.inf (M.sup x y) e) at impossible
        rw [hZero] at impossible
        exact (F.zero_not_mem impossible).elim
  · intro h
    have subid := L.bool.sup_le.mpr ⟨hx, hy⟩
    exact h.elim (fun hx => F.filter_up hx (L.bool.le_sup_left _ _) subid)
      (fun hy => F.filter_up hy (L.bool.le_sup_right _ _) subid)

end SubidentityUltrafilter
end PalomarI3380
