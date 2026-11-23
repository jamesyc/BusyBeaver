module
public import I3_334Support.Logic.Deduction
public import I3_334Support.Logic.FormulaListing
public import I3_334Support.Logic.NamedParameters
public import I3_334Support.Logic.ExpandedTemplates
@[expose] public section

namespace PalomarI3380.Logic

private theorem lower_expand (p : Formula) (n : Nat) :
    (Expanded.Formula.membership (V := Nat) p).lower id n = p := by
  induction p generalizing n <;>
    simp [Expanded.Formula.membership,Expanded.Formula.lower,Expanded.Argument.lower, *]

def formulaListing : Expanded.Listing Formula where
  get i := ((Expanded.Listing.formulas ⟨id,fun x => ⟨x,rfl⟩⟩).get i).lower id 0
  contains p := by
    obtain ⟨i,hi⟩ :=
      (Expanded.Listing.formulas ⟨id,fun x => ⟨x,rfl⟩⟩).contains (Expanded.Formula.membership (V := Nat) p)
    exact ⟨i,by simp only [hi,lower_expand]⟩

namespace Theory

variable {T U : Theory}

structure BoundedExtension (T : Theory) where
  theory : Theory
  original : ∀ p, T p → theory p
  consistent : theory.Consistent
  bound : Nat
  bounded : ∀ p, theory p → Bound p bound

namespace BoundedExtension

noncomputable def deciding (B : BoundedExtension T) (p : Formula) : BoundedExtension T := by
  classical
  let n := Classical.choose (formula_bounded p)
  have hn : Bound p n := Classical.choose_spec (formula_bounded p)
  let m := max B.bound n
  have inBound (q : Formula) (hq : B.theory q) : Bound q m := bound_weaken (B.bounded q hq) (by omega)
  have pBound : Bound p m := bound_weaken hn (by omega)
  exact if h : (B.theory.add p).Consistent then
    ⟨B.theory.add p,fun q hq => Or.inr (B.original q hq),h,m,add_bounded inBound pBound⟩
  else
    ⟨B.theory.add (Neg p),fun q hq => Or.inr (B.original q hq),
      (either_extension B.consistent p).resolve_left h,m,add_bounded inBound ⟨pBound,trivial⟩⟩

theorem deciding_extends (B : BoundedExtension T) (p q : Formula) (hq : B.theory q) :
    (B.deciding p).theory q := by
  classical
  simp only [deciding]
  split <;> exact Or.inr hq

theorem deciding_decides (B : BoundedExtension T) (p : Formula) :
    (B.deciding p).theory p ∨ (B.deciding p).theory (Neg p) := by
  classical
  simp only [deciding]
  split
  · exact Or.inl (Or.inl rfl)
  · exact Or.inr (Or.inl rfl)

noncomputable def withWitness (B : BoundedExtension T) (a : Formula) : BoundedExtension T := by
  classical
  let m := Classical.choose (formula_bounded a)
  have hm : Bound a m := Classical.choose_spec (formula_bounded a)
  let n := max B.bound m
  have inBound (q : Formula) (hq : B.theory q) : Bound q n := bound_weaken (B.bounded q hq) (by omega)
  have aBound : Bound a (n+1) := bound_weaken hm (by omega)
  exact if h : B.theory.Derives (.ex a) then
    ⟨B.theory.add (subst n a),fun q hq => Or.inr (B.original q hq),
      witness_consistent B.consistent inBound aBound h,n+1,
      add_bounded (fun q hq => bound_weaken (inBound q hq) (by omega))
        (rename_bounded a aBound (substMap n) fun i hi => by cases i <;> simp [substMap] <;> omega)⟩
  else B

theorem withWitness_extends (B : BoundedExtension T) (a q : Formula) (hq : B.theory q) :
    (B.withWitness a).theory q := by
  classical
  simp only [withWitness]
  split
  · exact Or.inr hq
  · exact hq

theorem withWitness_has (B : BoundedExtension T) (a : Formula) (h : B.theory.Derives (.ex a)) :
    ∃ i, (B.withWitness a).theory (subst i a) := by
  classical
  simp only [withWitness,dite_eq_left h]
  exact ⟨_,Or.inl rfl⟩

noncomputable def step (B : BoundedExtension T) (p : Formula) : BoundedExtension T :=
  let next := B.deciding p
  match p with
  | .ex a => next.withWitness a
  | _ => next

theorem step_extends_deciding (B : BoundedExtension T) (p q : Formula)
    (h : (B.deciding p).theory q) : (B.step p).theory q := by
  cases p <;> first | exact h | exact withWitness_extends _ _ _ h

theorem step_extends (B : BoundedExtension T) (p q : Formula)
    (h : B.theory q) : (B.step p).theory q :=
  B.step_extends_deciding p q (B.deciding_extends p q h)

end BoundedExtension

variable (T : Theory) (consistent : T.Consistent) (closed : ∀ p, T p → Closed p)

noncomputable def henkinStage : Nat → BoundedExtension T
  | 0 => ⟨T, fun _ => id, consistent, 0, closed⟩
  | n+1 => (henkinStage n).step (formulaListing.get n)

noncomputable def henkinUnion : Theory := fun p => ∃ n, (henkinStage T consistent closed n).theory p

include consistent closed

theorem henkinStage_mono {i j : Nat} (hi : i ≤ j) :
    ∀ p, (henkinStage T consistent closed i).theory p → (henkinStage T consistent closed j).theory p := by
  induction hi with
  | refl => exact fun _ h => h
  | @step j _ ih => exact fun p h =>
      (henkinStage T consistent closed j).step_extends _ _ (ih p h)

theorem henkinUnion_consistent : (henkinUnion T consistent closed).Consistent := by
  rintro ⟨Γ,axioms,refutes⟩
  have finite {Δ : Context} (hΔ : ∀ p ∈ Δ, henkinUnion T consistent closed p) :
      ∃ i, ∀ p ∈ Δ, (henkinStage T consistent closed i).theory p := by
    induction Δ with
    | nil => exact ⟨0,by simp⟩
    | cons q Δ ih =>
      obtain ⟨i,hi⟩ := hΔ q (by simp)
      obtain ⟨j,hj⟩ := ih (fun p hp => hΔ p (List.mem_cons_of_mem _ hp))
      refine ⟨max i j,fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with rfl | left
      · exact henkinStage_mono T consistent closed (Nat.le_max_left ..) _ hi
      · exact henkinStage_mono T consistent closed (Nat.le_max_right ..) _ (hj p left)
  obtain ⟨i,inStage⟩ := finite axioms
  exact (henkinStage T consistent closed i).consistent ⟨Γ,inStage,refutes⟩

theorem henkinUnion_decides (p : Formula) :
    henkinUnion T consistent closed p ∨ henkinUnion T consistent closed (Neg p) := by
  obtain ⟨i,eq⟩ := formulaListing.contains p
  let B := henkinStage T consistent closed i
  rcases B.deciding_decides p with hp | hn
  · exact Or.inl ⟨i+1,eq.symm ▸ B.step_extends_deciding p p hp⟩
  · exact Or.inr ⟨i+1,eq.symm ▸ B.step_extends_deciding p (Neg p) hn⟩

theorem henkinUnion_closedUnderProof {p : Formula}
    (h : (henkinUnion T consistent closed).Derives p) : henkinUnion T consistent closed p := by
  rcases henkinUnion_decides T consistent closed p with inUnion | denied
  · exact inUnion
  · exact (henkinUnion_consistent T consistent closed ((Derives.of_axiom denied).app h)).elim

theorem henkinUnion_witness (a : Formula)
    (h : henkinUnion T consistent closed (.ex a)) :
    ∃ i, henkinUnion T consistent closed (subst i a) := by
  obtain ⟨i,eq⟩ := formulaListing.contains (.ex a)
  let B := henkinStage T consistent closed i
  let next := B.deciding (.ex a)
  have hDecided : next.theory (.ex a) := by
    rcases B.deciding_decides (.ex a) with positive | denied
    · exact positive
    · have bad : henkinUnion T consistent closed (Neg (.ex a)) :=
        ⟨i+1,eq.symm ▸ B.step_extends_deciding (.ex a) (Neg (.ex a)) denied⟩
      exact (henkinUnion_consistent T consistent closed
        ((Derives.of_axiom bad).app (.of_axiom h))).elim
  obtain ⟨k,witness⟩ := next.withWitness_has a (.of_axiom hDecided)
  refine ⟨k,i+1,?_⟩
  change (B.step (formulaListing.get i)).theory (subst k a)
  rw [eq]
  exact witness

end Theory
end PalomarI3380.Logic
