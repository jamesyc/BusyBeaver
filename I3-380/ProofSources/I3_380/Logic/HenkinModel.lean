module
public import I3_380.Logic.HenkinExtensions
@[expose] public section

namespace PalomarI3380.Logic

theorem instantiateRenamed (p : Formula) (σ : Nat → Nat) (k : Nat) :
    subst k (rename (lift σ) p) = rename (pushValue σ k) p := by
  rw [subst,rename_comp]
  congr 1
  funext i
  cases i <;> rfl

namespace Theory

variable {T : Theory} {p : Formula}

theorem Derives.counterexample (denied : T.Derives (Neg (.all p))) : T.Derives (.ex (Neg p)) := by
  apply Derives.neg_elim
  apply discharge
  have allP : (T.add (Neg (.ex (Neg p)))).Derives (.all p) := by
    refine ⟨[Neg (.ex (Neg p))],fun _ h => Or.inl (List.mem_singleton.mp h),ND.allI ?_⟩
    change ND (.seq [shift (Neg (.ex (Neg p)))] p)
    let Γ := [shift (Neg (.ex (Neg p)))]
    let U : Theory := fun a => a ∈ Γ
    have nn : U.Derives (Neg (Neg p)) := by
      apply discharge
      refine ⟨Neg p :: Γ,fun a h => ?_,?_⟩
      · rcases List.mem_cons.mp h with hit | rest
        · exact Or.inl hit
        · exact Or.inr rest
      · have premise : ND (.seq [Neg p,shift (Neg (.ex (Neg p)))]
            (.ex (rename (lift Nat.succ) (Neg p)))) := by
          apply ND.exI 0
          rw [instantiateRenamed]
          have same : pushValue Nat.succ (0 : Nat) = id := by
            funext i
            cases i <;> rfl
          rw [same,rename_identity]
          exact ND.ctx List.mem_cons_self
        have negative : ND (.seq [Neg p,shift (Neg (.ex (Neg p)))]
            (Neg (.ex (rename (lift Nat.succ) (Neg p))))) :=
          ND.ctx (List.mem_cons_of_mem _ List.mem_cons_self)
        exact ND.ie negative premise
    obtain ⟨Δ,support,h⟩ := nn.neg_elim
    exact ND.wk support h
  exact (denied.mono (fun _ => Or.inr)).app allP

/-- Equality and membership instances are derived from the four closed
logical axioms of the source calculus. -/
theorem Derives.equality_refl (h : T.Derives fixedRefl) (a : Nat) : T.Derives (.eq a a) := by
  simpa [fixedRefl,subst,substMap,rename] using h.allE a

theorem Derives.equality_symm (h : T.Derives fixedSym) {a b : Nat}
    (eq : T.Derives (.eq a b)) : T.Derives (.eq b a) := by
  have ax : T.Derives (.imp (.eq a b) (.eq b a)) := by
    simpa [fixedSym,subst,substMap,rename,lift] using (h.allE a).allE b
  exact ax.app eq

theorem Derives.equality_trans (h : T.Derives fixedTrans) {a b c : Nat}
    (ab : T.Derives (.eq a b)) (bc : T.Derives (.eq b c)) : T.Derives (.eq a c) := by
  have ax : T.Derives (.imp (.eq a b) (.imp (.eq b c) (.eq a c))) := by
    simpa [fixedTrans,subst,substMap,rename,lift] using ((h.allE a).allE b).allE c
  exact (ax.app ab).app bc

theorem Derives.membership_congr (h : T.Derives fixedEqElem) {a b c d : Nat}
    (ac : T.Derives (.eq a c)) (bd : T.Derives (.eq b d))
    (ab : T.Derives (.mem a b)) : T.Derives (.mem c d) := by
  have ax : T.Derives (.imp (.eq a c) (.imp (.eq b d) (.imp (.mem a b) (.mem c d)))) := by
    simpa [fixedEqElem,subst,substMap,rename,lift] using (((h.allE a).allE b).allE c).allE d
  exact ((ax.app ac).app bd).app ab

variable (T) (consistent : T.Consistent) (closed : ∀ p, T p → Closed p)

local notation "H" => (henkinUnion T consistent closed)

theorem henkinUnion_extends (p : Formula) (h : T p) : (H) p := ⟨0,h⟩

structure EqualityAxioms (T : Theory) : Prop where
  refl : T fixedRefl
  symm : T fixedSym
  trans : T fixedTrans
  membership : T fixedEqElem

noncomputable def henkinEquality (eqs : EqualityAxioms T) : Setoid Nat where
  r i j := (H) (.eq i j)
  iseqv := {
    refl := fun a => henkinUnion_closedUnderProof T consistent closed
      ((Derives.of_axiom (henkinUnion_extends T consistent closed _ eqs.refl)).equality_refl a)
    symm := fun h => henkinUnion_closedUnderProof T consistent closed
      ((Derives.of_axiom (henkinUnion_extends T consistent closed _ eqs.symm)).equality_symm (.of_axiom h))
    trans := fun h k => henkinUnion_closedUnderProof T consistent closed
      ((Derives.of_axiom (henkinUnion_extends T consistent closed _ eqs.trans)).equality_trans
        (.of_axiom h) (.of_axiom k))
  }

variable (eqs : EqualityAxioms T)

abbrev HenkinPoint := Quotient (henkinEquality T consistent closed eqs)

noncomputable def henkinMem : HenkinPoint T consistent closed eqs →
    HenkinPoint T consistent closed eqs → Prop :=
  Quotient.lift₂ (fun a b => (H) (.mem a b)) (by
    intro a b c d ac bd
    let eqv := (henkinEquality T consistent closed eqs).iseqv
    apply propext
    have ax := Derives.of_axiom (henkinUnion_extends T consistent closed _ eqs.membership)
    exact ⟨fun mem => henkinUnion_closedUnderProof T consistent closed
      (ax.membership_congr (.of_axiom ac) (.of_axiom bd) (.of_axiom mem)),
      fun mem => henkinUnion_closedUnderProof T consistent closed
        (ax.membership_congr (.of_axiom (eqv.symm ac)) (.of_axiom (eqv.symm bd)) (.of_axiom mem))⟩)

local notation "Q" => (Quotient.mk (henkinEquality T consistent closed eqs))

noncomputable def henkinListing : Expanded.Listing (HenkinPoint T consistent closed eqs) :=
  ⟨(Q),fun q => Quotient.inductionOn q (fun n => ⟨n,rfl⟩)⟩

theorem henkin_truth (p : Formula) (σ : Nat → Nat) :
    eval (henkinMem T consistent closed eqs) p (fun i => (Q) (σ i)) ↔ (H) (rename σ p) := by
  have finish {a : Formula} (hp : (H).Derives a) : (H) a :=
    henkinUnion_closedUnderProof T consistent closed hp
  have decides := henkinUnion_decides T consistent closed
  have consistentH := henkinUnion_consistent T consistent closed
  have push_commute (env : Nat → Nat) (i : Nat) :
      pushValue (fun j => (Q) (env j)) ((Q) i) = (fun j => (Q) (pushValue env i j)) := by
    funext j
    cases j <;> rfl
  induction p generalizing σ with
  | bot => exact ⟨False.elim,fun hp => consistentH (.of_axiom hp)⟩
  | eq a b =>
    change (Q) (σ a) = (Q) (σ b) ↔ (henkinEquality T consistent closed eqs).r (σ a) (σ b)
    exact ⟨Quotient.exact,Quotient.sound⟩
  | mem a b => rfl
  | and p q ip iq =>
    exact (and_congr (ip σ) (iq σ)).trans ⟨fun ⟨hp,hq⟩ =>
      finish ((Derives.of_axiom hp).conj (.of_axiom hq)),fun h =>
      ⟨finish ((Derives.of_axiom h).map fun _ => ND.ce1),
        finish ((Derives.of_axiom h).map fun _ => ND.ce2)⟩⟩
  | or p q ip iq =>
    refine (or_congr (ip σ) (iq σ)).trans ⟨?_,?_⟩
    · exact fun h => h.elim (fun hp => finish ((Derives.of_axiom hp).map fun _ => ND.di1))
        (fun hq => finish ((Derives.of_axiom hq).map fun _ => ND.di2))
    · intro h
      rcases decides (rename σ p) with hp | hp
      · exact Or.inl hp
      rcases decides (rename σ q) with hq | hq
      · exact Or.inr hq
      exact (consistentH ((Derives.of_axiom h).close_pair
        ((Derives.of_axiom hp).conj (.of_axiom hq)) (fun Γ disj both =>
          ND.de disj (ND.branchPair
            (ND.ie (ND.wk (fun _ h => List.mem_cons_of_mem _ h) (ND.ce1 both)) (ND.ctx List.mem_cons_self))
            (ND.ie (ND.wk (fun _ h => List.mem_cons_of_mem _ h) (ND.ce2 both)) (ND.ctx List.mem_cons_self)))))).elim
  | imp p q ip iq =>
    refine (imp_congr (ip σ) (iq σ)).trans ⟨?_,fun h hp => finish ((Derives.of_axiom h).app (.of_axiom hp))⟩
    intro satisfied
    rcases decides (rename σ p) with hp | hp
    · exact finish ((Derives.of_axiom (satisfied hp)).map fun _ proof =>
        ND.ii (ND.wk (fun _ h => List.mem_cons_of_mem _ h) proof))
    · exact finish ((Derives.of_axiom hp).map fun _ proof =>
        ND.ii (ND.exp (ND.ie (ND.wk (fun _ h => List.mem_cons_of_mem _ h) proof) (ND.ctx List.mem_cons_self))))
  | all p ih =>
    constructor
    · intro forallEval
      rcases decides (.all (rename (lift σ) p)) with h | h
      · exact h
      have negExists := finish ((Derives.of_axiom h).counterexample)
      obtain ⟨i,bad⟩ := henkinUnion_witness T consistent closed _ negExists
      change (H) (subst i (rename (lift σ) (Neg p))) at bad
      rw [instantiateRenamed] at bad
      have inst := (ih (pushValue σ i)).mp (by simpa only [push_commute] using forallEval ((Q) i))
      change (H) (Neg (rename (pushValue σ i) p)) at bad
      exact (consistentH ((Derives.of_axiom bad).app (.of_axiom inst))).elim
    · intro h x
      induction x using Quotient.inductionOn with
      | _ i =>
        rw [push_commute]
        apply (ih (pushValue σ i)).mpr
        rw [← instantiateRenamed]
        exact finish ((Derives.of_axiom h).allE i)
  | ex p ih =>
    constructor
    · rintro ⟨x,hx⟩
      induction x using Quotient.inductionOn with
      | _ i =>
        rw [push_commute] at hx
        have instance_ := (ih (pushValue σ i)).mp hx
        rw [← instantiateRenamed] at instance_
        exact finish ((Derives.of_axiom instance_).exI i)
    · intro h
      obtain ⟨i,hit⟩ := henkinUnion_witness T consistent closed _ h
      rw [instantiateRenamed] at hit
      exact ⟨(Q) i,by rw [push_commute]; exact (ih (pushValue σ i)).mpr hit⟩

include consistent closed eqs in
theorem countable_model_of_consistency :
    ∃ (V : Type) (E : V → V → Prop), Nonempty (Expanded.Listing V) ∧
      ∀ p, T p → ∀ env : Nat → V, eval E p env := by
  classical
  refine ⟨HenkinPoint T consistent closed eqs,henkinMem T consistent closed eqs,
    ⟨henkinListing T consistent closed eqs⟩,fun p hp env => ?_⟩
  let σ := fun i => Classical.choose ((henkinListing T consistent closed eqs).contains (env i))
  have same : (fun i => (Q) (σ i)) = env := funext fun i =>
    Classical.choose_spec ((henkinListing T consistent closed eqs).contains (env i))
  rw [← same,henkin_truth,rename_closed p (closed p hp)]
  exact henkinUnion_extends T consistent closed p hp

end Theory
end PalomarI3380.Logic
