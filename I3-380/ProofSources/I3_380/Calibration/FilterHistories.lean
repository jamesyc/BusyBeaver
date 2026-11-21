module
public import I3_380.Calibration.FilterDescent
@[expose] public section

namespace PalomarI3380.Calibration.TermWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

noncomputable def unitName : CanonicalTerm M :=
  nameClass ((quotientAlgebra (M := M)).withStages.constant .I)

noncomputable def zeroName : CanonicalTerm M :=
  nameClass ((quotientAlgebra (M := M)).withStages.zero)

structure FilterHistory (seed : CanonicalTerm M) (length trace : M) : Prop where
  size : len trace = length+1
  initial : trace.[0] = seed.val
  canonical : ∀ i ≤ length, Canonical trace.[i]
  step : ∀ i < length,
    descentStepDef.val.Evalb ![i,trace.[i],trace.[i+1],(unitName (M := M)).val,(zeroName (M := M)).val]

noncomputable def filterHistoryDef : 𝚺ᴬ_[2].Semisentence 5 :=
  .mkSigma “trace length seed unit zero. !lenDef (length+1) trace ∧ !nthDef seed trace 0 ∧
    (∀ i < length+1, ∃ b, !nthDef b trace i ∧ !canonicalDef b) ∧
    (∀ i < length, ∃ a b, !nthDef a trace i ∧ !nthDef b trace (i+1) ∧ !(descentStepDef.val) i a b unit zero)”
    (by
      have canonSigma : ℬ[<,ℒₒᵣ].Hierarchy 𝚺 2 canonicalDef.val :=
        canonicalDef.hierarchy_of_lt (by decide)
      have lenSigma : ℬ[<,ℒₒᵣ].Hierarchy 𝚺 2 lenDef.val := lenDef.hierarchy_of_lt (by decide)
      have nthSigma : ℬ[<,ℒₒᵣ].Hierarchy 𝚺 2 nthDef.val := nthDef.hierarchy_of_lt (by decide)
      simp [canonSigma,lenSigma,nthSigma,descentStepDef.hierarchy_sigma])

theorem filterHistory_eval (seed : CanonicalTerm M) (length trace : M) :
    filterHistoryDef.val.Evalb ![trace,length,seed.val,(unitName (M := M)).val,(zeroName (M := M)).val] ↔
      FilterHistory seed length trace := by
  have args (i : M) :
      Semiterm.val ![trace.[i+1],trace.[i],i,trace,length,seed.val,
          (unitName (M := M)).val,(zeroName (M := M)).val] Empty.elim ∘
        (![Semiterm.bvar 2,Semiterm.bvar 1,Semiterm.bvar 0,Semiterm.bvar 6,Semiterm.bvar 7] :
          Fin 5 → ClosedSemiterm ℒₒᵣ 8) =
      ![i,trace.[i],trace.[i+1],(unitName (M := M)).val,(zeroName (M := M)).val] := by
    funext k
    have each : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by
      have lt := k.isLt
      have h : k.val=0 ∨ k.val=1 ∨ k.val=2 ∨ k.val=3 ∨ k.val=4 := by omega
      rcases h with h|h|h|h|h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))
    rcases each with rfl|rfl|rfl|rfl|rfl <;> rfl
  simp [filterHistoryDef,len_defined.iff,nth_defined.iff,canonical_eval,lt_succ_iff_le,args]
  exact ⟨fun ⟨a,b,c,d⟩ => ⟨a.symm,b.symm,c,d⟩,fun h => ⟨h.size.symm,h.initial.symm,h.canonical,h.step⟩⟩

theorem FilterHistory.extension {seed : CanonicalTerm M} {n trace : M}
    (h : FilterHistory seed n trace) :
    FilterHistory seed (n+1) (concat trace (descendName ⟨trace.[n],h.canonical n le_rfl⟩ n).val) := by
  let current : CanonicalTerm M := ⟨trace.[n],h.canonical n le_rfl⟩
  let next := descendName current n
  let extended := concat trace next.val
  have old (i : M) (within : i ≤ n) : extended.[i] = trace.[i] :=
    concat_nth_lt _ _ (h.size.symm ▸ lt_succ_iff_le.mpr within)
  have new : extended.[n+1] = next.val := concat_nth_len' _ _ h.size
  refine ⟨by simp [extended,h.size],(old 0 (Arithmetic.zero_le _)).trans h.initial,?_ ,?_⟩
  · intro i within
    rcases lt_or_eq_of_le within with earlier | rfl
    · have fits := lt_succ_iff_le.mp earlier
      rw [old _ fits]
      exact h.canonical _ fits
    · rw [new]
      exact next.property
  · intro i within
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp within) with earlier | rfl
    · rw [old _ (le_of_lt earlier),old _ (succ_le_iff_lt.mpr earlier)]
      exact h.step i earlier
    · rw [old _ le_rfl,new]
      exact (descentStepDef_eval current i next.val).mpr rfl

theorem filterHistory_definable (seed : CanonicalTerm M) :
    𝚺ᴬ_[2]-Relation (FilterHistory seed) := by
  let P (trace length first unit zero : M) :=
    filterHistoryDef.val.Evalb ![trace,length,first,unit,zero]
  have formula : 𝚺ᴬ_[2].Defined (fun (v : Fin 5 → M) => P (v 0) (v 1) (v 2) (v 3) (v 4)) filterHistoryDef :=
    .mk fun v => by
      have values : ![v 0,v 1,v 2,v 3,v 4] = v := by
        funext i
        refine Fin.cases rfl (fun i => ?_) i
        refine Fin.cases rfl (fun i => ?_) i
        refine Fin.cases rfl (fun i => ?_) i
        refine Fin.cases rfl (fun i => ?_) i
        exact Fin.cases rfl (fun k => k.elim0) i
      change _ ↔ filterHistoryDef.val.Evalb ![v 0,v 1,v 2,v 3,v 4]
      rw [values]
  have definition : 𝚺ᴬ_[2]-Relation₅ P := formula.to_definable
  have specialized : 𝚺ᴬ_[2]-Relation (fun length trace : M =>
        P trace length seed.val (unitName (M := M)).val (zeroName (M := M)).val) :=
    definition.comp (.var 1) (.var 0) (.const _) (.const _) (.const _)
  exact specialized.of_iff (fun v => (filterHistory_eval seed (v 0) (v 1)).symm)

theorem filterHistory_exists (seed : CanonicalTerm M) (n : M) :
    ∃ trace : M, FilterHistory seed n trace := by
  have historyDefined := filterHistory_definable seed
  have existence : 𝚺ᴬ_[2]-Predicate (fun k : M => ∃ trace, FilterHistory seed k trace) := by definability
  refine InductionOnHierarchy.succ_induction_sigma 𝚺 2 existence ?_ (fun k ⟨trace,h⟩ => ⟨_,h.extension⟩) n
  refine ⟨?[seed.val],by simp,by simp,?_ ,?_⟩
  · intro i nonpositive
    have zero' : i=0 := nonpos_iff_eq_zero.mp nonpositive
    simpa only [zero',nth_adjoin_zero] using seed.property
  · intro i earlier
    exact (not_lt_of_ge (Arithmetic.zero_le i) earlier).elim

/-- Two coded histories agree wherever both are defined. The invariance
proof is arithmetic induction on a coordinate, not on an external list. -/
theorem FilterHistory.agree {seed : CanonicalTerm M} {m n a b : M}
    (first : FilterHistory seed m a) (second : FilterHistory seed n b) (i : M) (hi : i ≤ m) (hj : i ≤ n) :
    a.[i] = b.[i] := by
  induction i using ISigma1.sigma1_succ_induction with
  | zero => exact first.initial.trans second.initial.symm
  | succ i previous =>
    have left := succ_le_iff_lt.mp hi
    have right := succ_le_iff_lt.mp hj
    have same := previous (le_of_lt left) (le_of_lt right)
    let current : CanonicalTerm M := ⟨a.[i],first.canonical _ (le_of_lt left)⟩
    have leftStep := (descentStepDef_eval current i a.[i+1]).mp (first.step i left)
    have rightStep := (descentStepDef_eval current i b.[i+1]).mp (by simpa only [current,same,unitName,zeroName] using second.step i right)
    exact leftStep.trans rightStep.symm
  | hP => definability

noncomputable def descentAt (seed : CanonicalTerm M) (n : M) : CanonicalTerm M := by
  let trace := Classical.choose (filterHistory_exists seed n)
  exact ⟨trace.[n],(Classical.choose_spec (filterHistory_exists seed n)).canonical n le_rfl⟩

theorem FilterHistory.result {seed : CanonicalTerm M} {n trace : M} (h : FilterHistory seed n trace) :
    (descentAt seed n).val = trace.[n] :=
  (Classical.choose_spec (filterHistory_exists seed n)).agree h n le_rfl le_rfl

theorem descentAt_zero (seed : CanonicalTerm M) : descentAt seed 0 = seed := by
  apply Subtype.ext
  exact (Classical.choose_spec (filterHistory_exists seed 0)).initial

theorem descentAt_succ (seed : CanonicalTerm M) (n : M) :
    descentAt seed (n+1) = descendName (descentAt seed n) n := by
  obtain ⟨trace,h⟩ := filterHistory_exists seed n
  have eq : descentAt seed n = ⟨trace.[n],h.canonical n le_rfl⟩ := Subtype.ext h.result
  rw [eq]
  apply Subtype.ext
  rw [h.extension.result,concat_nth_len' _ _ h.size]

end PalomarI3380.Calibration.TermWords
