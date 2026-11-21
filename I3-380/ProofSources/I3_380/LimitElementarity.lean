module
public import I3_380.LimitAssignments
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic SetContext

variable {A V : Type} {M : Algebra A} {N : NamedModel M V}

namespace Definable

theorem satisfiesAt {n a c r s i e : Nat}
    (ha : a < n) (hc : c < n) (hr : r < n) (hs : s < n) (hi : i < n) (he : e < n) :
    N.square.Definable n (fun v => Internal.SatisfiesAt N.mem (v a) (v c) (v r) (v s) (v i) (v e)) := by
  have scope : SetFormula.Scoped 6 (SetFormula.satisfiesAt 5 4 3 2 1 0) :=
    (checkBound_sound _ _).mp (by decide +kernel)
  have clause : N.square.Definable 6 (fun v => Internal.SatisfiesAt N.mem (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
    of_levels (S := N.square) (body := SetFormula.satisfiesAt 5 4 3 2 1 0) scope
      (p := fun v => Internal.SatisfiesAt N.mem (v 5) (v 4) (v 3) (v 2) (v 1) (v 0))
      (fun _ _ => SetFormula.holds_satisfiesAt (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide))
  let map (k : Nat) := match k with
    | 0 => a
    | 1 => c
    | 2 => r
    | 3 => s
    | 4 => i
    | _ => e
  have bound : ∀ k, k < 6 → map k < n := by
    intro k _
    unfold map
    split <;> assumption
  exact clause.reindex map bound

end Definable

namespace NamedModel

theorem satisfiesAt_rule (N : NamedModel M V) {w a c r stage j env t x y : V}
    (omega : Internal.Omega N.mem w) (code : Internal.SyntaxCode N.mem w a c r)
    (index : N.mem j c) (typed : Internal.FunctionInto N.mem env a stage)
    (entry : Internal.RowAt N.mem r j t x y) (valid : Internal.ValidRow N.mem a j t x y) :
    Internal.SatisfiesAt N.mem a c r stage j env ↔
      Internal.RowTruth N.mem (Internal.SatisfiesAt N.mem a c r stage) a stage env t x y := by
  obtain ⟨_, sat, _, _, table⟩ := N.truthSet_exists omega code stage
  have cOrd := (N.omega_ordinal omega).of_mem N.toSetContext code.2.1
  exact (N.satisfiesAt_iff_table omega code table index typed).trans
    ((N.truthSet_rule code table index typed entry).trans
      (N.rowTruth_congr valid typed fun i below values ok =>
        (N.satisfiesAt_iff_table omega code table (cOrd.transitive j index i below) ok).symm))

/-- The internally indexed union of the elementary stages is elementary
over each stage, for every internal code and every typed assignment. -/
theorem CriticalRun.elementary_limit {w heights stages limit : V}
    (run : N.CriticalRun w heights stages) (omega : Internal.Omega N.mem w)
    (covers : ∀ x, N.mem x limit ↔ ∃ n stage, Internal.At N.mem stages n stage ∧ N.mem x stage) :
    ∀ n s, Internal.At N.mem stages n s → Internal.ElementaryIncluded N.mem w s limit := by
  have sub {n stage : V} (he : Internal.At N.mem stages n stage) : N.Subset stage limit :=
    fun x hx => (covers x).mpr ⟨n,stage,he,hx⟩
  intro n s onStage
  refine ⟨sub onStage, fun a c rows code => ?_⟩
  let T (u i env : V) := Internal.SatisfiesAt N.mem a c rows u i env
  have rowOrd := (N.omega_ordinal omega).of_mem N.toSetContext code.2.1
  have graph := Definable.graphValue (N := N.toSetContext) (n := 10) (i := 8) (j := 2) (k := 1)
    (by decide) (by decide) (by decide)
  have typed := Definable.functionInto (N := N.toSetContext) (n := 10) (i := 0) (j := 5) (k := 1)
    (by decide) (by decide) (by decide)
  have holds := Definable.satisfiesAt (N := N) (n := 10) (a := 5) (c := 6) (r := 7) (s := 1) (i := 3) (e := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have holdsAt := Definable.satisfiesAt (N := N) (n := 10) (a := 5) (c := 6) (r := 7) (s := 9) (i := 3) (e := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have defn := Definable.all (Definable.all (Definable.all (graph.implies (typed.implies (holds.iff holdsAt)))))
  have agreement : ∀ i, N.mem i c → ∀ n s env,
      Internal.At N.mem stages n s → Internal.FunctionInto N.mem env a s → (T s i env ↔ T limit i env) := by
    apply N.order_induction rowOrd.ordered [a,c,rows,stages,limit] defn
    intro i index ih n s env hs ready
    obtain ⟨tag,x,y,entry,_,_,valid⟩ := code.2.2.2.2 i index
    have largeType := N.functionInto_mono ready (sub hs)
    have source := N.satisfiesAt_rule omega code index ready entry valid
    have target := N.satisfiesAt_rule omega code index largeType entry valid
    refine source.trans (?_ : Internal.RowTruth N.mem (T s) a s env tag x y ↔
      Internal.RowTruth N.mem (T limit) a limit env tag x y) |>.trans target.symm
    have earlier (child : V) (h : N.mem child i) (j u e : V) (atU : Internal.At N.mem stages j u)
        (context : Internal.FunctionInto N.mem e a u) : T u child e ↔ T limit child e :=
      ih child (rowOrd.transitive i index child h) h j u e atU context
    unfold Internal.RowTruth
    refine or_congr Iff.rfl (or_congr Iff.rfl (or_congr ?_ (or_congr ?_ ?_)))
    · exact and_congr_right fun neg =>
        not_congr (earlier x (N.first_before valid (Or.inl neg)) n s env hs ready)
    · exact and_congr_right fun conj =>
        and_congr (earlier x (N.first_before valid (Or.inr conj)) n s env hs ready)
          (earlier y (N.second_before valid (Or.inl conj)) n s env hs ready)
    · apply and_congr_right
      intro exTag
      have next := N.second_before valid (Or.inr exTag)
      constructor
      · rintro ⟨value, valueType, agrees, truth⟩
        exact ⟨value, N.functionInto_mono valueType (sub hs), agrees,
          (earlier y next n s value hs valueType).mp truth⟩
      · rintro ⟨value, valueType, agrees, truth⟩
        have bounded := run.bound_assignment omega (fun x hx => (covers x).mp hx) a code.1 value valueType
        obtain ⟨j, stage, fromChain, atStage⟩ := bounded
        obtain ⟨k, upper, top, elemS, elemStage⟩ := run.common_stage omega hs fromChain
        have typedValue := N.functionInto_mono atStage elemStage.1
        have child := (earlier y next k upper value top typedValue).mpr truth
        have typedEnv := N.functionInto_mono ready elemS.1
        have newRule := N.satisfiesAt_rule omega code index typedEnv entry valid
        have satUpper : T upper i env := newRule.mpr
          (Or.inr (Or.inr (Or.inr (Or.inr ⟨exTag, value, typedValue, agrees, child⟩))))
        have satSmall := (elemS.2 _ _ _ code i index env ready).mpr satUpper
        have known := source.mp satSmall
        rcases known with ⟨t₀, _⟩ | ⟨t₁, _⟩ | ⟨t₂, _⟩ | ⟨t₃, _⟩ | ⟨_, checked⟩
        · have impossible := N.numeral_not_clash t₀ exTag
          omega
        · have impossible := N.numeral_not_clash t₁ exTag
          omega
        · have impossible := N.numeral_not_clash t₂ exTag
          omega
        · have impossible := N.numeral_not_clash t₃ exTag
          omega
        · exact checked
  exact fun i hi env envTyped => agreement i hi n s env onStage envTyped

end NamedModel
end PalomarI3380.SquareRepresentation
