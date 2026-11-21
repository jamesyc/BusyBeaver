module
public import I3_380.EmbeddingGraphs
@[expose] public section

namespace PalomarI3380.Logic.Internal

variable {V : Type} (E : V → V → Prop)

/-- The truth of one row, with a well-typed finite assignment, in the
membership structure of the given set. -/
def SatisfiesAt (arity count rows stage i env : V) : Prop :=
  ∃ sat, TruthSet E arity count rows stage sat ∧ At E sat i env

def ElementaryIncluded (w small large : V) : Prop :=
  (∀ x, E x small → E x large) ∧ ∀ arity count rows, SyntaxCode E w arity count rows →
    ∀ i, E i count → ∀ env, FunctionInto E env arity small →
      (SatisfiesAt E arity count rows small i env ↔ SatisfiesAt E arity count rows large i env)

end PalomarI3380.Logic.Internal

namespace PalomarI3380.Logic.SetFormula

def satisfiesAt (arity count rows stage i env : Nat) : SetFormula :=
  someSet fun sat => both (truthSet arity count rows stage sat) (graphValue sat i env)

def elementaryIncluded (w small large : Nat) : SetFormula :=
  both (subset small large) (every fun arity => every fun count => every fun rows =>
    implies (syntaxCode w arity count rows) (eachIn count fun i => every fun env =>
      implies (functionInto env arity small)
        (iff (satisfiesAt arity count rows small i env) (satisfiesAt arity count rows large i env))))

variable {V : Type} {E : V → V → Prop} {d : Nat} {env : Nat → V} {default : V}

theorem holds_satisfiesAt {a c r s i e : Nat}
    (ha : a < d) (hc : c < d) (hr : r < d) (hs : s < d) (hi : i < d) (he : e < d) :
    holds E (satisfiesAt a c r s i e) d env default ↔
      Internal.SatisfiesAt E (env a) (env c) (env r) (env s) (env i) (env e) := by
  simp (disch := omega) only [satisfiesAt, holds_someSet, holds_both, holds_graphValue, holds_truthSet,
    assign_here, assign_earlier, Internal.SatisfiesAt]

theorem holds_elementaryIncluded {w a b : Nat} (hw : w < d) (ha : a < d) (hb : b < d) :
    holds E (elementaryIncluded w a b) d env default ↔ Internal.ElementaryIncluded E (env w) (env a) (env b) := by
  simp (disch := omega) only [elementaryIncluded, holds_both, holds_subset, holds_every, holds_implies,
    holds_syntaxCode, holds_eachIn, holds_functionInto, holds_iff, holds_satisfiesAt,
    assign_here, assign_earlier, Internal.ElementaryIncluded]

end PalomarI3380.Logic.SetFormula

namespace PalomarI3380.SquareRepresentation.NamedModel

open Logic SetContext

variable {A V : Type} {M : Algebra A} (N : NamedModel M V)

theorem truth_value_unique {w a c r stage left right : V} (omega : Internal.Omega N.mem w)
    (code : Internal.SyntaxCode N.mem w a c r)
    (first : Internal.TruthSet N.mem a c r stage left) (second : Internal.TruthSet N.mem a c r stage right) :
    ∀ i, N.mem i c → ∀ env, Internal.FunctionInto N.mem env a stage →
      (Internal.At N.mem left i env ↔ Internal.At N.mem right i env) := by
  have ord := (N.omega_ordinal omega).of_mem N.toSetContext code.2.1
  have typed := Definable.functionInto (N := N.toSetContext) (n := 7) (i := 0) (j := 3) (k := 4)
    (by decide) (by decide) (by decide)
  have yes := Definable.graphValue (N := N.toSetContext) (n := 7) (i := 5) (j := 1) (k := 0)
    (by decide) (by decide) (by decide)
  have iffYes := Definable.graphValue (N := N.toSetContext) (n := 7) (i := 6) (j := 1) (k := 0)
    (by decide) (by decide) (by decide)
  have defn := Definable.all (typed.implies (yes.iff iffYes))
  apply N.order_induction ord.ordered [a,stage,left,right] defn
  intro i hi ih env typed
  obtain ⟨tag, x, y, has, _, _, valid⟩ := code.2.2.2.2 i hi
  exact (N.truthSet_rule code first hi typed has).trans
    ((N.rowTruth_congr valid typed fun u hu e proof =>
      ih u (ord.transitive i hi u hu) hu e proof).trans
        (N.truthSet_rule code second hi typed has).symm)

theorem satisfiesAt_iff_table {w a c r stage sat i env : V} (omega : Internal.Omega N.mem w)
    (code : Internal.SyntaxCode N.mem w a c r) (table : Internal.TruthSet N.mem a c r stage sat)
    (hi : N.mem i c) (typed : Internal.FunctionInto N.mem env a stage) :
    Internal.SatisfiesAt N.mem a c r stage i env ↔ Internal.At N.mem sat i env :=
  ⟨fun ⟨_t, tv, atT⟩ => (N.truth_value_unique omega code tv table i hi env typed).mp atT,
    fun evidence => ⟨sat,table,evidence⟩⟩

theorem absolute_satisfiesAt {w : V} (omega : Internal.Omega N.mem w) (hW : N.square.activePoint w)
    (a c r s i env : N.Active) (code : Internal.SyntaxCode N.mem w a.val c.val r.val)
    (hi : N.mem i.val c.val) (typed : Internal.FunctionInto N.mem env.val a.val s.val) :
    Internal.SatisfiesAt N.localMem a c r s i env ↔
      Internal.SatisfiesAt N.mem a.val c.val r.val s.val i.val env.val := by
  constructor
  · rintro ⟨table, rules, value⟩
    exact ⟨table.val, (N.absolute_truthSet _ _ _ _ _).mp rules, (N.absolute_at _ _ _).mp value⟩
  · intro h
    obtain ⟨sat, act, rules⟩ := N.active_truthSet_exists omega hW s.property code
    let table : N.Active := ⟨sat,act⟩
    have holdsAt := (N.satisfiesAt_iff_table omega code rules hi typed).mp h
    exact ⟨table, (N.absolute_truthSet _ _ _ _ _).mpr rules, (N.absolute_at table i env).mpr holdsAt⟩

theorem preserves_satisfiesAt {w : V} (omega : Internal.Omega N.mem w) (hW : N.square.activePoint w)
    (a c r s i env : N.Active) (code : Internal.SyntaxCode N.mem w a.val c.val r.val)
    (hi : N.mem i.val c.val) (typed : Internal.FunctionInto N.mem env.val a.val s.val) :
    Internal.SatisfiesAt N.mem a.val c.val r.val s.val i.val env.val ↔
      Internal.SatisfiesAt N.mem a.val c.val r.val (N.embedding s).val i.val (N.embedding env).val := by
  have aFixed := N.fixes_natural omega hW a code.1
  have cFixed := N.fixes_natural omega hW c code.2.1
  have rFixed := N.fixes_syntax_rows omega hW a c r code
  have iFixed := N.fixes_natural omega hW i ((N.omega_ordinal omega).transitive c.val code.2.1 i.val hi)
  have typedImage := (N.preserves_functionInto env a s).mp typed
  rw [aFixed] at typedImage
  let assignment : Nat → N.Active := fun k => match k with
    | 0 => a
    | 1 => c
    | 2 => r
    | 3 => s
    | 4 => i
    | _ => env
  let formula := SetFormula.satisfiesAt 0 1 2 3 4 5
  have scope : SetFormula.Scoped 6 (SetFormula.satisfiesAt 0 1 2 3 4 5) :=
    (checkBound_sound _ _).mp (by decide +kernel)
  have readOriginal : SetFormula.holds N.localMem formula 6 assignment a ↔
      Internal.SatisfiesAt N.localMem a c r s i env :=
    SetFormula.holds_satisfiesAt (a := 0) (c := 1) (r := 2) (s := 3) (i := 4) (e := 5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have readMapped : SetFormula.holds N.localMem formula 6 (N.embedding ∘ assignment) (N.embedding a) ↔
      Internal.SatisfiesAt N.localMem (N.embedding a) (N.embedding c) (N.embedding r)
        (N.embedding s) (N.embedding i) (N.embedding env) :=
    SetFormula.holds_satisfiesAt (env := N.embedding ∘ assignment) (default := N.embedding a)
      (a := 0) (c := 1) (r := 2) (s := 3) (i := 4) (e := 5) (d := 6)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have codeFixed :
      Internal.SatisfiesAt N.localMem (N.embedding a) (N.embedding c) (N.embedding r)
        (N.embedding s) (N.embedding i) (N.embedding env) ↔
      Internal.SatisfiesAt N.localMem a c r (N.embedding s) i (N.embedding env) := by
    rw [aFixed, cFixed, rFixed, iFixed]
  have whole := readOriginal.symm.trans ((N.preserves_builder formula 6 scope assignment a).trans
    (readMapped.trans codeFixed))
  exact (N.absolute_satisfiesAt omega hW a c r s i env code hi typed).symm.trans
    (whole.trans (N.absolute_satisfiesAt omega hW a c r (N.embedding s) i (N.embedding env) code hi typedImage))

end PalomarI3380.SquareRepresentation.NamedModel
