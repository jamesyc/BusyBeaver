module
public import I3_334Support.SetTheory.Classes.DefinableTruth
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic SetContext

variable {A V : Type} {M : Algebra A} (N : SetContext M V)

structure TruthInput (V : Type) where
  space : V
  rows : V
  arity : V
  stage : V

noncomputable def truthKey (data : TruthInput V) : V :=
  N.orderedPair data.space (N.orderedPair data.rows (N.orderedPair data.arity data.stage))

def ReadsTruthKey (key : V) (data : TruthInput V) : Prop :=
  ∃ rest last, Internal.OrderedPair N.mem data.space rest key ∧
    Internal.OrderedPair N.mem data.rows last rest ∧ Internal.OrderedPair N.mem data.arity data.stage last

theorem reads_truthKey (data : TruthInput V) : N.ReadsTruthKey (N.truthKey data) data :=
  ⟨_, _, N.orderedPair_intro _ _, N.orderedPair_intro _ _, N.orderedPair_intro _ _⟩

theorem truthKey_unique {key : V} {a b : TruthInput V} (ha : N.ReadsTruthKey key a) (hb : N.ReadsTruthKey key b) :
    a = b := by
  obtain ⟨x, y, outer, mid, inner⟩ := ha
  obtain ⟨x', y', outer', mid', inner'⟩ := hb
  obtain ⟨space, eq⟩ := Internal.orderedPair_injective outer outer'
  subst x'
  obtain ⟨rows, eq⟩ := Internal.orderedPair_injective mid mid'
  subst y'
  obtain ⟨arity, stage⟩ := Internal.orderedPair_injective inner inner'
  cases a
  cases b
  simp_all

def FamilyTruth (family row env : V) : Prop :=
  ∃ trueAssignments, Internal.At N.mem family row trueAssignments ∧ N.mem env trueAssignments

theorem familyTruth_definable : Definable.Relation3 N (N.FamilyTruth) := by
  intro n i j k hi hj hk
  exact Definable.ex (
    (Definable.graphValue (N := N) (n := n + 1) (i := i + 1) (j := j + 1) (k := 0)
      (by omega) (by omega) (by omega)).and
    (Definable.mem (N := N) (n := n + 1) (i := k + 1) (j := 0) (by omega) (by omega)))

def TruthLayer (rows arity stage i family env : V) : Prop :=
  ∃ tag a b, Internal.RowAt N.mem rows i tag a b ∧
    Internal.RowTruth N.mem (N.FamilyTruth family) arity stage env tag a b

theorem truthLayer_def {n r a s i f e : Nat}
    (hr : r < n) (ha : a < n) (hs : s < n) (hi : i < n) (hf : f < n) (he : e < n) :
    N.square.Definable n (fun v => N.TruthLayer (v r) (v a) (v s) (v i) (v f) (v e)) := by
  have row := Definable.rowAt (N := N) (n := n + 3) (r := r + 3) (i := i + 3) (t := 2) (a := 1) (b := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have truth := Definable.rowTruth (N := N) (T := N.FamilyTruth) N.familyTruth_definable
    (n := n + 3) (p := f + 3) (a := a + 3) (s := s + 3) (e := e + 3) (t := 2) (x := 1) (y := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  exact Definable.ex (Definable.ex (Definable.ex (row.and truth)))

def TruthUpdate (key i previous value : V) : Prop :=
  ∃ data : TruthInput V, N.ReadsTruthKey key data ∧
    ∀ env, N.mem env value ↔ N.mem env data.space ∧
      N.TruthLayer data.rows data.arity data.stage i previous env

private theorem truthKey_def {n p s r a v : Nat}
    (hp : p < n) (hs : s < n) (hr : r < n) (ha : a < n) (hv : v < n) :
    N.square.Definable n (fun env => N.ReadsTruthKey (env p) ⟨env s, env r, env a, env v⟩) := by
  have first := Definable.orderedPair (N := N) (n := n + 2) (i := s + 2) (j := 1) (k := p + 2)
    (by omega) (by omega) (by omega)
  have middle := Definable.orderedPair (N := N) (n := n + 2) (i := r + 2) (j := 0) (k := 1)
    (by omega) (by omega) (by omega)
  have last := Definable.orderedPair (N := N) (n := n + 2) (i := a + 2) (j := v + 2) (k := 0)
    (by omega) (by omega) (by omega)
  exact Definable.ex (Definable.ex (first.and (middle.and last)))

theorem truthUpdate_formula : Definable.Relation4 N (N.TruthUpdate) := by
  intro n p i f out hp hi hf ho
  have settings := N.truthKey_def (n := n + 4) (p := p + 4) (s := 3) (r := 2) (a := 1) (v := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have output := Definable.mem (N := N) (n := n + 5) (i := 0) (j := out + 5) (by omega) (by omega)
  have typed := Definable.mem (N := N) (n := n + 5) (i := 0) (j := 4) (by omega) (by omega)
  have layer := N.truthLayer_def (n := n + 5) (r := 3) (a := 2) (s := 1) (i := i + 5) (f := f + 5)
    (e := 0) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine (Definable.ex (Definable.ex (Definable.ex (Definable.ex
    (settings.and (Definable.all (output.iff (typed.and layer)))))))).congr fun env => ?_
  constructor
  · rintro ⟨a, r, n, s, code, values⟩
    exact ⟨⟨a,r,n,s⟩, code, values⟩
  · rintro ⟨⟨a,r,n,s⟩, code, values⟩
    exact ⟨a,r,n,s,code,values⟩

theorem truthUpdate_exists (data : TruthInput V) (i previous : V) :
    ∃ value, N.TruthUpdate (N.truthKey data) i previous value := by
  have desc := N.truthLayer_def (n := 7) (r := 2) (a := 3) (s := 4) (i := 5) (f := 6) (e := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨value, membership⟩ :=
    N.separate [data.rows,data.arity,data.stage,i,previous] desc data.space data.space
  exact ⟨value, data, N.reads_truthKey data, membership⟩

theorem truthUpdate_unique (key i previous a b : V)
    (ha : N.TruthUpdate key i previous a) (hb : N.TruthUpdate key i previous b) : a = b := by
  obtain ⟨d, hd, left⟩ := ha
  obtain ⟨e, he, right⟩ := hb
  have same := N.truthKey_unique hd he
  subst e
  exact N.ext a b fun x => (left x).trans (right x).symm

noncomputable def truthRecursor (data : TruthInput V) {count : V} (ho : N.Ordinal count) :
    SetRecursion N :=
  ⟨count, count, N.truthKey data, fun _ => N.mem, Definable.membership_relation,
    ho.ordered, N.TruthUpdate, N.truthUpdate_formula, N.truthUpdate_exists data, N.truthUpdate_unique _⟩

theorem familyTruth_value {data : TruthInput V} {count family i : V} {ho : N.Ordinal count}
    (computation : (N.truthRecursor data ho).Solution count family) (hi : N.mem i count) :
    ∃ previous,
      N.Restricts family i previous ∧
        ∀ env, N.FamilyTruth family i env ↔ N.mem env data.space ∧
          N.TruthLayer data.rows data.arity data.stage i previous env := by
  obtain ⟨cut, past, value, cutSpec, uses, atValue, computes⟩ := computation.agrees i hi
  have cutEq : cut = i := N.ext cut i fun z =>
    (cutSpec z).trans ⟨And.right, fun hz => ⟨ho.transitive i hi z hz, hz⟩⟩
  subst cut
  obtain ⟨params, reads, result⟩ := computes
  have same : params = data := N.truthKey_unique reads (N.reads_truthKey data)
  subst params
  refine ⟨past, uses, fun env => Iff.trans ?_ (result env)⟩
  obtain ⟨_, _, one⟩ := computation.functionOn.1 i hi
  constructor
  · rintro ⟨values, read, member⟩
    have same := (one values read).trans (one value atValue).symm
    exact same ▸ member
  · exact fun h => ⟨value, atValue, h⟩

theorem familyTruth_restrict {f i past a x : V} (h : N.Restricts f i past) (ha : N.mem a i) :
    N.FamilyTruth past a x ↔ N.FamilyTruth f a x := by
  apply exists_congr
  intro value
  exact and_congr ((N.restricts_value h).trans ⟨And.right, fun hv => ⟨ha,hv⟩⟩) Iff.rfl

end PalomarI3380.SquareRepresentation.SetContext
