module
public import I3_334Support.SetTheory.Classes.ActiveSyntax
@[expose] public section

namespace PalomarI3380.SquareRepresentation.NamedModel

open Logic SetContext

variable {A V : Type} {M : Algebra A} (N : NamedModel M V)

def threeValues (a b c : N.Active) : Nat → N.Active
  | 0 => a
  | 1 => b
  | _ + 2 => c

theorem preserves_at (f x y : N.Active) :
    Internal.At N.mem f.val x.val y.val ↔
      Internal.At N.mem (N.embedding f).val (N.embedding x).val (N.embedding y).val := by
  let body := SetFormula.graphValue 0 1 2
  let env := N.threeValues f x y
  let mapped := N.embedding ∘ env
  have meaning := (SetFormula.holds_graphValue (E := N.localMem) (d := 3)
    (env := env) (default := f) (f := 0) (x := 1) (y := 2)
    (by decide) (by decide) (by decide)).trans (N.absolute_at f x y)
  have meaning' := (SetFormula.holds_graphValue (E := N.localMem) (d := 3)
    (env := mapped) (default := N.embedding f) (f := 0) (x := 1) (y := 2)
    (by decide) (by decide) (by decide)).trans (N.absolute_at (N.embedding f) (N.embedding x) (N.embedding y))
  exact meaning.symm.trans ((N.preserves_builder body 3
    (SetFormula.scope_graphValue (by decide) (by decide) (by decide)) env f).trans meaning')

theorem preserves_orderedPair (x y p : N.Active) :
    Internal.OrderedPair N.mem x.val y.val p.val ↔
      Internal.OrderedPair N.mem (N.embedding x).val (N.embedding y).val (N.embedding p).val := by
  let body := SetFormula.orderedPair 0 1 2
  let env := N.threeValues x y p
  let mapped := N.embedding ∘ env
  have meaning := (SetFormula.holds_orderedPair (E := N.localMem) (d := 3)
    (env := env) (default := x) (a := 0) (b := 1) (p := 2)
    (by decide) (by decide) (by decide)).trans (N.absolute_orderedPair x y p)
  have meaning' := (SetFormula.holds_orderedPair (E := N.localMem) (d := 3)
    (env := mapped) (default := N.embedding x) (a := 0) (b := 1) (p := 2)
    (by decide) (by decide) (by decide)).trans
    (N.absolute_orderedPair (N.embedding x) (N.embedding y) (N.embedding p))
  exact meaning.symm.trans ((N.preserves_builder body 3
    (SetFormula.scope_orderedPair (by decide) (by decide) (by decide)) env x).trans meaning')

theorem preserves_functionOn (f d : N.Active) :
    Internal.FunctionOn N.mem f.val d.val ↔ Internal.FunctionOn N.mem (N.embedding f).val (N.embedding d).val := by
  let p := SetFormula.functionOn 0 1
  have semantics (x y : N.Active) :
      SetFormula.holds N.localMem p 2 (N.twoValues x y) x ↔ Internal.FunctionOn N.mem x.val y.val :=
    (SetFormula.holds_functionOn (E := N.localMem) (d := 2) (env := N.twoValues x y) (default := x)
      (f := 0) (domain := 1) (by decide) (by decide)).trans (N.absolute_functionOn x y)
  have h := N.preserves_builder p 2 (SetFormula.scope_functionOn (by decide) (by decide)) (N.twoValues f d) f
  rw [N.map_twoValues] at h
  exact (semantics f d).symm.trans (h.trans (semantics _ _))

theorem preserves_functionInto (f d c : N.Active) :
    Internal.FunctionInto N.mem f.val d.val c.val ↔
      Internal.FunctionInto N.mem (N.embedding f).val (N.embedding d).val (N.embedding c).val := by
  let p := SetFormula.functionInto 0 1 2
  let env := N.threeValues f d c
  let mapped := N.embedding ∘ env
  have semantics := (SetFormula.holds_functionInto (E := N.localMem) (d := 3)
    (env := env) (default := f) (f := 0) (a := 1) (b := 2)
    (by decide) (by decide) (by decide)).trans (N.absolute_functionInto f d c)
  have semantics' := (SetFormula.holds_functionInto (E := N.localMem) (d := 3)
    (env := mapped) (default := N.embedding f) (f := 0) (a := 1) (b := 2)
    (by decide) (by decide) (by decide)).trans
    (N.absolute_functionInto (N.embedding f) (N.embedding d) (N.embedding c))
  have scope : SetFormula.Scoped 3 (SetFormula.functionInto 0 1 2) :=
    (checkBound_sound _ _).mp (by decide +kernel)
  exact semantics.symm.trans ((N.preserves_builder p 3 scope env f).trans semantics')

theorem fixes_orderedPair (a b p : N.Active) (code : Internal.OrderedPair N.mem a.val b.val p.val)
    (fa : N.embedding a = a) (fb : N.embedding b = b) : N.embedding p = p := by
  have image := (N.preserves_orderedPair a b p).mp code
  rw [fa, fb] at image
  exact Subtype.ext (Internal.orderedPair_unique N.ext image code)

theorem fixes_function (f domain : N.Active) (h : Internal.FunctionOn N.mem f.val domain.val)
    (fixedDomain : N.embedding domain = domain)
    (fixedValues : ∀ x y : N.Active, Internal.At N.mem f.val x.val y.val →
      N.embedding x = x ∧ N.embedding y = y) : N.embedding f = f := by
  have image := (N.preserves_functionOn f domain).mp h
  rw [fixedDomain] at image
  have forward (x y : V) (fAt : Internal.At N.mem f.val x y) :
      Internal.At N.mem (N.embedding f).val x y := by
    obtain ⟨xIn, yIn⟩ := N.active_graph_coordinates fAt f.property
    let a : N.Active := ⟨x, xIn⟩
    let b : N.Active := ⟨y, yIn⟩
    have new := (N.preserves_at f a b).mp fAt
    rw [(fixedValues a b fAt).1,(fixedValues a b fAt).2] at new
    exact new
  apply Subtype.ext
  apply N.function_ext image h
  intro x y xIn
  refine ⟨fun hy => ?_, forward x y⟩
  obtain ⟨v, hv, _⟩ := h.1 x xIn
  obtain ⟨w, _, same⟩ := image.1 x xIn
  have eq := (same v (forward x v hv)).trans (same y hy).symm
  exact eq ▸ hv

theorem fixes_syntax_rows {w : V} (omega : Internal.Omega N.mem w)
    (activeW : N.square.activePoint w) (arity count rows : N.Active)
    (code : Internal.SyntaxCode N.mem w arity.val count.val rows.val) :
    N.embedding rows = rows := by
  have domain := N.fixes_natural omega activeW count code.2.1
  apply N.fixes_function rows count code.2.2.2.1 domain
  intro i p hi
  have node := SetRecursion.at_domain code.2.2.2.1 hi
  have iIn := (N.omega_ordinal omega).transitive count.val code.2.1 i.val node
  obtain ⟨tag,a,b,⟨row, operands, atNode, tagAt, argAt⟩, ha, hb, valid⟩ := code.2.2.2.2 i.val node
  obtain ⟨_, _, one⟩ := code.2.2.2.1.1 i.val node
  have rowEq : row = p.val := (one row atNode).trans (one p.val hi).symm
  subst row
  have tagIn : N.mem tag w := by
    rcases valid with ⟨tag, _⟩ | ⟨tag, _⟩ | ⟨tag, _⟩ | ⟨tag, _⟩ | ⟨tag, _⟩
    all_goals exact ((N.numeral_def _ _).mp tag).symm ▸ N.numeral_in_omega omega _
  let tag' : N.Active := ⟨tag, active_transitive N.laws activeW tagIn⟩
  let a' : N.Active := ⟨a, active_transitive N.laws activeW ha⟩
  let b' : N.Active := ⟨b, active_transitive N.laws activeW hb⟩
  let args : N.Active := ⟨operands, (N.orderedPair_coordinates tagAt p.property).2⟩
  have argsFixed := N.fixes_orderedPair a' b' args argAt
    (N.fixes_natural omega activeW a' ha) (N.fixes_natural omega activeW b' hb)
  exact ⟨N.fixes_natural omega activeW i iIn,
    N.fixes_orderedPair tag' args p tagAt (N.fixes_natural omega activeW tag' tagIn) argsFixed⟩

end PalomarI3380.SquareRepresentation.NamedModel
