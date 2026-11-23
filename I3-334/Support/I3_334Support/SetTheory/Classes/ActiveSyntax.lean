module
public import I3_334Support.SetTheory.Classes.TruthSets
public import I3_334Support.SetTheory.Classes.SyntaxModel
@[expose] public section

namespace PalomarI3380.SquareRepresentation.NamedModel

open Logic SetContext

variable {A V : Type} {M : Algebra A} (N : NamedModel M V)

theorem active_truthSet_exists {w arity count rows stage : V} (hw : Internal.Omega N.mem w)
    (wActive : N.square.activePoint w) (stageActive : N.square.activePoint stage)
    (code : Internal.SyntaxCode N.mem w arity count rows) :
    ∃ sat, N.square.activePoint sat ∧ Internal.TruthSet N.mem arity count rows stage sat := by
  obtain ⟨space, sat, spaces, included, truth⟩ := N.truthSet_exists hw code stage
  have spaceActive := N.assignmentSpace_active spaces (active_transitive N.laws wActive code.1) stageActive
  have boundActive := N.active_pairBound (active_transitive N.laws wActive code.2.1) spaceActive
  exact ⟨sat, active_subset N.laws boundActive included, truth⟩

theorem absolute_functionInto (f d r : N.Active) :
    Internal.FunctionInto N.localMem f d r ↔ Internal.FunctionInto N.mem f.val d.val r.val := by
  refine and_congr (N.absolute_functionOn f d) ?_
  constructor
  · intro h x hx y hy
    have active := N.active_graph_coordinates hy f.property
    exact h ⟨x, active.1⟩ hx ⟨y, active.2⟩ ((N.absolute_at _ _ _).mpr hy)
  · exact fun h x hx y hy => h x.val hx y.val ((N.absolute_at _ _ _).mp hy)

theorem absolute_numeral (n : Nat) (a : N.Active) :
    Internal.Numeral N.localMem n a ↔ Internal.Numeral N.mem n a.val := by
  induction n generalizing a with
  | zero => exact N.absolute_empty a
  | succ n ih =>
    constructor
    · rintro ⟨b, hb, succ⟩
      exact ⟨b.val, (ih b).mp hb, (N.absolute_successor b a).mp succ⟩
    · rintro ⟨b, hb, succ⟩
      let previous : N.Active := ⟨b, active_transitive N.laws a.property ((succ b).mpr (Or.inr rfl))⟩
      exact ⟨previous, (ih previous).mpr hb, (N.absolute_successor previous a).mpr succ⟩

theorem rowAt_coordinates {rows i tag a b : V} (active : N.square.activePoint rows)
    (code : Internal.RowAt N.mem rows i tag a b) :
    N.square.activePoint i ∧ N.square.activePoint tag ∧ N.square.activePoint a ∧ N.square.activePoint b := by
  obtain ⟨row, pair, hr, tagPair, args⟩ := code
  have outer := N.active_graph_coordinates hr active
  have decoded := N.orderedPair_coordinates tagPair outer.2
  exact ⟨outer.1, decoded.1, N.orderedPair_coordinates args decoded.2⟩

theorem absolute_rowAt (r i tag a b : N.Active) :
    Internal.RowAt N.localMem r i tag a b ↔ Internal.RowAt N.mem r.val i.val tag.val a.val b.val := by
  constructor
  · rintro ⟨p, q, edge, dec, pair⟩
    exact ⟨p.val, q.val, (N.absolute_at _ _ _).mp edge, (N.absolute_orderedPair _ _ _).mp dec,
      (N.absolute_orderedPair _ _ _).mp pair⟩
  · rintro ⟨p, q, edge, dec, pair⟩
    let row : N.Active := ⟨p, (N.active_graph_coordinates edge r.property).2⟩
    let args : N.Active := ⟨q, (N.orderedPair_coordinates dec row.property).2⟩
    exact ⟨row, args, (N.absolute_at _ _ _).mpr edge, (N.absolute_orderedPair _ _ _).mpr dec,
      (N.absolute_orderedPair _ _ _).mpr pair⟩

theorem absolute_validRow (a i t x y : N.Active) :
    Internal.ValidRow N.localMem a i t x y ↔ Internal.ValidRow N.mem a.val i.val t.val x.val y.val := by
  simp only [Internal.ValidRow, N.absolute_numeral, localMem]

theorem absolute_code (w a c r : N.Active) :
    Internal.SyntaxCode N.localMem w a c r ↔ Internal.SyntaxCode N.mem w.val a.val c.val r.val := by
  refine and_congr_right fun _ => and_congr_right fun _ =>
    and_congr (not_congr (N.absolute_empty c)) (and_congr (N.absolute_functionOn r c) ?_)
  constructor
  · intro rows i hi
    let node : N.Active := ⟨i, active_transitive N.laws c.property hi⟩
    obtain ⟨tag, x, y, stored, hx, hy, valid⟩ := rows node hi
    exact ⟨tag.val, x.val, y.val, (N.absolute_rowAt _ _ _ _ _).mp stored, hx, hy,
      (N.absolute_validRow _ _ _ _ _).mp valid⟩
  · intro rows i hi
    obtain ⟨tag, x, y, stored, hx, hy, valid⟩ := rows i.val hi
    obtain ⟨_, htag, ha, hb⟩ := N.rowAt_coordinates r.property stored
    let t : N.Active := ⟨tag, htag⟩
    let a₀ : N.Active := ⟨x, ha⟩
    let b₀ : N.Active := ⟨y, hb⟩
    exact ⟨t, a₀, b₀, (N.absolute_rowAt _ _ _ _ _).mpr stored, hx, hy,
      (N.absolute_validRow _ _ _ _ _).mpr valid⟩

theorem absolute_agrees (a f g i : N.Active) :
    Internal.AgreesAway N.localMem a f g i ↔ Internal.AgreesAway N.mem a.val f.val g.val i.val := by
  constructor
  · intro h j hj diff value
    let k : N.Active := ⟨j, active_transitive N.laws a.property hj⟩
    have different : k ≠ i := fun eq => diff (congrArg Subtype.val eq)
    constructor
    · intro atF
      let y : N.Active := ⟨value, (N.active_graph_coordinates atF f.property).2⟩
      exact (N.absolute_at g k y).mp ((h k hj different y).mp ((N.absolute_at f k y).mpr atF))
    · intro atG
      let y : N.Active := ⟨value, (N.active_graph_coordinates atG g.property).2⟩
      exact (N.absolute_at f k y).mp ((h k hj different y).mpr ((N.absolute_at g k y).mpr atG))
  · intro h j hj different value
    have key : j.val ≠ i.val := fun eq => different (Subtype.ext eq)
    exact (N.absolute_at f j value).trans ((h j.val hj key value.val).trans (N.absolute_at g j value).symm)

theorem absolute_atomic {P : N.Active → N.Active → Prop} {Q : V → V → Prop}
    (describes : ∀ x y, P x y ↔ Q x.val y.val) (e a b : N.Active) :
    Internal.AtomicTruth N.localMem P e a b ↔ Internal.AtomicTruth N.mem Q e.val a.val b.val := by
  constructor
  · rintro ⟨x, y, ax, by_, h⟩
    exact ⟨x.val, y.val, (N.absolute_at _ _ _).mp ax, (N.absolute_at _ _ _).mp by_, (describes x y).mp h⟩
  · rintro ⟨x, y, ax, by_, h⟩
    let x' : N.Active := ⟨x, (N.active_graph_coordinates ax e.property).2⟩
    let y' : N.Active := ⟨y, (N.active_graph_coordinates by_ e.property).2⟩
    exact ⟨x', y', (N.absolute_at _ _ _).mpr ax, (N.absolute_at _ _ _).mpr by_, (describes x' y').mpr h⟩

theorem absolute_rowTruth (a s sat env t x y : N.Active) :
    Internal.RowTruth N.localMem (Internal.At N.localMem sat) a s env t x y ↔
      Internal.RowTruth N.mem (Internal.At N.mem sat.val) a.val s.val env.val t.val x.val y.val := by
  unfold Internal.RowTruth
  have equality := N.absolute_atomic (P := Eq) (Q := Eq)
    (fun _ _ => ⟨congrArg Subtype.val, Subtype.ext⟩) env x y
  have member := N.absolute_atomic (P := N.localMem) (Q := N.mem) (fun _ _ => Iff.rfl) env x y
  refine or_congr (and_congr (N.absolute_numeral 0 t) equality)
    (or_congr (and_congr (N.absolute_numeral 1 t) member)
      (or_congr (and_congr (N.absolute_numeral 2 t) (not_congr (N.absolute_at sat x env)))
        (or_congr (and_congr (N.absolute_numeral 3 t) (and_congr (N.absolute_at sat x env) (N.absolute_at sat y env))) ?_)))
  refine and_congr (N.absolute_numeral 4 t) ?_
  constructor
  · rintro ⟨amended, typed, agrees, truth⟩
    exact ⟨amended.val, (N.absolute_functionInto _ _ _).mp typed, (N.absolute_agrees _ _ _ _).mp agrees,
      (N.absolute_at _ _ _).mp truth⟩
  · rintro ⟨amended, typed, agrees, truth⟩
    let f : N.Active := ⟨amended, N.assignment_active typed a.property s.property⟩
    exact ⟨f, (N.absolute_functionInto _ _ _).mpr typed, (N.absolute_agrees _ _ _ _).mpr agrees,
      (N.absolute_at _ _ _).mpr truth⟩

theorem absolute_truthSet (a c r s sat : N.Active) :
    Internal.TruthSet N.localMem a c r s sat ↔ Internal.TruthSet N.mem a.val c.val r.val s.val sat.val := by
  constructor
  · intro truth i iIn assignment typed
    let node : N.Active := ⟨i, active_transitive N.laws c.property iIn⟩
    let env : N.Active := ⟨assignment, N.assignment_active typed a.property s.property⟩
    obtain ⟨tag, x, y, row, clauses⟩ := truth node iIn env ((N.absolute_functionInto _ _ _).mpr typed)
    exact ⟨tag.val, x.val, y.val, (N.absolute_rowAt _ _ _ _ _).mp row,
      (N.absolute_at _ _ _).symm.trans (clauses.trans (N.absolute_rowTruth _ _ _ _ _ _ _))⟩
  · intro truth i iIn env typed
    obtain ⟨tag, x, y, row, clauses⟩ := truth i.val iIn env.val ((N.absolute_functionInto _ _ _).mp typed)
    obtain ⟨_, hTag, hX, hY⟩ := N.rowAt_coordinates r.property row
    let t : N.Active := ⟨tag, hTag⟩
    let a₀ : N.Active := ⟨x, hX⟩
    let b₀ : N.Active := ⟨y, hY⟩
    exact ⟨t, a₀, b₀, (N.absolute_rowAt _ _ _ _ _).mpr row,
      (N.absolute_at _ _ _).trans (clauses.trans (N.absolute_rowTruth a s sat env t a₀ b₀).symm)⟩

end PalomarI3380.SquareRepresentation.NamedModel
