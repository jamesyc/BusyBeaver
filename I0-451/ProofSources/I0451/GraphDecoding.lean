module
public import I0451.ControlFlow

/-! Pointer prefixes in the structured graph agree with logical decoding
of the same packed address in the literal interpreter. -/
@[expose] public section
namespace I0451.Runtime

def Cursor.rank (c : Cursor) : Nat := Decoder.rank c.control c.previous c.earlier

private def WithinRank (start : Cursor) (word : List Bool) (finish : Edge) : Prop :=
  match finish with
  | .branch c => 0 < c.rank ∧ word.length + c.rank ≤ start.rank
  | .instruction _ => word.length ≤ start.rank

private theorem follows_rank {start : Cursor} {word : List Bool} {edge : Edge}
    (live : 0 < start.rank) (reached : follow start word = some edge) :
    WithinRank start word edge := by
  induction word generalizing start edge with
  | nil =>
    simp only [follow, Option.some.injEq] at reached
    subst edge
    exact ⟨live, by simp⟩
  | cons b tail ih =>
    cases move : Decoder.arm start.control start.previous start.earlier b with
    | none => simp [follow, outgoing, move] at reached
    | some answer =>
      cases answer with
      | inl q =>
        let child : Cursor := ⟨q, b, start.previous⟩
        obtain ⟨n, out, short, run, outcome⟩ := Decoder.arm_sound move
        cases outcome with
        | descend q positive decreases =>
          have route : follow child tail = some edge := by
            simpa only [follow, outgoing, move] using reached
          have childWithin := ih (start := child) positive route
          have rankDrops : child.rank < start.rank := decreases
          cases edge with
          | branch endCursor =>
            obtain ⟨endLive, inner⟩ := childWithin
            refine ⟨endLive, ?_⟩
            simp only [List.length_cons]
            omega
          | instruction op =>
            have inner : tail.length ≤ child.rank := childWithin
            show tail.length + 1 ≤ start.rank
            omega
      | inr out =>
        cases dispatch : instruction out with
        | none => simp [follow, outgoing, move, dispatch] at reached
        | some op =>
          cases tail with
          | nil =>
            simp only [follow, outgoing, move, dispatch, Option.map_some, List.isEmpty_nil,
              ite_true, Option.some.injEq] at reached
            subst edge
            exact live
          | cons x xs => simp [follow, outgoing, move, dispatch] at reached

private theorem instruction_decode {start : Cursor} {word : List Bool} {op : Instruction}
    (path : follow start word = some (.instruction op)) {fuel : Nat} (bound : word.length ≤ fuel) :
    ∃ out, instruction out = some op ∧
      Decoder.decode fuel start.control start.previous start.earlier (pack word 0) =
        some ⟨word, 0, out⟩ := by
  induction word generalizing start fuel with
  | nil => simp [follow] at path
  | cons b tail ih =>
    cases fuel with
    | zero => simp at bound
    | succ fuel =>
      cases move : Decoder.arm start.control start.previous start.earlier b with
      | none => simp [follow, outgoing, move] at path
      | some choice =>
        cases choice with
        | inl q =>
          have descent : follow ⟨q, b, start.previous⟩ tail = some (.instruction op) := by
            simpa only [follow, outgoing, move] using path
          obtain ⟨out, decodeOp, parsed⟩ := ih descent (by simp at bound; omega)
          refine ⟨out, decodeOp, ?_⟩
          simp only [pack_cons, Decoder.decode, bit_push, pop_push, move, parsed, Option.map_some]
        | inr out =>
          cases output : instruction out with
          | none => simp [follow, outgoing, move, output] at path
          | some r =>
            cases tail with
            | nil =>
              refine ⟨out, ?_, ?_⟩
              · simp [follow, outgoing, move, output] at path
                simpa only [path] using output
              · simp only [pack_cons, pack_nil, Decoder.decode, bit_push, pop_push, move]
            | cons c cs => simp [follow, outgoing, move, output] at path

theorem AtEdge.length_le {word : List Bool} {edge : Edge} (path : AtEdge word edge) :
    word.length ≤ 94 := by
  have depth : rootCursor.rank = 94 := Decoder.root_rank _ _
  have within := follows_rank (by rw [depth]; decide) path
  cases edge with
  | branch next =>
    have limit := within.2
    omega
  | instruction op => exact depth ▸ within

theorem AtEdge.decode {word : List Bool} {op : Instruction}
    (path : AtEdge word (.instruction op)) :
    ∃ out, instruction out = some op ∧
      Decoder.decode 94 root true false (pack word 0) = some ⟨word, 0, out⟩ := by
  have initial : 0 < rootCursor.rank := by
    change 0 < Decoder.rank root true false
    rw [Decoder.root_rank]
    decide
  have within : word.length ≤ rootCursor.rank := follows_rank initial path
  have maxDepth : rootCursor.rank = 94 := Decoder.root_rank _ _
  rw [maxDepth] at within
  exact instruction_decode path within

end I0451.Runtime
