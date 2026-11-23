module
public import I3_334.Simulation.DecoderWalk
public import I3_334Support.Search.Compiler.Paths
@[expose] public section

namespace PalomarI3334

open PalomarI3380 PalomarI3380.Compiler
open Control (root)
open Decoder (Result follow transition height exitAt)

/-- Unfold only the read-only decoder DAG. The leaves are the exact
primitive operations named by the checked physical exit ports. -/
def tableNode : Nat → Nat → Program
  | 0, _ => .op .halt
  | fuel+1, q =>
    let branch := fun b =>
      let target := (transition q b).target
      if 0 < height target then tableNode fuel target
      else .op ((exitAt target).getD .halt).op
    .seq (branch false) (branch true)

def referenceProgram : Program := tableNode 70 root

theorem tableNode_walk {fuel q : Nat} {before input : List Bool} {d : Result}
    (found : follow fuel q before input = some d) :
    (walk (tableNode fuel q) input).1 = d.command.op ∧
      before.reverse ++ (walk (tableNode fuel q) input).2 = d.path := by
  induction fuel generalizing q before input d with
  | zero => simp [follow] at found
  | succ fuel ih =>
    cases input with
    | nil => simp [follow] at found
    | cons b rest =>
      by_cases range : q < 344
      · let next := (transition q b).target
        have arm : walk (tableNode (fuel+1) q) (b :: rest) =
          let branch := if 0 < height next then tableNode fuel next
            else .op ((exitAt next).getD .halt).op
          let result := walk branch rest
          (result.1, b :: result.2) := by
            cases b <;> simp only [next, tableNode, walk, List.headD_cons, List.tail_cons,
              Bool.false_eq_true, ↓reduceIte]
        rw [arm]
        by_cases deeper : 0 < height next
        · have child : follow fuel next (b :: before) rest = some d := by
            simpa only [follow, range, dite_true, show 0 < height (transition q b).target from deeper,
              ↓reduceIte] using found
          have proof := ih child
          simp only [deeper, ↓reduceIte]
          exact ⟨proof.1, by simpa only [List.reverse_cons, List.append_assoc,
            List.singleton_append] using proof.2⟩
        · cases exit : exitAt next with
          | none => simp [follow, range, next, deeper, exit] at found
          | some op =>
            have reported : (⟨⟨q, range⟩, before, b, rest, op⟩ : Result) = d := by
              simpa only [follow, range, dite_true, show ¬0 < height (transition q b).target from deeper,
                ↓reduceIte, show exitAt (transition q b).target = some op from exit,
                Option.map_some, Option.some.injEq] using found
            subst d
            simp only [deeper, ↓reduceIte, Option.getD_some, walk, Result.path, true_and]
      · simp [follow, range] at found

end PalomarI3334
