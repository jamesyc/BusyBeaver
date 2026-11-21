module
public import I0451.FastGraph

/-! Shared subroutines can be entered with different earlier bits.
This checker compares their decoded branches, stopping immediately
when the same control and context have been reached. -/
@[expose] public section
namespace I0451.Runtime

def compareArms (equivalent : Edge → Edge → Bool) (a b : Cursor) (bit : Bool) : Bool :=
  (cachedOutgoing a bit).any fun l => (cachedOutgoing b bit).any (equivalent l)

def sameProgram : Nat → Edge → Edge → Bool
  | fuel, left, right =>
    if left == right then true
    else
      match fuel, left, right with
      | fuel + 1, .branch a, .branch b =>
        [false, true].all (compareArms (sameProgram fuel) a b)
      | _, _, _ => false

inductive SameProgram : Edge → Edge → Prop where
  | same (edge : Edge) : SameProgram edge edge
  | branch (a b : Cursor) {l₀ l₁ r₀ r₁ : Edge}
      (leftA : outgoing a false = some l₀) (leftB : outgoing b false = some r₀)
      (rightA : outgoing a true = some l₁) (rightB : outgoing b true = some r₁)
      (sameLeft : SameProgram l₀ r₀) (sameRight : SameProgram l₁ r₁) :
      SameProgram (.branch a) (.branch b)

theorem sameProgram_sound {fuel : Nat} {left right : Edge} (checked : sameProgram fuel left right = true) :
    SameProgram left right := by
  induction fuel generalizing left right with
  | zero =>
    by_cases h : left = right
    · subst right
      exact .same _
    · simp [sameProgram, h] at checked
  | succ fuel ih =>
    by_cases h : left = right
    · subst right
      exact .same _
    · cases left with
      | instruction op => simp [sameProgram, h] at checked
      | branch a =>
        cases right with
        | instruction op => simp [sameProgram, h] at checked
        | branch b =>
          have all : [false, true].all (compareArms (sameProgram fuel) a b) = true := by
            simpa only [sameProgram, beq_iff_eq, ite_eq_right h] using checked
          have children (bit : Bool) :
              ∃ l r, outgoing a bit = some l ∧ outgoing b bit = some r ∧ SameProgram l r := by
            have bitMem : bit ∈ [false, true] := by cases bit <;> decide
            have test := List.all_eq_true.mp all bit bitMem
            unfold compareArms at test
            cases l : cachedOutgoing a bit with
            | none => simp [l] at test
            | some l' =>
              cases r : cachedOutgoing b bit with
              | none => simp [l, r] at test
              | some r' => exact ⟨l', r', cachedOutgoing_sound l, cachedOutgoing_sound r,
                ih (by simpa only [l, r, Option.any] using test)⟩
          obtain ⟨l₀, r₀, al, bl, ll⟩ := children false
          obtain ⟨l₁, r₁, ar, br, rr⟩ := children true
          exact .branch a b al bl ar br ll rr

theorem SameProgram.branch_view {a : Cursor} {target : Edge}
    (same : SameProgram (.branch a) target) :
    ∃ b, target = .branch b ∧ ∀ bit l, outgoing a bit = some l →
      ∃ r, outgoing b bit = some r ∧ SameProgram l r := by
  cases same with
  | same => exact ⟨a, rfl, fun bit l edge => ⟨l, edge, .same _⟩⟩
  | branch _ b al bl ar br sameLeft sameRight =>
    refine ⟨b, rfl, fun bit l edge => ?_⟩
    cases bit
    · have eq := Option.some.inj (edge.symm.trans al)
      subst l
      exact ⟨_, bl, sameLeft⟩
    · have eq := Option.some.inj (edge.symm.trans ar)
      subst l
      exact ⟨_, br, sameRight⟩

theorem SameProgram.trans {a b c : Edge} (ab : SameProgram a b) (bc : SameProgram b c) :
    SameProgram a c := by
  induction ab generalizing c with
  | same => exact bc
  | branch a b al bl ar br _ _ ihLeft ihRight =>
    obtain ⟨target, rfl, children⟩ := bc.branch_view
    obtain ⟨left, leftEdge, similarLeft⟩ := children false _ bl
    obtain ⟨right, rightEdge, similarRight⟩ := children true _ br
    exact .branch a target al leftEdge ar rightEdge (ihLeft similarLeft) (ihRight similarRight)

/-- Structurally equal decoded branches have the same executions. -/
theorem Executes.share {edge target : Edge} {s finish : Registers} {result : Signal}
    (run : Executes edge s result finish) (same : SameProgram edge target) :
    Executes target s result finish := by
  induction run generalizing target with
  | inc i regs =>
    cases same
    exact .inc _ _
  | decPositive i regs v h =>
    cases same
    exact .decPositive _ _ _ h
  | decZero i regs h =>
    cases same
    exact .decZero _ _ h
  | «break» depth regs =>
    cases same
    exact .break _ _
  | restart depth regs =>
    cases same
    exact .restart _ _
  | halt regs =>
    cases same
    exact .halt _
  | leftExit left runLeft signal ih =>
    obtain ⟨cursor, rfl, children⟩ := same.branch_view
    obtain ⟨edge, branch, similar⟩ := children false _ left
    exact .leftExit branch (ih similar) signal
  | rightExit left right runLeft runRight signal ihLeft ihRight =>
    obtain ⟨cursor, rfl, children⟩ := same.branch_view
    obtain ⟨leftEdge, le, similarLeft⟩ := children false _ left
    obtain ⟨rightEdge, re, similarRight⟩ := children true _ right
    exact .rightExit le re (ihLeft similarLeft) (ihRight similarRight) signal
  | «repeat» left right runLeft runRight runAgain ihLeft ihRight ihAgain =>
    obtain ⟨cursor, rfl, children⟩ := same.branch_view
    obtain ⟨leftEdge, le, similarLeft⟩ := children false _ left
    obtain ⟨rightEdge, re, similarRight⟩ := children true _ right
    exact .repeat le re (ihLeft similarLeft) (ihRight similarRight) (ihAgain same)

end I0451.Runtime
