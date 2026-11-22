module
public import ZF192.Machine.FiniteChecks
public import ZF192.Machine.Decoder.Traversal
public import ZF192.Machine.Decoder.Paths
@[expose] public section
/-! # Fixed-corridor interfaces for the contextual decoder

A decoder run either reaches the appropriate selector at the file-side cut,
returns directly to the root, or enters the halt state. Arithmetic returns
start on the program side of that cut. The row checks compare both sides of
the finite window with the expected source address. -/
namespace M192.Sites
open M192.Window M192.Paths
open RegisterMachine.Source (Instruction instructionBound)

def fuel : Nat := 200
def atGate (_ : Nat) (wl : List Bool) : Bool := wl.isEmpty
def atRoot (q : Nat) (wl : List Bool) : Bool := q == root && wl.length == 38
def atHalt (q : Nat) (_ : List Bool) : Bool := q == halt

/-- Once the selector sees only padding, its left self-loop reaches the gate. -/
def resumeGate : WindowRun
  | f, q, left, true :: right =>
    if left.length < f ∧ left.all id = true ∧ literal q true = some (true, false, q) then
      some (q, [], left ++ true :: right)
    else wrun atGate f q left (true :: right)
  | f, q, left, right => wrun atGate f q left right

private theorem allOnes {bs : List Bool} (h : bs.all id = true) :
    bs = List.replicate bs.length true :=
  List.eq_replicate_of_mem fun b hb => by simpa using (List.all_eq_true.mp h b hb)

theorem resumeGate_eq : resumeGate = wrun atGate := by
  funext f q left right
  cases right with
  | nil => rfl
  | cons bit right =>
    cases bit
    · rfl
    · by_cases h : left.length < f ∧ left.all id = true ∧
          literal q true = some (true, false, q)
      · simp only [resumeGate, ite_eq_left h]
        have hf : left.length + (f - left.length - 1) + 1 = f := by omega
        have run := leftPadding q h.2.2 left.length (f - left.length - 1) right
        rw [hf, List.replicate_succ', List.append_assoc, ← allOnes h.2.1] at run
        exact run.symm
      · simp only [resumeGate, ite_eq_right h]

def wrunRoot : WindowRun := wrun atRoot

theorem wrunRoot_eq : wrunRoot = wrun atRoot := rfl

/-- Both arithmetic return states cross the leading ones before the next branch. -/
def wrunReturn (q : Nat) (left right : List Bool) : Option (Nat × List Bool × List Bool) :=
  let padding := right.takeWhile id
  if (q = readSuccess ∨ q = readZero) ∧ padding.length ≤ fuel then
    wrunRoot (fuel - padding.length) q (padding ++ left) (right.dropWhile id)
  else wrunRoot fuel q left right

theorem wrunReturn_eq (q : Nat) (left right : List Bool) :
    wrunReturn q left right = wrun atRoot fuel q left right := by
  unfold wrunReturn
  simp only [wrunRoot_eq]
  split
  · rename_i h
    have hrow : literal q true = some (true, true, q) :=
      h.1.elim (fun e => e ▸ row_readSuccess_1) (fun e => e ▸ row_readZero_1)
    have hstop : ∀ l, atRoot q l = false := by
      intro l
      rcases h.1 with rfl | rfl <;> rfl
    have run := rightPadding q hrow atRoot hstop (right.takeWhile id).length
      (fuel - (right.takeWhile id).length) left (right.dropWhile id)
    rw [Nat.add_sub_of_le h.2, ← allOnes List.all_takeWhile, List.takeWhile_append_dropWhile] at run
    exact run.symm
  · rfl

def frameIs (k : Nat) (wl wr : List Bool) : Bool := wl == winL (fpath k) && wr == winR (fpath k)

/-- After a macro: from window cell 1 in state `q` (cell 0, padding, on its left) back to the
root at site `k`. -/
def backTo (q : Nat) (wr : List Bool) (k : Nat) : Bool :=
  match wr with
  | true :: rest =>
    match wrunReturn q [true] rest with
    | some (_, wl', wr') => frameIs k wl' wr'
    | none => false
  | _ => false

def toGate (i : Nat) : Option (Nat × List Bool × List Bool) :=
  runAddress atGate resumeGate fuel (fpath i)

theorem toGate_eq (i : Nat) :
    toGate i = wrun1 atGate fuel root (winL (fpath i)) (winR (fpath i)) :=
  runAddress_eq atGate resumeGate resumeGate_eq _ _

def instructionCheck (i : Nat) : Instruction → Bool
  | .inc r k =>
    match toGate i with
    | some (q, _, wr) => q == chainI.getD (r + 2) 0 && backTo readSuccess wr k
    | none => false
  | .dec r z k =>
    match toGate i with
    | some (q, _, wr) =>
      q == chainD.getD (r + 2) 0 && backTo readZero wr z && backTo readSuccess wr k
    | none => false
  | .jump k =>
    match runAddress atRoot wrunRoot fuel (fpath i) with
    | some (_, wl', wr') => frameIs k wl' wr'
    | none => false
  | .halt => (runAddress atHalt (wrun atHalt) fuel (fpath i)).isSome

def siteCheck (i : Nat) : Bool :=
  match program i with
  | none => true
  | some code => decide (instructionBound siteCount code) && instructionCheck i code

abbrev blockCheck : Nat → Nat → Bool := M192.FiniteChecks.block siteCheck

theorem of_blockCheck {P : Nat → Prop} (sound : ∀ i, siteCheck i = true → P i) (base count : Nat)
    (checked : blockCheck base count = true) : ∀ i, i < count → P (base + i) := by
  intro i hi
  apply sound
  exact List.all_eq_true.mp checked _ (List.mem_range'.mpr ⟨i, hi, by simp⟩)

end M192.Sites
