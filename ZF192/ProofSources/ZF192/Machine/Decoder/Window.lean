module
public import ZF192.Machine.RegisterProtocol
@[expose] public section
/-! # The program window

The program side of ZF192 is a fixed finite word of 47 cells around the root (cell 38): the
address occupies cells 38, 37, … leftward, cells 0–37 beyond the address are padding (physical
1), cell 39 is the home marker (0) and cells 40–45 the guard (1), and cell 46 the guard endpoint (0). Further left lie a run of
padding of arbitrary length, the two gate cells and the register file; further right the tape
is arbitrary. A window configuration is a zipper `(wl, wr)` of the word: `wl` lists the cells
left of the head, nearest first, and the head reads the first cell of `wr`. `wrun` executes
literal rows on the window and fails if the head would read outside it, and `wrun1` forces a step before testing the stop condition.
The common soundness proof in `ZF192.Simulation.Window` allows arbitrary tape outside the window. -/
namespace M192.Window

/-- Physical cell `i` of the window when the program address is `p` (cell `38-k` holds the
complement of address bit `k`; unused address cells hold 1). -/
def cellAt (p : List Bool) (i : Nat) : Bool :=
  if i = 39 ∨ i = 46 then false
  else if i ≤ 38 ∧ 38 - i < p.length then !(p.getD (38 - i) false) else true

/-- Cells 37, …, 0, traversing the address once and filling the remaining cells. -/
def winL (p : List Bool) : List Bool :=
  ((p.drop 1).take 38).map (!·) ++ List.replicate (38 - (p.drop 1).length) true

/-- The home marker, six guard bits, and the endpoint. -/
def homeGuard : List Bool := false :: List.replicate 6 true ++ [false]

/-- Cells 38, …, 46, from the root through the guard endpoint. -/
def winR (p : List Bool) : List Bool := (!(p.headD false)) :: homeGuard

theorem winL_cells (p : List Bool) :
    winL p = (List.range 38).reverse.map (cellAt p) := by
  apply List.ext_getElem
  · simp [winL]
    omega
  · intro i hi hj
    have hi38 : i < 38 := by simpa using hj
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range] at ⊢
    have dist : 38 - (38 - 1 - i) = 1 + i := by omega
    have view : 38 - 1 - i ≤ 38 := by omega
    have away : ¬ (38 - 1 - i = 39 ∨ 38 - 1 - i = 46) := by omega
    simp only [winL] at hi ⊢
    rw [cellAt, if_neg away, dist]
    by_cases present : 1 + i < p.length
    · have h : i < (((p.drop 1).take 38).map (!·)).length := by
        simp
        omega
      rw [List.getElem_append_left h]
      rw [ite_eq_left (show 38 - 1 - i ≤ 38 ∧ 1 + i < p.length from ⟨view, present⟩)]
      have within : i + 1 < p.length := by omega
      simp [List.getD_eq_getElem?_getD, Nat.add_comm, getElem?_pos p (i + 1) within]
    · have h : (((p.drop 1).take 38).map (!·)).length ≤ i := by
        simp
        omega
      rw [List.getElem_append_right h]
      rw [ite_eq_right (fun ha : 38 - 1 - i ≤ 38 ∧ 1 + i < p.length => present ha.2)]
      exact List.getElem_replicate _

theorem winR_cells (p : List Bool) :
    winR p = (List.range 9).map (fun j => cellAt p (38 + j)) := by
  cases p with
  | nil => rfl
  | cons b p =>
    cases b <;> rfl

def wstep (q : Nat) (wl wr : List Bool) : Option (Nat × List Bool × List Bool) :=
  match wr with
  | [] => none
  | c :: rs =>
    match literal q c with
    | none => none
    | some (b, true, q') => some (q', b :: wl, rs)
    | some (b, false, q') =>
      match wl with
      | [] => none
      | a :: ls => some (q', ls, a :: b :: rs)

/-- Run until `stop` holds (checked before every step). -/
def wrun (stop : Nat → List Bool → Bool) : Nat → Nat → List Bool → List Bool →
    Option (Nat × List Bool × List Bool)
  | 0, _, _, _ => none
  | f + 1, q, wl, wr =>
    if stop q wl then some (q, wl, wr)
    else match wstep q wl wr with
      | none => none
      | some (q', wl', wr') => wrun stop f q' wl' wr'

/-- One forced step, then `wrun`. -/
def wrun1 (stop : Nat → List Bool → Bool) (f q : Nat) (wl wr : List Bool) :
    Option (Nat × List Bool × List Bool) :=
  match wstep q wl wr with
  | none => none
  | some (q', wl', wr') => wrun stop f q' wl' wr'

end M192.Window
