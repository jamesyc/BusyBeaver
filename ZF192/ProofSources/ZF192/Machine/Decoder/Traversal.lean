module
public import ZF192.Machine.Decoder.Window
@[expose] public section

namespace M192.Window

abbrev WindowRun := Nat → Nat → List Bool → List Bool → Option (Nat × List Bool × List Bool)

/-- Follow the leftward decoder along the address. The rest of the window is
kept separate until the first turn or the padding boundary. -/
def followAddress (stop : Nat → List Bool → Bool) (resume : WindowRun)
    (padding : List Bool) :
    List Bool → Nat → Nat → List Bool → Option (Nat × List Bool × List Bool)
  | bit :: path, fuel + 1, q, b :: right =>
    if stop q (bit :: path ++ padding) then some (q, bit :: path ++ padding, b :: right)
    else
      match literal q b with
      | some (w, false, next) => followAddress stop resume padding path fuel next (bit :: w :: right)
      | _ => resume (fuel + 1) q (bit :: path ++ padding) (b :: right)
  | path, fuel, q, right => resume fuel q (path ++ padding) right

theorem followAddress_eq (stop : Nat → List Bool → Bool) (resume : WindowRun)
    (hr : resume = wrun stop) (padding path : List Bool) (fuel q : Nat) (right : List Bool) :
    followAddress stop resume padding path fuel q right =
      wrun stop fuel q (path ++ padding) right := by
  subst resume
  induction path generalizing fuel q right with
  | nil => rfl
  | cons bit path ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases right with
      | nil => rfl
      | cons b right =>
        by_cases hs : stop q (bit :: (path ++ padding)) = true
        · simp [followAddress, wrun, hs]
        · cases h : literal q b with
          | none => simp [followAddress, hs, h]
          | some row =>
            obtain ⟨w, dir, next⟩ := row
            cases dir
            · simpa [followAddress, wrun, wstep, hs, h] using ih fuel next (bit :: w :: right)
            · simp [followAddress, hs, h]

/-- The first move is forced before testing the stopping predicate. -/
def runAddress (stop : Nat → List Bool → Bool) (resume : WindowRun)
    (fuel : Nat) (p : List Bool) : Option (Nat × List Bool × List Bool) :=
  let address := ((p.drop 1).take 38).map (!·)
  let padding := List.replicate (38 - (p.drop 1).length) true
  match address, winR p with
  | bit :: path, b :: right =>
    match literal root b with
    | some (w, false, next) => followAddress stop resume padding path fuel next (bit :: w :: right)
    | _ => wrun1 stop fuel root (address ++ padding) (b :: right)
  | _, right => wrun1 stop fuel root (address ++ padding) right

theorem runAddress_eq (stop : Nat → List Bool → Bool) (resume : WindowRun)
    (hr : resume = wrun stop) (fuel : Nat) (p : List Bool) :
    runAddress stop resume fuel p = wrun1 stop fuel root (winL p) (winR p) := by
  unfold runAddress winL
  dsimp only
  cases ((p.drop 1).take 38).map (!·) with
  | nil => rfl
  | cons bit path =>
    cases winR p with
    | nil => rfl
    | cons b right =>
      cases h : literal root b with
      | none => simp [h]
      | some row =>
        obtain ⟨w, dir, next⟩ := row
        cases dir
        · simp [h, wrun1, wstep, followAddress_eq stop resume hr]
        · simp [h]

/-- A leftward selector crosses all remaining padding before the gate. -/
theorem leftPadding (q : Nat) (row : literal q true = some (true, false, q))
    (n fuel : Nat) (right : List Bool) :
    wrun (fun _ l => l.isEmpty) (n + fuel + 1) q (List.replicate n true) (true :: right) =
      some (q, [], List.replicate (n + 1) true ++ right) := by
  induction n generalizing right with
  | zero => simp [wrun]
  | succ n ih =>
    calc
      _ = wrun (fun _ l => l.isEmpty) (n + fuel + 1) q (List.replicate n true)
          (true :: true :: right) := by
        simp [Nat.succ_add, wrun, wstep, row, List.replicate_succ]
      _ = _ := by rw [ih, List.replicate_succ' (n := n + 1), List.append_assoc]; rfl

/-- A rightward scan crosses the entire preserved padding prefix. -/
theorem rightPadding (q : Nat) (row : literal q true = some (true, true, q))
    (stop : Nat → List Bool → Bool) (live : ∀ l, stop q l = false) (n fuel : Nat)
    (left right : List Bool) :
    wrun stop (n + fuel) q left (List.replicate n true ++ right) =
      wrun stop fuel q (List.replicate n true ++ left) right := by
  induction n generalizing left with
  | zero => simp
  | succ n ih =>
    calc
      _ = wrun stop (n + fuel) q (true :: left) (List.replicate n true ++ right) := by
        simp only [Nat.succ_add, List.replicate_succ, List.cons_append, wrun, live,
          Bool.false_eq_true, ite_false, wstep, row]
      _ = _ := by rw [ih, List.replicate_succ', List.append_assoc]; rfl

end M192.Window
