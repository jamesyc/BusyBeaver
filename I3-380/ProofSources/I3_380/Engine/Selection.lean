module
public import I3_380.Engine.DecoderWalk
public import I3_380.Engine.Increment
public import I3_380.Engine.InstructionPointer
public import I3_380.Engine.FrameWords
@[expose] public section

namespace PalomarI3380.Engine

open scoped PalomarI3380.Engine

/-- The marked position is between two lists of registers.
The extra separator is the first of the two displayed zeros. -/
def marked (path : List Bool) (count gap : Nat) (before after : List Nat) : Configuration :=
  atRight Port.root [true] (path ++ (ones count ++
    (zeros gap ++ (registers before ++ false :: false :: reverseRegisters after))))

theorem marked_initial (path : List Bool) (gap : Nat) (rs : List Nat) :
    marked path 0 gap rs [] = frame path gap rs := by
  unfold marked frame
  rw [show ones 0 = [] by rfl, List.nil_append]
  change atRight Port.root [true] (path ++ (zeros gap ++ (registers rs ++ zeros 2))) =
    atRight Port.root [true] (path ++ (zeros gap ++ registers rs))
  rw [← List.append_assoc, ← List.append_assoc, atRight_pad]
  rw [List.append_assoc]

structure RegisterRoute (path : List Bool) (dec : Bool) (r : Fin 12) : Prop where
  short : shortZeros 0 path.reverse = true
  run : ∀ tail, atRight Port.root [true] (path ++ tail) ⟶+
      atRight (Port.registerEntry dec r.val) (path.reverse ++ [true]) tail

theorem DecodedFrom.register_route {input scanned : List Bool} {d : Decoded}
    (h : DecodedFrom 59 Port.root [] input scanned d)
    {dec : Bool} {r : Fin 12} (hc : d.command = .register dec r) :
    RegisterRoute scanned dec r := by
  have pathEq : scanned = d.path := h.pathEq
  have shape := h.shape
  rw [hc] at shape
  rcases shape with ⟨hRight, hWrite, hShort⟩
  have hPort := h.port
  rw [hc] at hPort
  change Port.registerEntry dec r.val = (transition d.node d.read).target at hPort
  constructor
  · rw [pathEq, Decoded.path, List.reverse_append, List.reverse_singleton,
      List.reverse_reverse, List.singleton_append]
    exact hShort
  · intro tail
    have run := h.progress [true] tail
    have hTail : d.read :: (d.before ++ [true]) = scanned.reverse ++ [true] := by
      rw [pathEq, Decoded.path, List.reverse_append, List.reverse_singleton,
        List.reverse_reverse, List.singleton_append, List.cons_append]
    simpa only [List.nil_append, Decoded.destination, Decoded.transition, hRight, ↓reduceIte, hWrite,
      ← hPort, hTail] using run

/-- One selector pass moves the register boundary by one and consumes one
zero from the gap. It leaves every register's value unchanged. -/
theorem select_cycle {path : List Bool} {dec : Bool} {r : Fin 12}
    (route : RegisterRoute path dec r) (n gap : Nat) (hn : n ≤ r.val)
    (before after : List Nat) (value : Nat) :
    marked path n (gap + 3) (before ++ [value]) after ⟶+
    marked path (n + 1) (gap + 2) before (value :: after) := by
  let l := ones n ++ (path.reverse ++ [true])
  let x := reverseRegisters after
  let box := registers (before ++ [value]) ++ false :: false :: x
  let tail := registers before ++ false :: false :: (ones (value + 1) ++ false :: x)
  calc
    _ ⟶+ atRight (Port.registerEntry dec r.val) (path.reverse ++ [true])
        (ones n ++ (zeros (gap + 3) ++ box)) := route.run _
    _ ⟶+ atRight Port.select (false :: l) (false :: (zeros (gap + 1) ++ box)) :=
      enter_selector dec r.val n r.isLt hn (path.reverse ++ [true]) _
    _ ⟶+ atLeft (Port.breakPort false) (false :: l)
        (false :: (zeros (gap + 1) ++ tail)) :=
      select (false :: l) gap before value x
    _ ⟶+ atLeft (Port.dispatch 0) l (true :: false :: (zeros (gap + 1) ++ tail)) :=
      left (show Row (Port.breakPort false) false true false (Port.dispatch 0) by decide +kernel) _ _
    _ ⟶+ _ := by
      have hShort : shortZeros 0 (ones n ++ path.reverse) = true := by
        rw [shortZeros_ones]
        exact route.short
      have h := dispatch_from (ones n ++ path.reverse) 0 (by decide) hShort
        (true :: false :: (zeros (gap + 1) ++ tail))
      simpa only [l, tail, x, marked, List.reverse_append, List.reverse_reverse,
        reverse_ones, List.append_assoc, List.cons_append, List.replicate_succ,
        repeat_slide, reverseRegisters_cons] using h

theorem select_passes {path : List Bool} {dec : Bool} {r : Fin 12}
    (route : RegisterRoute path dec r) (gap : Nat) (hGap : 2 ≤ gap)
    (pending : List Nat) (n : Nat) (hn : n + pending.length ≤ r.val + 1)
    (before after : List Nat) :
    marked path n (gap + pending.length) (before ++ pending.reverse) after ⟶*
      marked path (n + pending.length) gap before (pending.reverse ++ after) := by
  induction pending generalizing n after with
  | nil =>
    simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.append_nil, List.nil_append]
    exact Reach.refl _
  | cons value pending ih =>
    let g := gap + pending.length - 2
    have h0 : gap + (value :: pending).length = g + 3 := by
      simp only [List.length_cons]
      dsimp only [g]
      omega
    have h1 : g + 2 = gap + pending.length := by dsimp only [g]; omega
    have hr : n ≤ r.val := by simp only [List.length_cons] at hn; omega
    rw [h0, List.reverse_cons, ← List.append_assoc]
    have pass := select_cycle route n g hr (before ++ pending.reverse) after value
    rw [h1] at pass
    refine pass.reach.trans ?_
    have remaining := ih (n + 1) (by simp only [List.length_cons] at hn; omega) (value :: after)
    have hCount : n + 1 + pending.length = n + (pending.length + 1) := by omega
    simpa only [List.length_cons, hCount, List.append_assoc, List.singleton_append] using remaining

/-- Select the register with `r` blocks to its right. -/
theorem select_register {path : List Bool} {dec : Bool} {r : Fin 12}
    (route : RegisterRoute path dec r) (gap : Nat) (hGap : 2 ≤ gap)
    (before after : List Nat) (value : Nat) (hIndex : after.length = r.val) :
    frame path (gap + (r.val + 1)) (before ++ value :: after) ⟶*
      marked path (r.val + 1) gap before (value :: after) := by
  have hlen : (after.reverse ++ [value]).length = r.val + 1 := by simp [hIndex]
  have h := select_passes route gap hGap (after.reverse ++ [value]) 0 (by rw [hlen]; omega) before []
  simpa only [hlen, Nat.zero_add, List.reverse_append, List.reverse_singleton, List.reverse_reverse,
    List.singleton_append, List.append_nil, marked_initial] using h

end PalomarI3380.Engine
