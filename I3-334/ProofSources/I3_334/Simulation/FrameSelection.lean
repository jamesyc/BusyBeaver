module
public import I3_334.Tape.SelectRegister
public import I3_334.Tape.Progress
public import I3_334.Simulation.DecoderWalk
public import I3_334Support.Engine.Arithmetic.StandardTape
@[expose] public section

namespace PalomarI3334.Stock

open PalomarI3380 PalomarI3380.ArithmeticMachine
open PalomarI3380.ArithmeticMachine.Reference (cell registers reverseRegisters)
open Control (root boundedZeros dispatch)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def frame (path : List Bool) (gap : M) (values : List M) : M :=
  cell root 1 (packWord path (repeatBit false gap (registers values 0)))

noncomputable def marked (path : List Bool) (count : Nat) (gap : M)
    (before after : List M) : M :=
  cell root 1 (packWord path (repeatBit true (count : M)
    (repeatBit false gap (registers before (pushBit false (pushBit false (reverseRegisters after 0)))))))

theorem marked_initial (path : List Bool) (gap : M) (rs : List M) :
    marked path 0 gap rs [] = frame path gap rs := by
  simp only [marked, frame, Nat.cast_zero, repeatBit_zero, reverseRegisters, pushBit_false_zero]

structure EntryRows (m : Machine) (entry : Bool → Nat → Nat) : Prop where
  choose : ∀ (dec : Bool) (r : Fin 11), Row m (entry dec r.val) false false true 31
  advance : ∀ (dec : Bool) (r : Fin 10), Row m (entry dec (r.val+1)) true true true (entry dec r.val)
  operate : ∀ dec : Bool, Row m (entry dec 0) true true true (if dec then 47 else 50)

theorem referenceEntries : EntryRows decoderReference Decoder.registerPort := by
  constructor <;> decide +kernel

abbrev operationPort (dec : Bool) : Nat := if dec then 47 else 50

structure RegisterRoute (m : Machine) (entry : Bool → Nat → Nat) (path : List Bool)
    (dec : Bool) (r : Fin 11) : Prop where
  short : boundedZeros 0 path.reverse = true
  run : ∀ {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (tail : M),
    Progress m (cell root 1 (packWord path tail)) (cell (entry dec r.val) (packWord path.reverse 1) tail)

theorem decoded_register_route {input : List Bool} {d : Decoder.Result}
    (found : Decoder.Decodes root [] input d) {dec : Bool} {r : Fin 11}
    (instruction : d.command = .register dec r) :
    RegisterRoute decoderReference Decoder.registerPort d.path dec r := by
  have path : found.scanned = d.path := found.path
  have shape := found.leaf
  have target := found.target
  rw [instruction] at shape target
  rcases shape with ⟨write, right, valid⟩
  refine ⟨?_, ?_⟩
  · simpa only [Decoder.Result.path, List.reverse_append, List.reverse_singleton,
      List.reverse_reverse, List.singleton_append] using valid
  · intro V _ _ tail
    have run := found.run (1 : V) tail
    change (Decoder.transition d.node d.read).target = Decoder.registerPort dec r.val at target
    have reach :
        Reaches decoderReference (cell root 1 (packWord d.path tail))
          (cell (Decoder.registerPort dec r.val) (packWord d.path.reverse 1) tail) := by
      simpa only [path, Decoder.Result.destination, write, right, ↓reduceIte, target,
        Decoder.Result.path, List.reverse_append, List.reverse_singleton, List.reverse_reverse,
        List.singleton_append, packWord_nil, packWord_cons] using run
    apply progress_of_ne reach
    intro same
    have state := congrArg (fun x : V => π₁ x) same
    simp only [cell, encode, Arithmetic.pi₁_pair, nat_cast_inj] at state
    exact (Decoder.Exit.port_ne_root (.register dec r)) state.symm

variable {m : Machine} {entry : Bool → Nat → Nat}

theorem enterSelector (rows : EntryRows m entry) (dec : Bool) (r n : Nat) (hr : r < 11)
    (hn : n ≤ r) (l x : M) :
    Reaches m (cell (entry dec r) l (repeatBit true (n : M) (pushBit false x)))
      (cell 31 (pushBit false (repeatBit true (n : M) l)) x) := by
  induction n generalizing r l with
  | zero => simpa only [Nat.cast_zero, repeatBit_zero] using right (rows.choose dec ⟨r,hr⟩) l x
  | succ n ih =>
    cases r with
    | zero => omega
    | succ r =>
      have move := right (rows.advance dec ⟨r, by omega⟩) l
        (repeatBit true (n : M) (pushBit false x))
      have rest := ih r (by omega) (by omega) (pushBit true l)
      simpa only [Nat.cast_succ, repeatBit_succ, repeatBit_push] using move.trans rest

theorem enterOperation (rows : EntryRows m entry) (dec : Bool) (r : Nat) (hr : r < 11)
    (l x : M) :
    Reaches m (cell (entry dec r) l (repeatBit true ((r : M)+1) x))
      (cell (operationPort dec) (repeatBit true ((r : M)+1) l) x) := by
  induction r generalizing l with
  | zero => simpa only [Nat.cast_zero, zero_add, repeatBit_one] using right (rows.operate dec) l x
  | succ r ih =>
    have move := right (rows.advance dec ⟨r, by omega⟩) l (repeatBit true ((r : M)+1) x)
    have rest := ih (by omega) (pushBit true l)
    simpa only [Nat.cast_succ, repeatBit_succ, repeatBit_push] using move.trans rest

/-- One selector pass changes the marked boundary while preserving
all register values. The gap and each register are model-valued. -/
theorem selectCycle {path : List Bool} {dec : Bool} {r : Fin 11}
    {last back : Nat} (control : Control.Rows m) (entries : EntryRows m entry)
    (selector : SelectorRows m last back) (route : RegisterRoute m entry path dec r) (n : Nat) (gap : M) (hn : n ≤ r.val)
    (before after : List M) (value : M) :
    Progress m (marked path n (gap+3) (before++[value]) after)
      (marked path (n+1) (gap+2) before (value::after)) := by
  let l := repeatBit true (n : M) (packWord path.reverse 1)
  let suffix := reverseRegisters after 0
  let box := registers (before++[value]) (pushBit false (pushBit false suffix))
  let moved := registers before (pushBit false (pushBit false
    (repeatBit true (value+1) (pushBit false suffix))))
  have start := route.run (repeatBit true (n : M) (repeatBit false (gap+3) box))
  have enter := enterSelector entries dec r.val n r.isLt hn (packWord path.reverse 1) (repeatBit false (gap+2) box)
  have splitGap : gap+3 = (gap+2)+1 := by
    have three : (3 : M) = 2+1 := by exact_mod_cast (show (3 : Nat) = 2+1 from rfl)
    rw [add_assoc,three]
  have gapTwo : gap+2 = (gap+1)+1 := by rw [add_assoc,one_add_one_eq_two]
  rw [splitGap,repeatBit_succ,gapTwo,repeatBit_succ] at start
  rw [gapTwo,repeatBit_succ] at enter
  have select := selectRegister selector (pushBit false l) gap before value suffix
  have next := left control.breakZero
    l (pushBit false (repeatBit false (gap+1) moved))
  rw [fromLeft_pushBit] at select
  have short : boundedZeros 0 (Engine.ones n ++ path.reverse) = true := by
    rw [Control.boundedZeros_ones]
    exact route.short
  have back := Control.dispatchFrom control (Engine.ones n ++ path.reverse) 0 (by decide) short
    (pushBit true (pushBit false (repeatBit false (gap+1) moved)))
  rw [packWord_append,← repeatBit_cast] at back
  have pass := start.trans (enter.trans (select.trans (next.trans back)))
  rw [List.reverse_append,List.reverse_reverse,Engine.reverse_ones,packWord_append,← repeatBit_cast] at pass
  have repeatOne : repeatBit true (n : M)
      (pushBit true (pushBit false (repeatBit false (gap+1) moved))) =
    repeatBit true ((n : M)+1) (repeatBit false (gap+2) moved) := by
    simp only [repeatBit_push,repeatBit_succ,gapTwo]
  rw [repeatOne] at pass
  unfold marked
  rw [Nat.cast_succ,splitGap,repeatBit_succ,gapTwo,repeatBit_succ]
  simpa only [gapTwo,repeatBit_succ,reverseRegisters,moved] using pass

theorem selectPasses {path : List Bool} {dec : Bool} {r : Fin 11}
    {last back : Nat} (control : Control.Rows m) (entries : EntryRows m entry)
    (selector : SelectorRows m last back) (route : RegisterRoute m entry path dec r) (gap : M)
    (pending : List M) (n : Nat) (bound : n + pending.length ≤ r.val+1)
    (before after : List M) :
    let first := marked path n (gap+2+(pending.length : M)) (before++pending.reverse) after
    let last := marked path (n+pending.length) (gap+2) before (pending.reverse++after)
    Reaches m first last ∧ (pending ≠ [] → Progress m first last) := by
  induction pending generalizing n after with
  | nil =>
    exact ⟨by simpa using Reaches.refl m (marked path n (gap+2) before after),
      fun impossible => (impossible rfl).elim⟩
  | cons value pending ih =>
    let g := gap + (pending.length : M)
    have atThree : gap+2+((value::pending).length : M) = g+3 := by
      simp only [List.length_cons,Nat.cast_succ,g]
      have three : (3 : M) = 2+1 := by exact_mod_cast (show (3 : Nat) = 2+1 from rfl)
      rw [three]
      ac_rfl
    have atTwo : g+2 = gap+2+(pending.length : M) := by dsimp [g]; ac_rfl
    have remains : n+1+pending.length ≤ r.val+1 := by simp only [List.length_cons] at bound; omega
    dsimp only
    rw [atThree,List.reverse_cons,← List.append_assoc]
    have pick := selectCycle control entries selector route n g (by omega) (before++pending.reverse) after value
    rw [atTwo] at pick
    have rest := ih (n+1) remains (value::after)
    have pass := pick.trans (by
      simpa only [List.length_cons,show n+1+pending.length = n+(pending.length+1) by omega,
        List.append_assoc,List.singleton_append] using rest.1)
    rw [List.append_assoc pending.reverse [value] after, List.singleton_append]
    simpa only [List.length_cons] using
      And.intro pass.reach (fun (_ : value :: pending ≠ []) => pass)

theorem selectFrame {path : List Bool} {dec : Bool} {r : Fin 11}
    {last back : Nat} (control : Control.Rows m) (entries : EntryRows m entry)
    (selector : SelectorRows m last back) (route : RegisterRoute m entry path dec r) (gap : M) (before after : List M) (value : M)
    (index : after.length = r.val) :
    Progress m (frame path (gap+2+((r.val+1 : Nat) : M)) (before++value::after))
      (marked path (r.val+1) (gap+2) before (value::after)) := by
  have len : (after.reverse++[value]).length = r.val+1 := by simp [index]
  have run := selectPasses control entries selector route gap (after.reverse++[value]) 0 (by rw [len,Nat.zero_add]) before []
  simpa only [len,Nat.zero_add,List.reverse_append,List.reverse_singleton,List.reverse_reverse,
    List.singleton_append,List.append_nil,marked_initial] using run.2 (by simp)

end PalomarI3334.Stock
