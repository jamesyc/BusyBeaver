module
public import I3_334.Simulation.DecoderWalk
public import I3_334Support.Machine.DecoderWindow
@[expose] public section

namespace PalomarI3334.LiteralDecoder

open PalomarI3380
open Decoder (height transition)
open DecoderWindow

/-- Packed map from reference states directly to literal states.
The row checks below verify the resulting transition simulation. -/
def referenceToLiteral : Nat := 0x14ea6d32974aa4d228f46a2d128742a0d027e979f4f6793b9d4e671379b4d66933994c6612f96b8655299248e3b019745a2b2c944ae0d0c83c9e31267d3e64b227dc8640ee8f471df1b8d4622f0f88c5227128fc38950d8242e15098446606ec75c0a03007fbf9fafc883e1bede7bbd9eaf479bc9e2f082bb5a4ea74ba1cee672b91c6e270b813ac561b4dbadc6db69b2d86bb59aad459b4d92d16833d9ccd6627d96ca37b218ec662b10e0bc6130580bf48af97abb5d2e570b75b2d55ab4592c560af43ab9587b55aa952a853a9948a351284eca03ea793a9c4da6932984ba592a9449a48e29047a391a8c45a29128832218b0854220d047e40a00fe7a3c9e0ee723b1d4e873371b4d86b351a4f86833998ca5431184c05f2f174ae5c2d968b2582b958aa4229948a250279389a4c259289248239188a44218c882401f8f87a3c1d8e872381b8d86a3419d386230178b85a2c158a85228138984a241188842200f8783a1c0d86832180b8582a14098482210078381a0c058281208038180a04018080200

def image (q : Nat) : Nat := (referenceToLiteral >>> (9*q)) % 512

def translateWindow (w : DecoderWindow) : DecoderWindow :=
  { w with config := { w.config with state := image w.config.state } }

/-- The terminal owner needs the first zero of the clean frame's gap.
The two donor exits also erase part of the continue word before joining. -/
def special (q : Nat) (bit : Bool) : Bool :=
  bit && (q == 48 || q == 74 || q == 210)

/-- Visit the decoder states together with the three bits to the left
of the head. The mask records visited windows. -/
def visitWindows : Nat → List (Nat × Nat) → Nat → Nat
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, (q, left) :: pending, seen =>
    let index := 8 * q + left
    if height q == 0 || ((seen >>> index) % 2 == 1) then
      visitWindows fuel pending seen
    else
      let next := fun bit : Bool => ((transition q bit).target, (2 * left + bit.toNat) % 8)
      visitWindows fuel (next false :: next true :: pending) (seen ||| (1 <<< index))

-- Each of the 344 × 8 windows can schedule at most two successors.
-- The row check independently verifies closure under the live edges.
def leftMasks : Nat := visitWindows (1 + 2 * 344 * 8) [(Control.root, 1)] 0

def leftWindow (q left : Nat) : Bool :=
  ((leftMasks >>> (8 * q + left)) % 2) == 1

def input (q left : Nat) (bit : Bool) : DecoderWindow :=
  ⟨⟨q, left % 2, bit.toNat⟩, 1, 1⟩

def verifies (src dst : DecoderWindow) (fuel : Nat) : Bool :=
  match runToMatch machine (translateWindow dst) fuel (translateWindow src) with
  | some n => decide (0 < n)
  | none => false

def checkStep (src : DecoderWindow) : Bool :=
  match next decoderReference src with
  | none => false
  | some dst => verifies src dst 3

def ordinaryCheck (q left : Nat) (bit : Bool) : Bool :=
  checkStep (input q left bit)

/-- The only extra condition is a zero immediately after the final
read-1 bit of the pure continue word. -/
def continueWordCheck (left : Nat) : Bool :=
  checkStep ⟨⟨48,left % 2,1⟩,1,2⟩

def donorWidth (left : Nat) : Nat := if left % 4 = 3 then 2 else 3

def donorSteps (left : Nat) : Nat := donorWidth left + 1

/-- A donor exit joins the reference after the first surviving one to
its left has reset the dispatcher. Neither trace reads farther left. -/
-- The high bit of the left window is the cell immediately before the
-- surviving one. Its value is preserved as the new read cell.
def donorInput (q left : Nat) (previous : Bool) : DecoderWindow :=
  ⟨⟨q,left % 2 ^ donorWidth left + (2 ^ donorWidth left) * previous.toNat,1⟩,
    donorWidth left + 1,2⟩

def donorExit (left : Nat) (previous : Bool) : DecoderWindow :=
  ⟨⟨9,0,previous.toNat + 2⟩,0,donorWidth left + 3⟩

def donorCheck (q left : Nat) : Bool :=
  (left % 4 == 3 || left % 8 == 5) &&
    [false,true].all fun previous =>
      let src := donorInput q left previous
      let dst := donorExit left previous
      (runToMatch decoderReference dst (donorSteps left) src == some (donorSteps left)) &&
        verifies src dst 6

def checkArm (q left : Nat) (bit : Bool) : Bool :=
  let target := (transition q bit).target
  (if 0 < height target then leftWindow target ((2*left+bit.toNat)%8) else true) &&
    if special q bit then
      if q == 48 then continueWordCheck left else donorCheck q left
    else ordinaryCheck q left bit

def checkRows : Bool :=
  (List.range 344).all fun q =>
    if 0 < height q then
      (List.range 8).all fun left =>
        if leftWindow q left then checkArm q left false && checkArm q left true else true
    else true

set_option maxRecDepth 16384 in
set_option maxHeartbeats 18000000 in
theorem checkedRows : checkRows = true := by decide +kernel

theorem checked_arm (q : Fin 344) (left : Fin 8) (bit : Bool)
    (live : 0 < height q.val) (known : leftWindow q.val left.val = true) :
    checkArm q.val left.val bit = true := by
  have state := List.all_eq_true.mp checkedRows q.val (List.mem_range.mpr q.isLt)
  have shape := List.all_eq_true.mp (by simpa only [live, ↓reduceIte] using state)
    left.val (List.mem_range.mpr left.isLt)
  simp only [known, ↓reduceIte, Bool.and_eq_true] at shape
  cases bit
  · exact shape.1
  · exact shape.2

theorem root_left : leftWindow Control.root 1 = true := by decide +kernel

theorem root_image : image Control.root = Control.root := by decide +kernel

theorem entry_image (dec : Bool) (rank : Fin 11) :
    image (Decoder.registerPort dec rank.val) < 334 := by
  revert dec rank
  decide +kernel

-- Clients use the checked transition and closure lemmas. Keep the
-- finite traversal out of routine unification.
attribute [irreducible] leftWindow

end PalomarI3334.LiteralDecoder
