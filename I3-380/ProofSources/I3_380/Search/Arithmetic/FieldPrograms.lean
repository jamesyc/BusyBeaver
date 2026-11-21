module
public import I3_380.Search.Arithmetic.CantorPrograms
public import I3_380.Search.Arithmetic.ProgramEquivalence
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ArithmeticMachine.SourceCantor

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem coded_pop {src dst : Register} (different : dst ≠ src) (notSrc : u ≠ src) (notDst : dst ≠ u)
    (s : Store M) (destinationZero : s dst = 0) (scratchZero : s u = 0) :
    (pop src dst).Runs .normal s.code
      ((s.set src (decodeRight (s src))).set dst (decodeLeft (s src))).code := by
  let a := decodeLeft (s src)
  let b := decodeRight (s src)
  let middle := ((s.set src 0).set dst a).set u b
  have split := coded_unpair notDst different notSrc s destinationZero scratchZero
  change (unpair dst u src).Runs .normal s.code middle.code at split
  have move := coded_move notSrc middle
  have inputCleared : middle src = 0 := by
    simp [middle,Store.set,Ne.symm notSrc,Ne.symm different]
  have scratch : middle u = b := Store.get_set .. 
  rw [inputCleared,scratch,zero_add] at move
  have result : (middle.set u 0).set src b = (s.set src b).set dst a := by
    funext r
    by_cases atSrc : r = src <;> by_cases atDst : r = dst <;> by_cases atScratch : r = u <;>
      simp [middle,Store.set,atSrc,atDst,atScratch,scratchZero,different,notSrc,notDst,
        Ne.symm different,Ne.symm notDst]
  rw [result] at move
  exact Program.Runs.rightExit split move rfl

theorem coded_read {dst : Register} (notPending : dst ≠ pl) (notToken : dst ≠ tok)
    (s : Store M) (tokenZero : s tok = 0) (scratchZero : s u = 0) :
    (read dst).Runs .normal s.code
      ((s.set pl (decodeRight (s pl))).set dst (s dst+decodeLeft (s pl))).code := by
  let a := decodeLeft (s pl)
  let b := decodeRight (s pl)
  let middle := (s.set pl b).set tok a
  have first := coded_pop (src := pl) (dst := tok) (by decide) (by decide) (by decide)
    s tokenZero scratchZero
  have last := coded_move (Ne.symm notToken) middle
  have preserved : middle dst = s dst := by simp [middle,Store.set,notPending,notToken]
  have token : middle tok = a := Store.get_set ..
  have restored : (middle.set tok 0).set dst (middle dst+middle tok) = (s.set pl b).set dst (s dst+a) := by
    rw [preserved,token]
    have clean : (s.set pl b).set tok 0 = s.set pl b := by
      rw [Store.set_comm _ (by decide : pl ≠ tok),← tokenZero,Store.set_same]
    simp only [middle,Store.set_set,clean]
  rw [restored] at last
  have grouped := Program.Runs.rightExit first last (out := .normal) rfl
  have associate := code_associate (M := M)
    (p := unpair tok u pl) (q := move u pl) (r := move tok dst) (by rfl) (by rfl) (by rfl)
  exact (associate .normal _ _).mp grouped

theorem coded_read_pair {dst : Register} (notPending : dst ≠ pl) (notToken : dst ≠ tok)
    (s : Store M) (tokenZero : s tok = 0) (scratchZero : s u = 0)
    (first last : M) (code : s pl = pairValue first last) :
    (read dst).Runs .normal s.code ((s.set pl last).set dst (s dst+first)).code := by
  simpa only [code,(decode_pairValue _ _).1,(decode_pairValue _ _).2] using
    coded_read notPending notToken s tokenZero scratchZero

end PalomarI3380.Compiler.Source
