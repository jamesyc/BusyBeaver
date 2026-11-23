module
public import I3_334.Search.SearchScan
public import I3_334Support.Search.Arithmetic.CantorPrograms
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (ifZero ifPositive whilePositive clear move inc
  coded_copy_with coded_unpair coded_move coded_clear coded_while coded_ifZero_positive
  coded_ifZero_zero coded_decrement_zero coded_decrement_positive)
open ArithmeticMachine.SourceCantor
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem coded_ifPositive_zero {r : Register} {body : Program} {s : Store M} (zero : s r = 0) :
    (ifPositive r body).Runs .normal s.code s.code :=
  Program.Runs.leftExit (coded_decrement_zero zero) rfl

theorem coded_ifPositive_pos_normal {r : Register} {body : Program} {s : Store M} {t : M}
    (positive : s r ≠ 0) (run : body.Runs .normal (s.set r (s r-1)).code t) :
    (ifPositive r body).Runs .normal s.code t :=
  Program.Runs.rightExit (coded_decrement_positive positive) run rfl

theorem coded_copy {a b : Register} (different : a ≠ b) (source : a ≠ u) (target : b ≠ u)
    (s : Store M) (free : s u = 0) :
    (copy a b).Runs .normal s.code (s.set b (s b+s a)).code :=
  coded_copy_with different source target s free

theorem coded_pop {src dst : Register} (different : dst ≠ src) (notSrc : u ≠ src) (notDst : dst ≠ u)
    (s : Store M) (destinationZero : s dst = 0) (scratchZero : s u = 0) :
    (pop src dst).Runs .normal s.code
      ((s.set src (decodeRight (s src))).set dst (decodeLeft (s src))).code := by
  let a := decodeLeft (s src)
  let b := decodeRight (s src)
  let middle := ((s.set src 0).set dst a).set u b
  have split := coded_unpair notDst different notSrc s destinationZero scratchZero
  change (Source.unpair dst u src).Runs .normal s.code middle.code at split
  have transfer := coded_move notSrc middle
  have inputCleared : middle src = 0 := by
    simp [middle,Store.set,Ne.symm notSrc,Ne.symm different]
  have scratch : middle u = b := Store.get_set .. 
  rw [inputCleared,scratch,zero_add] at transfer
  have result : (middle.set u 0).set src b = (s.set src b).set dst a := by
    funext r
    by_cases atSrc : r = src <;> by_cases atDst : r = dst <;> by_cases atScratch : r = u <;>
      simp [middle,Store.set,atSrc,atDst,atScratch,scratchZero,different,notSrc,notDst,
        Ne.symm different,Ne.symm notDst]
  rw [result] at transfer
  exact Program.Runs.rightExit split transfer rfl

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
  exact Program.Runs.rightExit first last rfl

/-- A model-finite unary comparison. The marker is cleared as soon as
the token counter crosses the available expected field. -/
theorem coded_compare_prefix (s : Store M) :
    (whilePositive tok (ifZero expected (clear gues))).Runs .normal s.code
      (((s.set tok 0).set expected (s expected-s tok)).set gues
        (if s expected<s tok then 0 else s gues)).code := by
  let states := fun i : M =>
    (((s.set tok (s tok-i)).set expected (s expected-i)).set gues
      (if s expected < i then 0 else s gues))
  have markerDefinition : 𝚺ᴬ₁-Function₁ (fun (i : M) => if s expected < i then (0 : M) else s gues) := by
    change 𝚺ᴬ₁.Definable (fun v : Fin 2 → M => v 0 = if s expected < v 1 then (0 : M) else s gues)
    have eq : (fun v : Fin 2 → M => v 0 = if s expected < v 1 then (0 : M) else s gues) =
        (fun v => (s expected < v 1 ∧ v 0 = (0 : M)) ∨ (¬ s expected < v 1 ∧ v 0 = s gues)) := by
      funext v
      by_cases deficit : s expected < v 1 <;> simp [deficit]
    rw [eq]
    definability
  have graph : 𝚺ᴬ₁-Function₁ (fun i => (states i).code) := by
    apply matrixToVec_definable₁
    intro r
    by_cases mark : r = gues
    · simpa only [states,Store.set,mark,↓reduceIte] using markerDefinition
    · by_cases token : r = tok <;> by_cases expectedField : r = expected <;>
        simp only [states,Store.set,token,expectedField,mark,↓reduceIte] <;> definability
  have tokAt (i : M) : states i tok = s tok-i := by simp [states,Store.set,tok,expected,gues]
  have expAt (i : M) : states i expected = s expected-i := by simp [states,Store.set,expected,tok,gues]
  have guessAt (i : M) : states i gues = if s expected<i then 0 else s gues :=
    Store.get_set .. 
  have base : states 0 = s := by simp [states,Store.set_same]
  have done : states (s tok) tok = 0 := by rw [tokAt,Arithmetic.sub_self]
  have advances (i : M) (earlier : i < s tok) :
      states i tok ≠ 0 ∧ (ifZero expected (clear gues)).Runs .normal
        ((states i).set tok (states i tok-1)).code (states (i+1)).code := by
    let middle := (states i).set tok (states i tok-1)
    have token : states i tok ≠ 0 := by
      rw [tokAt]
      exact (Arithmetic.pos_sub_iff_lt.mpr earlier).ne'
    refine ⟨token,?_⟩
    have needed : middle expected = s expected-i := by
      unfold middle
      rw [Store.get_set_other _ _ _ _ (by decide : expected ≠ tok),expAt]
    by_cases enough : i < s expected
    · have positive : middle expected ≠ 0 := by
        rw [needed]
        exact (Arithmetic.pos_sub_iff_lt.mpr enough).ne'
      have first := coded_ifZero_positive (body := clear gues) (s := middle) (r := expected) positive
      have before : ¬ s expected<i := not_lt_of_ge (le_of_lt enough)
      have fits : i+1 ≤ s expected := (lt_iff_succ_le.mp enough)
      have next : middle.set expected (middle expected-1) = states (i+1) := by
        rw [needed]
        unfold middle
        rw [tokAt]
        funext r
        by_cases mark : r = gues <;> by_cases tok' : r = tok <;> by_cases exp' : r = expected <;>
          simp [states,Store.set,mark,tok',exp',tok,expected,gues,before,not_lt_of_ge fits,Arithmetic.sub_sub]
      rw [next] at first
      exact first
    · have short : s expected ≤ i := le_of_not_gt enough
      have empty : middle expected = 0 := by rw [needed,Arithmetic.sub_spec_of_le short]
      have clear := coded_clear gues middle
      have run := coded_ifZero_zero empty clear (out := .normal) rfl
      have missing : s expected < i+1 := lt_of_le_of_lt short (lt_add_one i)
      have noExpected : s expected-(i+1) = 0 := Arithmetic.sub_spec_of_lt missing
      have next : middle.set gues 0 = states (i+1) := by
        unfold middle
        rw [tokAt]
        funext r
        by_cases mark : r = gues <;> by_cases tok' : r = tok <;> by_cases exp' : r = expected <;>
          simp [states,Store.set,mark,tok',exp',tok,expected,gues,missing,noExpected,
            Arithmetic.sub_spec_of_le short,Arithmetic.sub_sub]
      rw [next] at run
      exact run
  have proof := coded_while tok (ifZero expected (clear gues)) states (s tok) graph done advances
  simpa only [base,states,Arithmetic.sub_self] using proof

theorem coded_compare (s : Store M) :
    compare.Runs .normal s.code
      (((s.set tok 0).set expected 0).set gues (if s expected=s tok then s gues else 0)).code := by
  let mid := (((s.set tok 0).set expected (s expected-s tok)).set gues
    (if s expected<s tok then 0 else s gues))
  have first := coded_compare_prefix s
  have quantity : mid expected = s expected-s tok := by simp [mid,Store.set,expected,gues]
  by_cases fits : s expected ≤ s tok
  · have zero : mid expected = 0 := by rw [quantity,Arithmetic.sub_spec_of_le fits]
    have stop := coded_ifPositive_zero (body := .seq (clear expected) (clear gues)) zero
    have last : mid = (((s.set tok 0).set expected 0).set gues
        (if s expected=s tok then s gues else 0)) := by
      unfold mid
      rw [Arithmetic.sub_spec_of_le fits]
      rcases lt_or_eq_of_le fits with lt | eq
      · simp [lt,lt.ne]
      · simp [eq]
    rw [← last]
    exact Program.Runs.rightExit first stop rfl
  · have greater : s tok<s expected := lt_of_not_ge fits
    have positive : mid expected ≠ 0 := by rw [quantity]; exact (Arithmetic.pos_sub_iff_lt.mpr greater).ne'
    let shifted := mid.set expected (mid expected - 1)
    have clear : (.seq (clear expected) (clear gues) : Program).Runs .normal shifted.code
        ((shifted.set expected 0).set gues 0).code :=
      Program.Runs.rightExit (coded_clear expected shifted) (coded_clear gues (shifted.set expected 0)) rfl
    have last := coded_ifPositive_pos_normal positive clear
    have result : ((shifted.set expected 0).set gues 0) =
        (((s.set tok 0).set expected 0).set gues (if s expected=s tok then s gues else 0)) := by
      simp only [shifted,mid,Store.set_set,greater.ne',↓reduceIte]
      funext r
      by_cases a : r = tok <;> by_cases b : r = expected <;> by_cases c : r = gues <;>
        simp [Store.set,a,b,c,tok,expected,gues]
    rw [result] at last
    exact Program.Runs.rightExit first last rfl

theorem coded_eat (s : Store M) (freeTok : s tok = 0) (freeAux : s u = 0) :
    eat.Runs .normal s.code
      (((s.set fr (decodeRight (s fr))).set expected 0).set gues
        (if s expected = decodeLeft (s fr) then s gues else 0)).code := by
  let a := decodeLeft (s fr)
  let b := decodeRight (s fr)
  let middle := (s.set fr b).set tok a
  have first := coded_pop (src := fr) (dst := tok) (by decide) (by decide) (by decide)
    s freeTok freeAux
  have last := coded_compare middle
  have result : (((middle.set tok 0).set expected 0).set gues (if middle expected=middle tok then middle gues else 0)) =
      (((s.set fr b).set expected 0).set gues (if s expected=a then s gues else 0)) := by
    funext r
    by_cases x : r = expected <;> by_cases y : r = tok <;> by_cases z : r = gues <;>
      by_cases w : r = fr <;> simp [middle,Store.set,x,y,z,w,freeTok,tok,expected,gues,fr]
  rw [result] at last
  exact Program.Runs.rightExit first last rfl

end PalomarI3334.SearchProgram
