module
public import I3_380.Search.Arithmetic.FieldPrograms
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem exp_ne_tok : «exp» ≠ tok := by decide
private theorem exp_ne_marker : «exp» ≠ gues := by decide
private theorem tok_ne_marker : tok ≠ gues := by decide

theorem coded_compare_heads (s : Store M) :
    (compareHeads).Runs .normal s.code
      (((s.set «exp» 0).set tok (s tok-s «exp»)).set gues (if s tok<s «exp» then 0 else s gues)).code := by
  let states := fun i : M => (s.set «exp» (s «exp»-i)).set tok (s tok-i)
  let count := min (s «exp») (s tok)
  let body := ifZero tok mismatch
  have graph : 𝚺ᴬ₁-Function₁ (fun i => (states i).code) := by
    apply matrixToVec_definable₁
    intro r
    by_cases toToken : r = tok
    · simp only [states,Store.set,toToken,↓reduceIte]
      definability
    · by_cases toExpected : r = «exp» <;>
        simp only [states,Store.set,toToken,toExpected,↓reduceIte] <;> definability
  have expAt (i : M) : states i «exp» = s «exp»-i := by simp [states,Store.set,exp_ne_tok]
  have tokAt (i : M) : states i tok = s tok-i := by simp [states]
  have base : states 0 = s := by simp [states,Store.set_same]
  have runPrefix : ∀ i < count, states i «exp» ≠ 0 ∧
      body.Runs .normal ((states i).set «exp» (states i «exp»-1)).code (states (i+1)).code := by
    intro i earlier
    have seeExp : 0 < s «exp»-i := Arithmetic.pos_sub_iff_lt.mpr (lt_of_lt_of_le earlier (min_le_left ..))
    have seeTok : 0 < s tok-i := Arithmetic.pos_sub_iff_lt.mpr (lt_of_lt_of_le earlier (min_le_right ..))
    let mid := (states i).set «exp» (states i «exp»-1)
    have token : mid tok = s tok-i :=
      (Store.get_set_other _ _ _ _ (Ne.symm exp_ne_tok)).trans (tokAt i)
    have step := coded_ifZero_positive (body := mismatch) (s := mid) (r := tok)
      (token.symm ▸ seeTok.ne')
    have next : mid.set tok (mid tok-1) = states (i+1) := by
      rw [token]
      unfold mid
      rw [expAt]
      funext r
      by_cases atExp : r = «exp» <;> by_cases atTok : r = tok <;>
        simp [states,Store.set,atExp,atTok,Arithmetic.sub_sub]
    exact ⟨by simpa only [expAt] using seeExp.ne',by simpa only [body,next] using step⟩
  have extend (final : M) := coded_while_prefix «exp» body states count graph runPrefix (final := final)
  by_cases fits : s «exp» ≤ s tok
  · have countEq : count = s «exp» := min_eq_left fits
    have done : states count «exp» = 0 := by rw [countEq,expAt,Arithmetic.sub_self]
    have exit := coded_while_done «exp» body (states count) done
    have result := extend _ exit
    let last := (s.set «exp» 0).set tok (s tok-s «exp»)
    have marker : last gues = s gues := by simp [last,Store.set,Ne.symm exp_ne_marker,Ne.symm tok_ne_marker]
    have kept : last.set gues (s gues) = last := by rw [← marker,Store.set_same]
    have finish : states count = last := by simp [states,countEq,last]
    rw [ite_eq_right (not_lt_of_ge fits)]
    change compareHeads.Runs .normal s.code (last.set gues (s gues)).code
    rw [kept]
    simpa only [base,finish,compareHeads,body] using result
  · have less : s tok < s «exp» := lt_of_not_ge fits
    have countEq : count = s tok := min_eq_right (le_of_lt less)
    have still : states count «exp» ≠ 0 := by
      rw [expAt,countEq]
      exact (Arithmetic.pos_sub_iff_lt.mpr less).ne'
    let dec := (states count).set «exp» (states count «exp»-1)
    let last := (dec.set gues 0).set «exp» 0
    have token : dec tok = 0 := by
      unfold dec
      rw [Store.get_set_other _ _ _ _ (Ne.symm exp_ne_tok),tokAt,countEq,Arithmetic.sub_self]
    have clearBoth : mismatch.Runs .normal dec.code last.code :=
      Program.Runs.rightExit (coded_clear gues dec) (coded_clear «exp» (dec.set gues 0)) rfl
    have finish : last «exp» = 0 := Store.get_set ..
    have tail := coded_while_more still (coded_ifZero_zero token clearBoth rfl)
      (coded_while_done «exp» body last finish)
    have result := extend _ tail
    have same : last = ((s.set «exp» 0).set tok (s tok-s «exp»)).set gues 0 := by
      have zeroTok : s tok-s «exp» = 0 := Arithmetic.sub_spec_of_lt less
      funext r
      by_cases atExp : r = «exp» <;> by_cases atTok : r = tok <;> by_cases atMark : r = gues <;>
        simp [last,dec,states,Store.set,countEq,zeroTok,atExp,atTok,atMark,
          exp_ne_tok,Ne.symm exp_ne_tok,exp_ne_marker,Ne.symm exp_ne_marker,
          tok_ne_marker,Ne.symm tok_ne_marker]
    simpa only [base,same,less,↓reduceIte,compareHeads,body] using result

theorem coded_compare_tail (s : Store M) :
    (whilePositive tok (clear gues)).Runs .normal s.code
      ((s.set tok 0).set gues (if s tok=0 then s gues else 0)).code := by
  by_cases zero : s tok = 0
  · have unchanged : s.set tok 0 = s := by rw [← zero,Store.set_same]
    rw [ite_eq_left zero,unchanged,Store.set_same]
    exact coded_while_done tok (clear gues) s zero
  · let mid := (s.set tok (s tok-1)).set gues 0
    let states := fun i : M => (mid.set tok (mid tok-i))
    have graph : 𝚺ᴬ₁-Function₁ (fun i => (states i).code) := by
      have update := Store.writeCode_definable (M := M) tok
      have eq (x : M) : (states x).code = Store.writeCode tok mid.code (mid tok-x) := by
        simp [states,Store.writeCode]
      simp only [eq]
      definability
    have done : states (mid tok) tok = 0 := by simp [states]
    have base : states 0 = mid := by simp [states,Store.set_same]
    have finish : states (mid tok) = (mid.set tok 0) := by simp [states]
    have tail := coded_while tok (clear gues) states (mid tok) graph done
    have rest : (whilePositive tok (clear gues)).Runs .normal mid.code (mid.set tok 0).code := by
      suffices steps : _ by
        simpa only [base,finish] using tail steps
      intro i earlier
      have positive : 0 < mid tok-i := Arithmetic.pos_sub_iff_lt.mpr earlier
      refine ⟨by simpa only [states,Store.get_set] using positive.ne',?_⟩
      have next : (states i).set tok (states i tok-1) = states (i+1) := by
        simp [states,Store.set_set,Arithmetic.sub_sub]
      have marker : states (i+1) gues = 0 := by
        simp [states,mid,Store.set,Ne.symm tok_ne_marker]
      have keep : (states (i+1)).set gues 0 = states (i+1) := by rw [← marker,Store.set_same]
      rw [next]
      simpa only [keep] using coded_clear gues (states (i+1))
    have run := coded_while_more zero (coded_clear gues (s.set tok (s tok-1))) rest
    have final : mid.set tok 0 = (s.set tok 0).set gues 0 := by
      unfold mid
      rw [Store.set_comm _ (Ne.symm tok_ne_marker),Store.set_set]
    simpa only [final,zero,↓reduceIte] using run

/-- Counter equality, preserving the candidate marker precisely when
the two fields match. Both counters are cleared. -/
theorem coded_compare (s : Store M) :
    compare.Runs .normal s.code
      (((s.set «exp» 0).set tok 0).set gues (if s «exp»=s tok then s gues else 0)).code := by
  let marker := if s tok<s «exp» then 0 else s gues
  let middle := ((s.set «exp» 0).set tok (s tok-s «exp»)).set gues marker
  have first := coded_compare_heads s
  have last := coded_compare_tail middle
  have t : middle tok = s tok-s «exp» := by simp [middle,Store.set,tok_ne_marker]
  have g : middle gues = marker := Store.get_set ..
  have result : (if middle tok=0 then middle gues else 0) = if s «exp»=s tok then s gues else 0 := by
    simp only [t,g,Arithmetic.sub_eq_zero_iff_le]
    by_cases equal : s «exp»=s tok
    · simp [equal,marker]
    · rcases lt_or_gt_of_ne equal with lt | gt
      · simp [marker,equal,not_le_of_gt lt]
      · simp [marker,equal,le_of_lt gt,gt]
  rw [result] at last
  have clean : (middle.set tok 0).set gues (if s «exp»=s tok then s gues else 0) =
      ((s.set «exp» 0).set tok 0).set gues (if s «exp»=s tok then s gues else 0) := by
    funext r
    by_cases token : r=tok <;> by_cases mark : r=gues <;> simp [middle,Store.set,token,mark]
  rw [clean] at last
  exact Program.Runs.rightExit first last rfl

theorem coded_eat (s : Store M) (tokenZero : s tok = 0) (scratchZero : s u = 0) :
    eat.Runs .normal s.code
      (((s.set fr (ArithmeticMachine.SourceCantor.decodeRight (s fr))).set «exp» 0).set gues
        (if s «exp» = ArithmeticMachine.SourceCantor.decodeLeft (s fr) then s gues else 0)).code := by
  let a := ArithmeticMachine.SourceCantor.decodeLeft (s fr)
  let b := ArithmeticMachine.SourceCantor.decodeRight (s fr)
  let middle := (s.set fr b).set tok a
  have first := coded_pop (src := fr) (dst := tok) (by decide) (by decide) (by decide)
    s tokenZero scratchZero
  have last := coded_compare middle
  have expected : middle «exp» = s «exp» := by
    simp [middle,Store.set,exp_ne_tok,show «exp» ≠ fr by decide]
  have token : middle tok = a := Store.get_set ..
  have marker : middle gues = s gues := by
    simp [middle,Store.set,Ne.symm tok_ne_marker,show gues ≠ fr by decide]
  rw [expected,token,marker] at last
  have same : ((middle.set «exp» 0).set tok 0).set gues (if s «exp» = a then s gues else 0) =
      ((s.set fr b).set «exp» 0).set gues (if s «exp» = a then s gues else 0) := by
    funext r
    by_cases expect : r = «exp» <;> by_cases isToken : r = tok <;> by_cases mark : r = gues <;>
      simp [middle,Store.set,expect,isToken,mark,tokenZero,Ne.symm exp_ne_tok,
        show tok ≠ fr by decide,exp_ne_marker,tok_ne_marker]
  rw [same] at last
  exact Program.Runs.rightExit first last rfl

end PalomarI3380.Compiler.Source
