module
public import I3_334.Calibration.ModelSchedulerInput
public import I3_334.Calibration.ModelProgram
public import I3_334.Search.MainTrial
public import I3_334Support.Search.Arithmetic.CodedLines
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (CodedLines block inc clear move ifZero ifPositive halt store_ext
  coded_clear coded_move coded_increment coded_ifZero_zero coded_ifZero_positive
  coded_decrement_zero coded_decrement_positive)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem coded_output (s : Store M) (ready : Scratch s) (unused : s 11 = 0) :
    CodedLines output s.code (gateStore (s np) (s pl) (finalMark s) (s tmp)).code := by
  let s₁ := s.set goal 0
  let s₂ := (s₁.set fr 0).set expected (s fr)
  let s₃ := (s₂.set lv 0).set tok (s lv)
  let s₄ := ((s₃.set tok 0).set expected 0).set gues (finalMark s)
  have h₁ := coded_clear goal s
  have h₂ : (move fr expected).Runs .normal s₁.code s₂.code := by
    have exp0 : s₁ expected = 0 := by simpa [s₁,Store.set,goal,expected] using ready.expectedEmpty
    have front : s₁ fr = s fr := by simp [s₁,Store.set,goal,fr]
    simpa only [exp0,front,zero_add,s₂] using coded_move (a := fr) (b := expected) (by decide) s₁
  have h₃ : (move lv tok).Runs .normal s₂.code s₃.code := by
    have tok0 : s₂ tok=0 := by simpa [s₂,s₁,Store.set,goal,fr,expected,tok] using ready.tokenEmpty
    have back : s₂ lv=s lv := by simp [s₂,s₁,Store.set,goal,fr,expected,lv]
    simpa only [tok0,back,zero_add,s₃] using coded_move (a := lv) (b := tok) (by decide) s₂
  have h₄ : compare.Runs .normal s₃.code s₄.code := by
    have left : s₃ expected=s fr := by simp [s₃,s₂,Store.set,lv,tok,expected]
    have right : s₃ tok=s lv := Store.get_set ..
    have candidate : s₃ gues=s gues := by simp [s₃,s₂,s₁,Store.set,goal,fr,expected,lv,tok,gues]
    simpa only [left,right,candidate,s₄,finalMark,markedIf] using coded_compare s₃
  have h₅ := coded_clear dc s₄
  have result : s₄.set dc 0 = gateStore (s np) (s pl) (finalMark s) (s tmp) := by
    apply store_ext <;>
      simp [s₄,s₃,s₂,s₁,gateStore,Scheduler.store,tmp,Store.set,
        np,pl,goal,fr,gues,lv,dc,tok,expected,u,
        ready.auxiliaryEmpty,unused]
  rw [result] at h₅
  exact .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ (.cons h₅ (.nil _)))))

theorem coded_accept (index pending marker scratchWord : M) :
    accept.Runs (trialFlow marker) (gateStore index pending marker scratchWord).code
      (Scheduler.mk index pending (if marker=1 then 0 else marker) scratchWord).store.code := by
  let s := gateStore index pending marker scratchWord
  let cleared := (Scheduler.mk index pending (0 : M) scratchWord).store
  have candidate : s gues = marker := Store.get_set ..
  have empty : cleared gues = 0 := by simp [cleared,Scheduler.store,tmp,Store.set,gues,np,pl,fr]
  by_cases accepts : marker=1
  · have nonzero : s gues≠0 := by simp [candidate,accepts]
    have decrease := coded_decrement_positive nonzero
    have ends : s.set gues (s gues-1) = cleared := by
      rw [candidate,accepts,Arithmetic.sub_self]
      change (cleared.set gues marker).set gues 0 = cleared
      rw [Store.set_set,← empty,Store.set_same]
    rw [ends] at decrease
    have stop : halt.Runs .halt cleared.code cleared.code := Program.Runs.instruction .halt _
    have stopIf := coded_ifZero_zero empty stop rfl
    have branch : (block [ifZero gues halt,inc fr,inc fr,move gues fr]).Runs .halt
        cleared.code cleared.code := .leftExit stopIf rfl
    simpa only [accept,ifPositive,s,cleared,trialFlow,accepts,↓reduceIte] using Program.Runs.rightExit decrease branch (by rfl)
  simp only [trialFlow,accepts,↓reduceIte]
  by_cases rejects : marker=0
  · have unchanged : s = (Scheduler.mk index pending marker scratchWord).store := by
      change cleared.set gues marker = _
      rw [rejects]
      exact (congrArg (cleared.set gues) empty.symm).trans (Store.set_same _ _)
    have drop := Program.Runs.leftExit (q := block [ifZero gues halt,inc fr,inc fr,move gues fr])
      (coded_decrement_zero (candidate.trans rejects)) (by rfl)
    exact unchanged ▸ drop
  · let first := s.set gues (marker-1)
    let second := s.set gues (marker-1-1)
    let one := second.set fr 1
    let two := second.set fr 2
    have gt : 1 < marker := by
      rcases zero_or_succ marker with none | ⟨k,hk⟩
      · exact (rejects none).elim
      · have positive : 0 < k := by
          apply lt_of_le_of_ne (Arithmetic.zero_le _)
          intro eq
          exact accepts (by simp [hk,← eq])
        rw [hk]
        simpa using add_lt_add_right positive 1
    have subPositive : marker-1≠0 := (Arithmetic.pos_sub_iff_lt.mpr gt).ne'
    have decrement := coded_decrement_positive (s := s) (r := gues) (by rwa [candidate])
    rw [candidate] at decrement
    have test := coded_ifZero_positive (r := gues) (body := halt) (s := first)
      (by simpa [first,Store.get_set] using subPositive)
    have next : first.set gues (first gues-1) = second := by
      simp [first,second,Store.get_set,Store.set_set]
    rw [next] at test
    have firstInc := coded_increment fr second
    have frZero : second fr=0 := by
      simp [second,s,gateStore,Scheduler.store,Store.set,fr,gues,tmp]
    rw [frZero,zero_add] at firstInc
    have secondInc := coded_increment fr one
    rw [show one fr=1 from Store.get_set ..,show (1 : M)+1=2 from one_add_one_eq_two] at secondInc
    change (inc fr).Runs .normal one.code ((second.set fr 1).set fr 2).code at secondInc
    rw [Store.set_set] at secondInc
    have transfer := coded_move (a := gues) (b := fr) (by decide) two
    have value : two gues = marker-1-1 := by simp [two,second,Store.set,fr,gues,tmp]
    have sums : (2 : M)+(marker-1-1) = marker := by
      rw [Arithmetic.sub_sub,one_add_one_eq_two,add_comm]
      exact tsub_add_cancel_of_le (by simpa only [one_add_one_eq_two] using succ_le_iff_lt.mpr gt)
    rw [show two fr=2 from Store.get_set ..,value,sums] at transfer
    have endStore : (two.set gues 0).set fr marker = (Scheduler.mk index pending marker scratchWord).store := by
      apply store_ext <;>
        simp [two,second,s,gateStore,Scheduler.store,tmp,Store.set,np,pl,fr,gues]
    rw [endStore] at transfer
    exact .rightExit decrement (.rightExit test (.rightExit firstInc (.rightExit secondInc transfer rfl) rfl) rfl) rfl

theorem coded_trial (s : Scheduler M) {prepared final : Store M}
    (input : CodedLines [ifZero pl restart,produce,read goal,contextScan,read dc] s.store.code prepared.code)
    (row : CodedLines rows prepared.code final.code) (ready : Scratch final)
    (unused : final 11 = 0) (index : final np = s.begin.index) :
    main.Runs (trialFlow (finalMark final)) s.store.code
      (s.finish (final pl) (finalMark final) (final tmp)).store.code := by
  have before := (input.append row).append (coded_output final ready unused)
  have proper (x : M) : (trialFlow x).fromRight = some (trialFlow x) := by
    unfold trialFlow
    split <;> rfl
  rw [index] at before
  exact before.finish (coded_accept _ _ _ _) (proper _)

theorem coded_main_total [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (s : Scheduler M) :
    CodedTermination s.store.code ∨
      ∃ p ≤ s.begin.pending, ∃ mark scratchWord : M,
        main.Runs .normal s.store.code (Scheduler.mk s.begin.index p mark scratchWord).store.code := by
  obtain ⟨prepared, input, first⟩ := coded_trialInput_total s
  obtain ⟨final, row, last⟩ := coded_trie_total templateFuel templateTable prepared first.scratch
  have front := first.trans last
  have index : final np = s.begin.index := by
    simpa [Scheduler.store, Store.set,np,pl,fr,tmp] using front.index
  have pending : final pl ≤ s.begin.pending := by
    simpa [Scheduler.store, Store.set,np,pl,fr,tmp] using front.pending
  have unused : final 11 = 0 := by
    simpa [Scheduler.store, Store.set,np,pl,fr,tmp] using front.unused
  have trial := coded_trial s input row front.scratch unused index
  by_cases stop : finalMark final = 1
  · exact Or.inl (.of_halt (by simpa only [trialFlow,stop,↓reduceIte] using trial))
  · exact Or.inr ⟨final pl,pending,finalMark final,final tmp,
      by simpa only [trialFlow,Scheduler.finish,stop,↓reduceIte] using trial⟩

end PalomarI3334.SearchProgram
