module
public import I3_380.Search.Arithmetic.SchedulerPrograms
public import I3_380.Search.Compiler.MainOutput
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem CodedLines.finish {ps : List Program} {a b : M} (before : CodedLines ps a b)
    {p : Program} {out : Flow} {c : M} (after : p.Runs out b c)
    (proper : out.fromRight = some out) : (Source.block (ps ++ [p])).Runs out a c := by
  induction before with
  | nil => exact after
  | @cons head ps start middle last h _ ih =>
    have tail := ih after
    cases shape : ps ++ [p] with
    | nil => simp at shape
    | cons next rest =>
      change (Source.block (head :: (ps ++ [p]))).Runs out start c
      rw [shape] at tail ⊢
      exact .rightExit h tail proper

theorem coded_mainOutput (s : Store M) (ready : ClearScratch s) :
    CodedLines mainOutput s.code (gateStore (s np) (s pl) (remainingMarker s)).code := by
  let s₁ := s.set sel 0
  let s₂ := (s₁.set fr 0).set «exp» (s fr)
  let s₃ := (s₂.set lv 0).set tok (s lv)
  let s₄ := ((s₃.set «exp» 0).set tok 0).set gues (remainingMarker s)
  have h₁ := coded_clear sel s
  have h₂ : (move fr «exp»).Runs .normal s₁.code s₂.code := by
    have exp0 : s₁ «exp» = 0 := by simpa [s₁,Store.set,sel,«exp»] using ready.expZero
    have front : s₁ fr = s fr := by simp [s₁,Store.set,sel,fr]
    simpa only [exp0,front,zero_add,s₂] using coded_move (a := fr) (b := «exp») (by decide) s₁
  have h₃ : (move lv tok).Runs .normal s₂.code s₃.code := by
    have tok0 : s₂ tok=0 := by simpa [s₂,s₁,Store.set,sel,fr,«exp»,tok] using ready.tokZero
    have back : s₂ lv=s lv := by simp [s₂,s₁,Store.set,sel,fr,«exp»,lv]
    simpa only [tok0,back,zero_add,s₃] using coded_move (a := lv) (b := tok) (by decide) s₂
  have h₄ : compare.Runs .normal s₃.code s₄.code := by
    have left : s₃ «exp»=s fr := by simp [s₃,s₂,Store.set,lv,tok,«exp»]
    have right : s₃ tok=s lv := Store.get_set ..
    have candidate : s₃ gues=s gues := by simp [s₃,s₂,s₁,Store.set,sel,fr,«exp»,lv,tok,gues]
    simpa only [left,right,candidate,s₄,remainingMarker,mark] using coded_compare s₃
  have h₅ := coded_clear dc s₄
  have result : s₄.set dc 0 = gateStore (s np) (s pl) (remainingMarker s) := by
    apply store_ext <;>
      simp [s₄,s₃,s₂,s₁,gateStore,SchedulerState.store,emptyStore,Store.set,
        np,pl,sel,goal,fr,gues,lv,dc,tok,«exp»,
        show s 3=0 from ready.goalZero,show s 8=0 from ready.auxZero,show s 9=0 from ready.tempZero]
  rw [result] at h₅
  exact .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ (.cons h₅ (.nil _)))))

theorem coded_accept (index pending marker : M) :
    acceptGate.Runs (if marker=1 then .halt else .normal) (gateStore index pending marker).code
      (SchedulerState.mk index pending (if marker=1 then 0 else marker)).store.code := by
  let s := gateStore index pending marker
  let cleared := (SchedulerState.mk index pending (0 : M)).store
  have candidate : s gues = marker := Store.get_set ..
  have empty : cleared gues = 0 := by simp [cleared,SchedulerState.store,emptyStore,Store.set,gues,np,pl,goal]
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
    have branch : (block [ifZero gues halt,inc goal,inc goal,move gues goal]).Runs .halt
        cleared.code cleared.code := .leftExit stopIf rfl
    simpa only [acceptGate,ifPositive,s,cleared,accepts,↓reduceIte] using Program.Runs.rightExit decrease branch (by rfl)
  simp only [accepts,↓reduceIte]
  by_cases rejects : marker=0
  · have unchanged : s = (SchedulerState.mk index pending marker).store := by
      change cleared.set gues marker = _
      rw [rejects]
      exact (congrArg (cleared.set gues) empty.symm).trans (Store.set_same _ _)
    have drop := Program.Runs.leftExit (q := block [ifZero gues halt,inc goal,inc goal,move gues goal])
      (coded_decrement_zero (candidate.trans rejects)) (by rfl)
    exact unchanged ▸ drop
  · let first := s.set gues (marker-1)
    let second := s.set gues (marker-1-1)
    let one := second.set goal 1
    let two := second.set goal 2
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
    have firstInc := coded_increment goal second
    have goalZero : second goal=0 := by
      simp [second,s,gateStore,SchedulerState.store,Store.set,goal,gues]
    rw [goalZero,zero_add] at firstInc
    have secondInc := coded_increment goal one
    rw [show one goal=1 from Store.get_set ..,show (1 : M)+1=2 from one_add_one_eq_two] at secondInc
    change (inc goal).Runs .normal one.code ((second.set goal 1).set goal 2).code at secondInc
    rw [Store.set_set] at secondInc
    have transfer := coded_move (a := gues) (b := goal) (by decide) two
    have value : two gues = marker-1-1 := by simp [two,second,Store.set,goal,gues]
    have sums : (2 : M)+(marker-1-1) = marker := by
      rw [Arithmetic.sub_sub,one_add_one_eq_two,add_comm]
      exact tsub_add_cancel_of_le (by simpa only [one_add_one_eq_two] using succ_le_iff_lt.mpr gt)
    rw [show two goal=2 from Store.get_set ..,value,sums] at transfer
    have endStore : (two.set gues 0).set goal marker = (SchedulerState.mk index pending marker).store := by
      apply store_ext <;>
        simp [two,second,s,gateStore,SchedulerState.store,emptyStore,Store.set,np,pl,goal,gues]
    rw [endStore] at transfer
    exact .rightExit decrement (.rightExit test (.rightExit firstInc (.rightExit secondInc transfer rfl) rfl) rfl) rfl

theorem coded_trial (s : SchedulerState M) {prepared final : Store M}
    (input : CodedLines mainInput s.store.code prepared.code)
    (row : CodedLines compiledRows prepared.code final.code) (ready : ClearScratch final) :
    let marker := remainingMarker final
    main.Runs (if marker=1 then .halt else .normal) s.store.code
      (SchedulerState.mk (final np) (final pl) (if marker=1 then 0 else marker)).store.code := by
  have before := (input.append row).append (coded_mainOutput final ready)
  have proper (x : M) : (if x=1 then Flow.halt else Flow.normal).fromRight =
      some (if x=1 then Flow.halt else Flow.normal) := by split <;> rfl
  exact before.finish (coded_accept _ _ _) (proper _)

end PalomarI3380.Compiler.Source
