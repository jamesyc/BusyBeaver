module
public import I3_380.Search.Arithmetic.CompareProgram
public import I3_380.Search.Arithmetic.LoopInvariant
public import I3_380.Search.Arithmetic.WordEmission
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ArithmeticMachine.SourceCantor (decodeLeft decodeRight decode_pairValue)
open ArithmeticMachine.SourceWords (tail emitVector emitVector_cons tail_cons decodeLeft_cons decodeRight_cons)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def ContextScratch (s : Store M) : Prop := s «exp» = 0 ∧ s tok = 0 ∧ s u = 0

noncomputable def replaceContext (s : Store M) (front back marker : M) : Store M :=
  ((s.set fr front).set lv back).set gues marker

theorem contextScratch_replace {s : Store M} (clean : ContextScratch s) (front back marker : M) :
    ContextScratch (replaceContext s front back marker) := by
  simpa [ContextScratch,replaceContext,Store.set,«exp»,tok,u,fr,lv,gues] using clean

theorem coded_contextField (s : Store M) (clean : ContextScratch s) :
    contextField.Runs .normal s.code
      (replaceContext s (decodeRight (s fr)) (decodeRight (s lv))
        (if decodeLeft (s lv) = decodeLeft (s fr) then s gues else 0)).code := by
  let a := decodeLeft (s lv)
  let b := decodeRight (s lv)
  let stage := (s.set lv b).set «exp» a
  have first := coded_pop (src := lv) (dst := «exp») (by decide) (by decide) (by decide) s clean.1 clean.2.2
  have noToken : stage tok = 0 := by
    simpa [stage,Store.set,tok,lv,«exp»] using clean.2.1
  have noScratch : stage u = 0 := by
    simpa [stage,Store.set,u,lv,«exp»] using clean.2.2
  have last := coded_eat stage noToken noScratch
  have front : stage fr = s fr := by simp [stage,Store.set,fr,lv,«exp»]
  have expected : stage «exp» = a := Store.get_set ..
  have marker : stage gues = s gues := by simp [stage,Store.set,gues,lv,«exp»]
  rw [front,expected,marker] at last
  have reset : (s.set lv b).set «exp» 0 = s.set lv b := by
    have same : (s.set lv b) «exp» = 0 := by simpa [Store.set,lv,«exp»] using clean.1
    rw [← same,Store.set_same]
  have aligned :=
    (show ((stage.set fr (decodeRight (s fr))).set «exp» 0) = (s.set fr (decodeRight (s fr))).set lv b by
      unfold stage
      rw [Store.set_comm _ (by decide : «exp» ≠ fr),Store.set_set,
        Store.set_comm _ (by decide : fr ≠ «exp»),reset,
        Store.set_comm _ (by decide : lv ≠ fr)])
  rw [aligned] at last
  exact Program.Runs.rightExit first last rfl

noncomputable def fieldMarker (s : Store M) : M :=
  if decodeLeft (s lv)=decodeLeft (s fr) then s gues else 0

noncomputable def tokenMarker (s : Store M) : M :=
  if decodeLeft (s lv)=decodeLeft (s fr) ∧
      decodeLeft (decodeRight (s lv))=decodeLeft (decodeRight (s fr))
  then s gues else 0

theorem coded_contextToken (s : Store M) (clean : ContextScratch s) :
    (Program.seq contextField contextField).Runs .normal s.code
      (replaceContext s (tail (s fr)) (tail (s lv)) (tokenMarker s)).code := by
  let middle := replaceContext s (decodeRight (s fr)) (decodeRight (s lv)) (fieldMarker s)
  have first := coded_contextField s clean
  have last := coded_contextField middle
    (contextScratch_replace clean (decodeRight (s fr)) (decodeRight (s lv)) (fieldMarker s))
  have front : middle fr = decodeRight (s fr) := by simp [middle,replaceContext,Store.set,fr,lv,gues]
  have back : middle lv = decodeRight (s lv) := by simp [middle,replaceContext,Store.set,lv,gues]
  have marker : middle gues = fieldMarker s := Store.get_set ..
  rw [front,back,marker] at last
  have combine :
      (if decodeLeft (decodeRight (s lv))=decodeLeft (decodeRight (s fr)) then fieldMarker s else 0) =
        tokenMarker s := by
    unfold fieldMarker tokenMarker
    by_cases left : decodeLeft (s lv)=decodeLeft (s fr) <;>
      by_cases right : decodeLeft (decodeRight (s lv))=decodeLeft (decodeRight (s fr)) <;> simp [left,right]
  rw [combine] at last
  have merge : replaceContext middle (tail (s fr)) (tail (s lv)) (tokenMarker s) =
      replaceContext s (tail (s fr)) (tail (s lv)) (tokenMarker s) := by
    funext r
    by_cases isFront : r = fr <;> by_cases isBack : r = lv <;> by_cases isMarker : r = gues <;>
      simp [middle,replaceContext,Store.set,isFront,isBack,isMarker]
  change (Program.seq contextField contextField).Runs .normal s.code _
  exact Program.Runs.rightExit first (merge ▸ last) rfl

theorem coded_contextToken_shared (s : Store M) (clean : ContextScratch s) (token rest front back : M)
    (left : s fr = emitVector (token ∷ rest) front)
    (right : s lv = emitVector (token ∷ rest) back) :
    (Program.seq contextField contextField).Runs .normal s.code
      (replaceContext s (emitVector rest front) (emitVector rest back) (s gues)).code := by
  have step := coded_contextToken s clean
  simpa only [left,right,emitVector_cons,tail_cons,tokenMarker,decodeLeft_cons,
    decodeRight_cons,(decode_pairValue _ _).1,eq_self_iff_true,and_self,↓reduceIte] using step

noncomputable def contextState (s : Store M) (remaining a b marker : M) : Store M :=
  replaceContext (s.set sel remaining) a b marker

theorem contextState_code (s : Store M) (remaining a b marker : M) :
    (contextState s remaining a b marker).code =
      Store.writeCode gues (Store.writeCode lv (Store.writeCode fr (Store.writeCode sel s.code remaining) a) b) marker := by
  simp [contextState,replaceContext,Store.writeCode]

/-- The context scanner decrements its counter and consumes one cell
from each stream per round. Other registers remain available unchanged. -/
theorem coded_contextScan_invariant (s : Store M) (clean : ContextScratch s)
    (P : M → M → M → M → Prop) (defined : 𝚺ᴬ₁-Relation₄ P)
    (initial : P 0 (s fr) (s lv) (s gues))
    (next : ∀ i < s sel, ∀ a b g, P i a b g →
      P (i+1) (tail a) (tail b) (tokenMarker (contextState s (s sel-i-1) a b g))) :
    ∃ a b g, P (s sel) a b g ∧
      contextScan.Runs .normal s.code (contextState s 0 a b g).code := by
  let I := fun i code : M => ∃ a b g, P i a b g ∧ code = (contextState s (s sel-i) a b g).code
  have relation : 𝚺ᴬ₁-Relation I := by
    have dSel := Store.writeCode_definable (M := M) sel
    have dFr := Store.writeCode_definable (M := M) fr
    have dLv := Store.writeCode_definable (M := M) lv
    have dGuess := Store.writeCode_definable (M := M) gues
    unfold I
    simp only [contextState_code]
    definability
  have first : contextState s (s sel-0) (s fr) (s lv) (s gues) = s := by
    simp [contextState,replaceContext,Store.set_same]
  have start : I 0 s.code := ⟨_,_,_,initial,congrArg Store.code first.symm⟩
  have count (n a b g : M) : contextState s n a b g sel = n := by
    simp [contextState,replaceContext,Store.set,sel,fr,lv,gues]
  have stopped (code : M) (state : I (s sel) code) : Store.ofCode code sel = 0 := by
    obtain ⟨a,b,g,_,rfl⟩ := state
    rw [Store.ofCode_code,count,Arithmetic.sub_self]
  have iterate : ∀ i < s sel, ∀ code : M, I i code →
      Store.ofCode code sel ≠ 0 ∧
        ∃ nextCode : M, (Program.seq contextField contextField).Runs .normal
          (Store.writeCode sel code (Store.ofCode code sel-1)) nextCode ∧ I (i+1) nextCode := by
    intro i prior code state
    obtain ⟨a,b,g,hP,rfl⟩ := state
    let current := contextState s (s sel-i) a b g
    let mid := contextState s (s sel-i-1) a b g
    have positive : (s sel-i) ≠ 0 := (Arithmetic.pos_sub_iff_lt.mpr prior).ne'
    rw [Store.ofCode_code,count]
    refine ⟨positive,(contextState s (s sel-(i+1)) (tail a) (tail b) (tokenMarker mid)).code,?_,?_⟩
    · have cleanMid : ContextScratch mid := by
        apply contextScratch_replace
        simpa [ContextScratch,Store.set,sel,«exp»,tok,u] using clean
      have step := coded_contextToken mid cleanMid
      have front : mid fr = a := by simp [mid,contextState,replaceContext,Store.set,fr,lv,gues]
      have back : mid lv = b := by simp [mid,contextState,replaceContext,Store.set,lv,gues]
      rw [front,back] at step
      have before : current.set sel (s sel-i-1) = mid := by
        unfold current mid contextState replaceContext
        rw [Store.set_comm _ (by decide : gues ≠ sel) g (s sel-i-1),
          Store.set_comm _ (by decide : lv ≠ sel) b (s sel-i-1),
          Store.set_comm _ (by decide : fr ≠ sel) a (s sel-i-1),Store.set_set]
      have after : replaceContext mid (tail a) (tail b) (tokenMarker mid) =
          contextState s (s sel-(i+1)) (tail a) (tail b) (tokenMarker mid) := by
        funext r
        by_cases isFront : r = fr <;> by_cases isBack : r = lv <;> by_cases isMark : r = gues <;>
          simp [mid,contextState,replaceContext,Store.set,isFront,isBack,isMark,Arithmetic.sub_sub]
      rw [Store.writeCode,Store.ofCode_code]
      change (Program.seq contextField contextField).Runs .normal
        (current.set sel (s sel-i-1)).code _
      rw [before,← after]
      exact step
    · exact ⟨_,_,_,next i prior a b g hP,rfl⟩
  obtain ⟨last,execution,ending⟩ := coded_while_invariant sel (.seq contextField contextField) (s sel)
    s.code I relation start iterate stopped
  obtain ⟨a,b,g,hP,rfl⟩ := ending
  refine ⟨a,b,g,hP,?_⟩
  simpa only [contextScan,Arithmetic.sub_self] using execution

theorem coded_contextScan_total (s : Store M) (clean : ContextScratch s) :
    ∃ a b g, contextScan.Runs .normal s.code (contextState s 0 a b g).code := by
  obtain ⟨a,b,g,_,run⟩ := coded_contextScan_invariant s clean (fun _ _ _ _ => True)
    (by definability) trivial (fun _ _ _ _ _ _ => trivial)
  exact ⟨a,b,g,run⟩

/-- A common token prefix is consumed exactly, including when its length
is nonstandard in the ambient arithmetic model. -/
theorem coded_contextScan_shared (s : Store M) (clean : ContextScratch s)
    (tokens front back : M) (count : s sel = len tokens)
    (left : s fr = emitVector tokens front) (right : s lv = emitVector tokens back) :
    contextScan.Runs .normal s.code (contextState s 0 front back (s gues)).code := by
  let P := fun i a b g : M => ∃ remainder : M,
    len remainder = s sel-i ∧ a = emitVector remainder front ∧
      b = emitVector remainder back ∧ g = s gues
  have definable : 𝚺ᴬ₁-Relation₄ P := by unfold P; definability
  have began : P 0 (s fr) (s lv) (s gues) :=
    ⟨tokens,by simpa only [Arithmetic.sub_zero] using count.symm,left,right,rfl⟩
  have next : ∀ i < s sel, ∀ a b g, P i a b g →
      P (i+1) (tail a) (tail b) (tokenMarker (contextState s (s sel-i-1) a b g)) := by
    intro i earlier a b g state
    obtain ⟨remainder,remaining,aEq,bEq,gEq⟩ := state
    have positive : 0 < len remainder := remaining ▸ (Arithmetic.pos_sub_iff_lt.mpr earlier)
    rcases nil_or_adjoin remainder with rfl | ⟨token,rest,rfl⟩
    · simpa using positive
    · refine ⟨rest,?_,?_,?_,?_⟩
      · rw [← Arithmetic.sub_sub, ← remaining, len_adjoin, Arithmetic.add_sub_self]
      · rw [aEq,emitVector_cons,tail_cons]
      · rw [bEq,emitVector_cons,tail_cons]
      · have values : (contextState s (s sel-i-1) a b g) fr = a ∧
            (contextState s (s sel-i-1) a b g) lv = b ∧
            (contextState s (s sel-i-1) a b g) gues = g := by
          simp [contextState,replaceContext,Store.set,fr,lv,gues]
        unfold tokenMarker
        rw [values.1,values.2.1,values.2.2]
        simp only [aEq,bEq,emitVector_cons,
          decodeLeft_cons,decodeRight_cons,(decode_pairValue _ _).1,eq_self_iff_true,and_self,
          ↓reduceIte,gEq]
  obtain ⟨a,b,g,hP,result⟩ := coded_contextScan_invariant s clean P definable began next
  obtain ⟨rest,length,outA,outB,outMark⟩ := hP
  rw [Arithmetic.sub_self] at length
  have empty : rest = 0 := len_zero_iff_eq_nil.mp length
  simpa only [outA,outB,outMark,empty,ArithmeticMachine.SourceWords.emitVector_nil] using result

end PalomarI3380.Compiler.Source
