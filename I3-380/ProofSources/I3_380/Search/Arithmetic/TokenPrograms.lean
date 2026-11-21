module
public import I3_380.Search.Arithmetic.DictionaryScan
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ArithmeticMachine.SourceCantor (decodeLeft decodeRight)
open ArithmeticMachine.SourceWords (cons tail decodeLeft_cons decodeRight_cons tail_cons)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem coded_increments (n : Nat) (r : Register) (s : Store M) :
    CodedLines (List.replicate n (inc r)) s.code (s.set r (s r+(n : M))).code := by
  induction n generalizing s with
  | zero =>
    simpa only [List.replicate_zero,Nat.cast_zero,add_zero,Store.set_same] using CodedLines.nil s.code
  | succ n ih =>
    let next := s.set r (s r+1)
    have rest := ih next
    change CodedLines _ next.code ((s.set r (s r+1)).set r ((s.set r (s r+1)) r+(n : M))).code at rest
    rw [Store.get_set,Store.set_set,add_right_comm] at rest
    simpa only [List.replicate_succ,Nat.cast_succ,add_assoc] using
      CodedLines.cons (coded_increment r s) rest

noncomputable def literalMarker (s : Store M) (token : Token) : M :=
  if decodeLeft (s fr) = (token.arity+1 : Nat) ∧ decodeLeft (decodeRight (s fr)) = token.tag
  then s gues else 0

theorem coded_literal (s : Store M) (token : Token) (clean : ContextScratch s) :
    (eatLiteral token).Runs .normal s.code
      ((s.set fr (tail (s fr))).set gues (literalMarker s token)).code := by
  let expected := s.set «exp» ((token.arity+1 : Nat) : M)
  have header := coded_increments (token.arity+1) «exp» s
  rw [clean.1,zero_add] at header
  have noTok : expected tok = 0 := by simpa [expected,Store.set,«exp»,tok] using clean.2.1
  have noAux : expected u = 0 := by simpa [expected,Store.set,«exp»,u] using clean.2.2
  have first := coded_eat expected noTok noAux
  let afterFirst := eatScanField expected
  have cleared : afterFirst «exp» = 0 := by
    simp [afterFirst,eatScanField,Store.set,«exp»,gues]
  have label := coded_increments token.tag «exp» afterFirst
  rw [cleared,zero_add] at label
  let next := afterFirst.set «exp» (token.tag : M)
  have tokenReady : next tok = 0 := by
    simpa [next,afterFirst,expected,eatScanField,Store.set,tok,«exp»,fr,gues] using clean.2.1
  have scratchReady : next u = 0 := by
    simpa [next,afterFirst,expected,eatScanField,Store.set,u,«exp»,fr,gues] using clean.2.2
  have last := coded_eat next tokenReady scratchReady
  change eat.Runs .normal next.code (eatScanField next).code at last
  have frontAfter : next fr = decodeRight (s fr) := by
    simp [next,afterFirst,expected,eatScanField,Store.set,fr,«exp»,gues]
  have expectedTag : next «exp» = (token.tag : M) := Store.get_set ..
  have markAfter : next gues = if decodeLeft (s fr)=((token.arity+1 : Nat) : M) then s gues else 0 := by
    simp [next,afterFirst,expected,eatScanField,Store.set,«exp»,fr,gues,eq_comm]
  have mark : eatScanField next gues = literalMarker s token := by
    simp only [eatScanField,Store.get_set]
    rw [expectedTag,frontAfter,markAfter]
    change (if (token.tag : M)=decodeLeft (decodeRight (s fr)) then
        (if decodeLeft (s fr)=((token.arity+1 : Nat) : M) then s gues else 0) else 0) =
      (if decodeLeft (s fr)=((token.arity+1 : Nat) : M) ∧
        decodeLeft (decodeRight (s fr))=(token.tag : M) then s gues else 0)
    by_cases t : decodeLeft (decodeRight (s fr))=(token.tag : M)
    · rw [if_pos t.symm]
      simp only [t,and_true]
    · rw [if_neg (Ne.symm t)]
      simp only [t,and_false,ite_false]
  have normalized : eatScanField next = (s.set fr (tail (s fr))).set gues (literalMarker s token) := by
    funext r
    by_cases front : r=fr
    · subst r
      simp only [eatScanField,Store.get_set_other _ _ _ _ (by decide : fr ≠ gues),
        Store.get_set_other _ _ _ _ (by decide : fr ≠ «exp»),Store.get_set,frontAfter,tail]
    by_cases marked : r=gues
    · subst r
      simpa only [Store.get_set] using mark
    by_cases expZero : r=«exp»
    · subst r
      have preserved : (s.set fr (tail (s fr))).set gues (literalMarker s token) «exp» = 0 := by
        simpa [Store.set,«exp»,fr,gues] using clean.1
      have actual : eatScanField next «exp» = 0 := by simp [eatScanField,Store.set,«exp»,fr,gues]
      exact actual.trans preserved.symm
    simp [next,afterFirst,expected,eatScanField,Store.set,front,marked,expZero]
  rw [normalized] at last
  apply CodedLines.block
  have form := header.append (CodedLines.cons first (label.append (.cons last (.nil _))))
  simpa only [eatLiteral,List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using form

theorem coded_side (s : Store M) (clear : s tmp = 0) :
    side.Runs .normal s.code ((s.set fr (s lv)).set lv (s fr)).code := by
  let first := (s.set fr 0).set tmp (s tmp+s fr)
  let second := (first.set lv 0).set fr (first fr+first lv)
  have liftFront : (move fr tmp).Runs .normal s.code first.code := coded_move (by decide) s
  have liftBack : (move lv fr).Runs .normal first.code second.code := coded_move (by decide) first
  have restore := coded_move (a := tmp) (b := lv) (by decide) second
  have result : (second.set tmp 0).set lv (second lv+second tmp) = (s.set fr (s lv)).set lv (s fr) := by
    funext r
    by_cases a : r=fr <;> by_cases b : r=lv <;> by_cases c : r=tmp <;>
      simp_all [first,second,Store.set,fr,lv,tmp]
  rw [result] at restore
  exact Program.Runs.rightExit liftFront (Program.Runs.rightExit liftBack restore rfl) rfl

end PalomarI3380.Compiler.Source
