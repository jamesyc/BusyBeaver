module
public import I3_334Support.Search.Arithmetic.ProgramRuns
public import I3_334Support.Search.Compiler.Factorization
@[expose] public section

namespace PalomarI3380.Compiler

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open PalomarI3380.Arithmetic (Chain)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem Program.Runs.bounded {p : Program} {out : Flow} {s t : M}
    (execution : p.Runs out s t) : out.fits p.needs := by
  induction p generalizing out s t with
  | op instruction =>
    change instruction.Runs out s t at execution
    have effect : (instruction.effect (Store.ofCode s)).1 = out :=
      congrArg Prod.fst execution.effect_matches
    rw [← effect]
    cases instruction with
    | inc | halt => trivial
    | decNZ r =>
      by_cases zero : Store.ofCode s r = 0 <;> simp [Op.effect,zero,Program.needs,Flow.fits]
    | break_ n => cases n <;> simp [Op.effect,Program.needs,Flow.fits]
    | continue_ n => simp [Op.effect,Program.needs,Flow.fits]
  | seq p q left right =>
    obtain ⟨steps,last,trace,exit⟩ := execution
    rcases exit with done | ⟨mid,first,done⟩
    · exact leftFits (left done) (Flow.leftInput_exit out)
    · exact rightFits (right done) (Flow.rightInput_exit out)

theorem Program.Runs.closed_flow {p : Program} {out : Flow} {s t : M}
    (closed : p.closed) (execution : p.Runs out s t) : out = .normal ∨ out = .halt := by
  have fits := execution.bounded
  rw [Program.closed] at closed
  rw [closed] at fits
  cases out <;> simp [Flow.fits] at fits ⊢

theorem code_closed_sequence {p q : Program} (hp : p.closed) (hq : q.closed)
    (s : M) (out : Flow) (t : M) :
    (Program.seq p q).Runs out s t ↔
      (out = .halt ∧ p.Runs .halt s t) ∨
      ∃ mid, p.Runs .normal s mid ∧ q.Runs out mid t := by
  constructor
  · rintro ⟨count,last,trace,exit⟩
    obtain ⟨code,_,first,lastEq,edges⟩ := trace
    have empty : count = 0 := by
      rcases zero_or_succ count with zero | ⟨k,positive⟩
      · exact zero
      · have nonzero : 0 < count := by rw [positive]; simp
        obtain ⟨mid,_,loop⟩ := edges 0 nonzero
        have impossible := loop.closed_flow hq
        simp at impossible
    have same : last = s := by simpa only [empty,first] using lastEq.symm
    rw [same] at exit
    rcases exit with stopped | ⟨mid,before,after⟩
    · have options := stopped.closed_flow hp
      cases out <;> simp [Flow.leftInput] at options
      exact Or.inl ⟨rfl,stopped⟩
    · have options := after.closed_flow hq
      cases out <;> simp [Flow.rightInput] at options
      · exact Or.inr ⟨mid,before,after⟩
      · exact Or.inr ⟨mid,before,after⟩
  · rintro (⟨rfl,stopped⟩ | ⟨mid,before,after⟩)
    · exact Program.Runs.leftExit stopped rfl
    · rcases after.closed_flow hq with rfl | rfl
      · exact Program.Runs.rightExit before after rfl
      · exact Program.Runs.rightExit before after rfl

def CodeEquivalent (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (p q : Program) : Prop :=
  ∀ (flow : Flow) (s t : M), p.Runs flow s t ↔ q.Runs flow s t

theorem code_sequence {p p' q q' : Program}
    (left : CodeEquivalent M p p') (right : CodeEquivalent M q q') :
    CodeEquivalent M (.seq p q) (.seq p' q') := by
  intro flow s t
  have loop :
      (fun a b : M => ∃ mid, p.Runs .normal a mid ∧ q.Runs (.repeatAt 0) mid b) =
      (fun a b : M => ∃ mid, p'.Runs .normal a mid ∧ q'.Runs (.repeatAt 0) mid b) := by
    funext a b
    exact propext (exists_congr fun mid => and_congr (left ..) (right ..))
  unfold CodeEquivalent at left right
  simp only [Program.Runs,loop,left,right]

theorem code_associate {p q r : Program} (hp : p.closed) (hq : q.closed) (hr : r.closed) :
    CodeEquivalent M (.seq (.seq p q) r) (.seq p (.seq q r)) := by
  intro out s t
  rw [code_closed_sequence (Program.closed_seq hp hq) hr, code_closed_sequence hp (Program.closed_seq hq hr)]
  constructor
  · rintro (⟨rfl,stop⟩ | ⟨afterBoth,both,last⟩)
    · rcases (code_closed_sequence hp hq s .halt t).mp stop with ⟨_,first⟩ | ⟨next,first,second⟩
      · exact Or.inl ⟨rfl,first⟩
      · exact Or.inr ⟨next,first,(code_closed_sequence hq hr ..).mpr (Or.inl ⟨rfl,second⟩)⟩
    · rcases (code_closed_sequence hp hq s .normal afterBoth).mp both with ⟨bad,_⟩ | ⟨next,first,second⟩
      · cases bad
      · exact Or.inr ⟨next,first,(code_closed_sequence hq hr ..).mpr (Or.inr ⟨afterBoth,second,last⟩)⟩
  · rintro (⟨rfl,first⟩ | ⟨next,first,both⟩)
    · exact Or.inl ⟨rfl,(code_closed_sequence hp hq ..).mpr (Or.inl ⟨rfl,first⟩)⟩
    · rcases (code_closed_sequence hq hr next out t).mp both with ⟨rfl,second⟩ | ⟨afterBoth,second,last⟩
      · exact Or.inl ⟨rfl,(code_closed_sequence hp hq ..).mpr (Or.inr ⟨next,first,second⟩)⟩
      · exact Or.inr ⟨afterBoth,(code_closed_sequence hp hq ..).mpr (Or.inr ⟨next,first,second⟩),last⟩

theorem code_nop_left {p : Program} (closed : p.closed) : CodeEquivalent M (.seq nop p) p := by
  intro out s t
  rw [code_closed_sequence nop_closed closed]
  simp [nop,Program.Runs,Op.Runs,Op.effect]

theorem code_nop_right {p : Program} (closed : p.closed) : CodeEquivalent M (.seq p nop) p := by
  intro out s t
  rw [code_closed_sequence closed nop_closed]
  cases out with
  | normal =>
    simp only [nop,Program.Runs,Op.Runs,Op.effect,true_and,reduceCtorEq,false_and,false_or]
    exact ⟨fun ⟨mid,run,same⟩ => same.symm ▸ run,fun run => ⟨t,run,rfl⟩⟩
  | halt => simp [nop,Program.Runs,Op.Runs,Op.effect]
  | escape n | repeatAt n =>
    simp only [nop,Program.Runs,Op.Runs,Op.effect,reduceCtorEq, false_and,or_false,false_or,
      and_false,exists_false]
    refine ⟨False.elim,fun run => ?_⟩
    have cases' := run.closed_flow closed
    simp at cases' 

theorem code_comm_inc (a b : Register) :
    CodeEquivalent M (.seq (.op (.inc a)) (.op (.inc b))) (.seq (.op (.inc b)) (.op (.inc a))) := by
  intro out s t
  rw [code_closed_sequence (p := .op (.inc a)) (q := .op (.inc b)) rfl rfl,
    code_closed_sequence (p := .op (.inc b)) (q := .op (.inc a)) rfl rfl]
  simp [Program.Runs,Op.Runs,Store.writeCode,increment_commute (Store.ofCode s) a b]

def codedNormalizationLaws (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : NormalizationLaws where
  equivalent := CodeEquivalent M
  reflexive _ _ _ _ := Iff.rfl
  symmetric refinement x y z := (refinement x y z).symm
  transitive first second x y z := (first x y z).trans (second x y z)
  sequence := code_sequence
  associate := code_associate
  nopLeft := code_nop_left
  nopRight := code_nop_right
  commuteIncrements := code_comm_inc

end PalomarI3380.Compiler
