module
public import I3_380.Search.Arithmetic.StoreCode
public import I3_380.Arithmetic.FiniteTraces
@[expose] public section

namespace PalomarI3380.Compiler

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PalomarI3380.Arithmetic (Chain)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Which control result from a child exits its parent with the given
result. The two missing cases are sequencing and a loop back edge. -/
def Flow.leftInput : Flow → Flow
  | .normal => .escape 0
  | .escape n => .escape (n+1)
  | .repeatAt n => .repeatAt n
  | .halt => .halt

def Flow.rightInput : Flow → Flow
  | .repeatAt n => .repeatAt (n+1)
  | other => other

theorem Flow.leftInput_of_exit {input output : Flow} (h : input.fromLeft = some output) :
    output.leftInput = input := by
  cases input with
  | normal => cases h
  | halt | repeatAt => cases h; rfl
  | escape n => cases n <;> cases h <;> rfl

theorem Flow.rightInput_of_exit {input output : Flow} (h : input.fromRight = some output) :
    output.rightInput = input := by
  cases input with
  | normal | halt | escape => cases h; rfl
  | repeatAt n => cases n <;> cases h <;> rfl

theorem Flow.leftInput_exit (flow : Flow) : flow.leftInput.fromLeft = some flow := by
  cases flow <;> rfl

theorem Flow.rightInput_exit (flow : Flow) : flow.rightInput.fromRight = some flow := by
  cases flow <;> rfl

def Op.Runs (op : Op) (out : Flow) (start finish : M) : Prop :=
  match op with
  | .inc r => out = .normal ∧ finish = Store.writeCode r start (Store.ofCode start r+1)
  | .decNZ r =>
      (out = .escape 0 ∧ Store.ofCode start r = 0 ∧ finish = start) ∨
      (out = .normal ∧ Store.ofCode start r ≠ 0 ∧
        finish = Store.writeCode r start (Store.ofCode start r-1))
  | .break_ n => out = (Op.effect (V := Nat) (.break_ n) (fun _ => 0)).1 ∧ finish = start
  | .continue_ n => out = .repeatAt n ∧ finish = start
  | .halt => out = .halt ∧ finish = start

private theorem opRuns_definable (op : Op) (flow : Flow) :
    𝚺ᴬ₁-Relation (op.Runs (M := M) flow) := by
  change 𝚺ᴬ₁.Definable (fun v : Fin 2 → M => op.Runs flow (v 0) (v 1))
  cases op with
  | inc r | decNZ r =>
    have read := Store.read_definable (M := M) r
    have write := Store.writeCode_definable (M := M) r
    cases flow <;> simp [Op.Runs] <;> definability
  | break_ n =>
    cases n <;> cases flow <;> simp [Op.Runs,Op.effect] <;> definability
  | continue_ n | halt =>
    cases flow <;> simp [Op.Runs] <;> definability

theorem Op.Runs.effect_matches {op : Op} {out : Flow} {start finish : M}
    (run : op.Runs out start finish) :
    op.effect (Store.ofCode start) = (out,Store.ofCode finish) := by
  cases op with
  | inc r =>
    obtain ⟨rfl,rfl⟩ := run
    simp [Op.effect,Store.writeCode]
  | decNZ r =>
    rcases run with ⟨rfl,zero,rfl⟩ | ⟨rfl,nonzero,rfl⟩
    · simp [Op.effect,zero]
    · simp [Op.effect,nonzero,Store.writeCode]
  | break_ n =>
    obtain ⟨rfl,rfl⟩ := run
    cases n <;> rfl
  | continue_ n | halt =>
    obtain ⟨rfl,rfl⟩ := run
    rfl

/-- Execution of a fixed program on arithmetic-model codes. Each binary
sequence iterates its continue edge along a coded finite trace, then
takes a single exit. There is no external finiteness bound on that trace. -/
def Program.Runs : Program → Flow → M → M → Prop
  | .op instruction, flow, start, finish => instruction.Runs flow start finish
  | .seq p q, flow, start, finish =>
      ∃ steps last,
        Chain (fun a b => ∃ mid, p.Runs .normal a mid ∧ q.Runs (.repeatAt 0) mid b) steps start last ∧
        (p.Runs flow.leftInput last finish ∨
          ∃ mid, p.Runs .normal last mid ∧ q.Runs flow.rightInput mid finish)

theorem Program.runs_definable (p : Program) (flow : Flow) :
    𝚺ᴬ₁-Relation (p.Runs (M := M) flow) := by
  induction p generalizing flow with
  | op op => exact opRuns_definable op flow
  | seq p q left right =>
    have leftExit := left flow.leftInput
    have rightExit := right flow.rightInput
    have ready := left .normal
    have repeatEdge := right (.repeatAt 0)
    change 𝚺ᴬ₁.Definable (fun v : Fin 2 → M => (Program.seq p q).Runs flow (v 0) (v 1))
    simp only [Program.Runs,Chain]
    definability

namespace Program.Runs

theorem leftExit {p q : Program} {s t : M} {input out : Flow}
    (run : p.Runs input s t) (exit : input.fromLeft = some out) :
    (Program.seq p q).Runs out s t := by
  refine ⟨0,s,Chain.refl _ _,Or.inl ?_⟩
  rwa [Flow.leftInput_of_exit exit]

theorem rightExit {p q : Program} {s mid t : M} {input out : Flow}
    (first : p.Runs .normal s mid) (next : q.Runs input mid t)
    (exit : input.fromRight = some out) : (Program.seq p q).Runs out s t := by
  refine ⟨0,s,Chain.refl _ _,Or.inr ⟨mid,first,?_⟩⟩
  rwa [Flow.rightInput_of_exit exit]

theorem reenter {p q : Program} {s mid next t : M} {out : Flow}
    (first : p.Runs .normal s mid) (again : q.Runs (.repeatAt 0) mid next)
    (rest : (Program.seq p q).Runs out next t) : (Program.seq p q).Runs out s t := by
  obtain ⟨steps,last,trace,exit⟩ := rest
  exact ⟨1+steps,last,(Chain.single ⟨mid,first,again⟩).trans trace,exit⟩

theorem instruction (op : Op) (s : Store M) :
    (Program.op op).Runs (op.effect s).1 s.code (op.effect s).2.code := by
  cases op with
  | inc r => simp [Program.Runs,Op.Runs,Op.effect,Store.writeCode]
  | decNZ r =>
    by_cases zero : s r = 0 <;> simp [Program.Runs,Op.Runs,Op.effect,Store.writeCode,zero]
  | break_ n => cases n <;> simp [Program.Runs,Op.Runs,Op.effect]
  | continue_ n | halt => simp [Program.Runs,Op.Runs,Op.effect]

theorem store_length {p : Program} {out : Flow} {s t : M} (run : p.Runs out s t)
    (start : len s = (12 : M)) : len t = (12 : M) := by
  induction p generalizing out s t with
  | op instruction =>
    change instruction.Runs out s t at run
    cases instruction with
    | inc r =>
      obtain ⟨_,rfl⟩ := run
      exact Store.len_code _
    | decNZ r =>
      rcases run with ⟨_,_,rfl⟩ | ⟨_,_,rfl⟩
      · exact start
      · exact Store.len_code _
    | break_ | continue_ | halt =>
      obtain ⟨_,rfl⟩ := run
      exact start
  | seq p q left right =>
    obtain ⟨steps,last,trace,exit⟩ := run
    have lastLength := trace.last_holds (fun code => len code = (12 : M)) (by definability) start
      (fun a b ready ⟨mid,first,second⟩ => right second (left first ready))
    rcases exit with leftExit | ⟨mid,first,second⟩
    · exact left leftExit lastLength
    · exact right second (left first lastLength)

end Program.Runs
end PalomarI3380.Compiler
