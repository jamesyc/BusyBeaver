module
public import I3_380.Search.Arithmetic.ProgramRuns
public import I3_380.Search.Compiler.Source
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A fixed source list of commands. Each command may run for an
arbitrary number of steps in the arithmetic model. -/
inductive CodedLines : List Program → M → M → Prop where
  | nil (state : M) : CodedLines [] state state
  | cons {p : Program} {ps : List Program} {a b c : M} :
    p.Runs .normal a b → CodedLines ps b c → CodedLines (p::ps) a c

theorem CodedLines.append {ps qs : List Program} {a b c : M}
    (first : CodedLines ps a b) (last : CodedLines qs b c) : CodedLines (ps++qs) a c := by
  induction first with
  | nil => exact last
  | cons h _ ih => exact .cons h (ih last)

theorem CodedLines.block {ps : List Program} {a b : M} (h : CodedLines ps a b) :
    (block ps).Runs .normal a b := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | @cons p ps a middle ending first rest ih =>
    cases ps with
    | nil => cases rest; exact first
    | cons next tail => exact Program.Runs.rightExit first ih rfl

end PalomarI3380.Compiler.Source
