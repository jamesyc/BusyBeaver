module
public import ModelNativeInstructionGraph
public import M209.SourceData
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeSource
open M209.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- A fixed literal source site. The table is used without expanding it in proofs. -/
def siteGraph (k:Nat) (code:Option Instruction) : ArithmeticSemisentence 20 :=
 match code with
 | none => ⊥
 | some i => (“#1=↑k”:ArithmeticSemisentence 20) ⋏ instructionGraph i
def tableGraph (p:Nat→Option Instruction) (sites:List Nat) : ArithmeticSemisentence 20 :=
 sites.foldr (fun k rest=>siteGraph k (p k) ⋎ rest) ⊥
def nativeProgramGraph : ArithmeticSemisentence 20 := tableGraph program (List.range 4341)
def programStep (s t:State M) : Prop := ∃k:Nat, k<4341 ∧ s.pc=(k:M) ∧ ∃i, program k=some i ∧ execute i s=some t
lemma siteGraph_eval (k:Nat) (code:Option Instruction) (v:Fin 20→M) :
 (siteGraph k code).Evalb v ↔ v 1=(k:M) ∧ ∃i,code=some i ∧
 execute i ⟨v 1,fun j=>v (oldIndex j)⟩=some ⟨v 0,fun j=>v (newIndex j)⟩ := by
 cases code <;> simp [siteGraph,instructionGraph_eval,numeral_eq_natCast]
lemma tableGraph_eval (p:Nat→Option Instruction) (sites:List Nat) (v:Fin 20→M) :
 (tableGraph p sites).Evalb v ↔ ∃k∈sites,v 1=(k:M) ∧ ∃i,p k=some i ∧
 execute i ⟨v 1,fun j=>v (oldIndex j)⟩=some ⟨v 0,fun j=>v (newIndex j)⟩ := by
 induction sites with
 | nil => simp [tableGraph]
 | cons a xs ih =>
   change ((siteGraph a (p a)).Evalb v ∨ (tableGraph p xs).Evalb v) ↔ _
   rw [siteGraph_eval,ih]
   simp
lemma nativeProgramGraph_eval (v:Fin 20→M) :
 nativeProgramGraph.Evalb v ↔ programStep ⟨v 1,fun j=>v (oldIndex j)⟩ ⟨v 0,fun j=>v (newIndex j)⟩ := by
 change (tableGraph program (List.range 4341)).Evalb v ↔ _
 rw [tableGraph_eval]
 simp only [List.mem_range,programStep]
end ZF209.NativeSource
