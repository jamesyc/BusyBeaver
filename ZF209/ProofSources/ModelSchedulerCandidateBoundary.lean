module
public import ModelFiniteMacroHistory
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.ModelCommands
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Fresh scheduler candidate n enters the command interpreter at live pointer
n+1. This is distinct from retained residual pointer zero (candidate exhausted). -/
noncomputable def candidateEntry (n:M) (s:Store M) : M := commandCfgCode (n+1) s
/-- Every AX-prefixed word lies in the actual search range starting at 2,
including arbitrary nonstandard parameters and residual continuations. -/
lemma ax_candidate_bound (a x y tail:M) : 2≤commandCode (.ax a x y) tail := by
 apply le_trans (show (2:M)≤a+2 from le_add_self)
 exact modelCantor_left_le _ _
end ZF209.ModelCommands
