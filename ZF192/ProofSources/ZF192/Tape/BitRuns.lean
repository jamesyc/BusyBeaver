module
public import ZF192.Tape.History
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Internal binary prefix of n identical bits; b is normally0 or1. -/
def bitRunBlueprint : PR.Blueprint 2 where
 zero := .mkSigma “z b tail. z=tail”
 succ := .mkSigma “u z i b tail. u=b+2*z”
noncomputable def bitRunConstruction : PR.Construction M bitRunBlueprint where
 zero := fun v=>v 1
 succ := fun v _ z=>v 0+2*z
 zero_defined := .mk (by intro v; simp [bitRunBlueprint])
 succ_defined := .mk (by intro v; simp [bitRunBlueprint])
noncomputable def bitRun (n b tail:M) : M := bitRunConstruction.result ![b,tail] n
def bitRunGraph : 𝚺ᴬ₁.Semisentence 4 := bitRunBlueprint.resultDef
lemma bitRun_defined : 𝚺ᴬ₁.DefinedFunction₃ (bitRun (M:=M)) bitRunGraph := .mk (by
 intro v
 rw [Matrix.fun_eq_vec_four v]; exact bitRunConstruction.result_defined_iff _)
instance bitRun_definable : 𝚺ᴬ₁-Function₃ (bitRun (M:=M)) := bitRun_defined.to_definable
lemma bitRun_zero (b tail:M) : bitRun 0 b tail=tail := bitRunConstruction.result_zero ![b,tail]
lemma bitRun_succ (n b tail:M) : bitRun (n+1) b tail=b+2*bitRun n b tail :=
 bitRunConstruction.result_succ ![b,tail] n
lemma bitRun_commute (n b tail:M) : bitRun n b (b+2*tail)=bitRun (n+1) b tail := by
 induction n using ISigma1.sigma1_succ_induction
 · definability
 case zero => rw [bitRun_zero,bitRun_succ,bitRun_zero]
 case succ n ih => rw [bitRun_succ,ih,bitRun_succ (n+1)]
/-- Only this binding uses an external finite list. Internal bitRun above quantifies
all model lengths; it is not defined by mapping a standard Nat sequence. -/
lemma bitRun_nat (n:Nat) (b:Bool) (tail:List Bool) :
 bitRun (n:M) (bitValue b) (bitsCode tail)=bitsCode (List.replicate n b++tail) := by
 induction n with
 | zero => simp [bitRun_zero,bitsCode]
 | succ n ih =>
   have hc : ((n+1:Nat):M)=(n:M)+1 := by simp
   rw [hc,bitRun_succ,ih]
   simp only [List.replicate_succ,List.cons_append,bitsCode]
attribute [irreducible] bitRunGraph
end ZF192.BinaryTape
