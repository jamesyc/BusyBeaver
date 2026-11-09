/- Minimized211 candidate: fresh arithmetic/native model runtime.
The unchanged original source interpreter is reused explicitly. -/
import User211PAInternalFileBoxes
namespace PA211.UserCandidate.PA.InternalTrace.FileBoxes
open PA215
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ScanBits FileLayout PA215.Runtime

def dropGraph : Nat → 𝚺ᴬ₁.Semisentence 2
  | 0 => .mkSigma “y xs. y=xs”
  | n+1 => .mkSigma “y xs. ∃ s, !sndIdxDef s xs ∧ !(dropGraph n) y s”
def frontGraph : Nat → 𝚺ᴬ₁.Semisentence 2
  | 0 => .mkSigma “y xs. y=0”
  | n+1 => .mkSigma “y xs. ∃ a s p, !fstIdxDef a xs ∧ !sndIdxDef s xs ∧
      !(frontGraph n) p s ∧ !adjoinDef y a p”
def valueGraph (r : Nat) : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “y xs. ∃ s, !(dropGraph r) s xs ∧ !fstIdxDef y s”
def suffixGraph (r : Nat) : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “y xs. ∃ s, !(dropGraph r) s xs ∧ !sndIdxDef y s”

def boxGraph : BoxSt → 𝚺ᴬ₁.Semisentence 3
  | .plain .none => CarryCode.rightGraph
  | .mark r => .mkSigma
      “y xs t. ∃ p v rs rt k, !(frontGraph r) p xs ∧ !(valueGraph r) v xs ∧
        !(suffixGraph r) rs xs ∧ !CarryCode.rightGraph rt rs t ∧
        !repeatGraph k v 1 rt ∧ !CarryCode.rightGraph y p (4*k)”
  | .plain (.inc r) => .mkSigma
      “y xs t. ∃ p v rs rt k, !(frontGraph r) p xs ∧ !(valueGraph r) v xs ∧
        !(suffixGraph r) rs xs ∧ !CarryCode.rightGraph rt rs (4*t+2) ∧
        !repeatGraph k (v+1) 1 rt ∧ !CarryCode.rightGraph y p (4*k+2)”
  | .plain (.dec r) => .mkSigma
      “y xs t. ∃ p v rs rt u k, !(frontGraph r) p xs ∧ !(valueGraph r) v xs ∧
        !(suffixGraph r) rs xs ∧ !CarryCode.rightGraph rt rs t ∧ !subDef u v 1 ∧
        !repeatGraph k u 1 rt ∧ !CarryCode.rightGraph y p (4*k+2)”

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
instance drop_defined (r : Nat) : 𝚺ᴬ₁-Function₁ (drop r : V → V) via dropGraph r := by
  induction r with
  | zero => exact .mk fun v => by simp [dropGraph,drop]
  | succ r ih => exact .mk fun v => by simp [dropGraph,sndIdx_defined.df,ih.df,drop]
instance front_defined (r : Nat) : 𝚺ᴬ₁-Function₁ (front r : V → V) via frontGraph r := by
  induction r with
  | zero => exact .mk fun v => by simp [frontGraph,front]
  | succ r ih => exact .mk fun v => by simp [frontGraph,fstIdx_defined.df,sndIdx_defined.df,ih.df,adjoin_defined.df,front]
instance value_defined (r : Nat) : 𝚺ᴬ₁-Function₁ (value r : V → V) via valueGraph r :=
  .mk fun v => by simp [valueGraph,(drop_defined r).df,fstIdx_defined.df,value]
instance suffix_defined (r : Nat) : 𝚺ᴬ₁-Function₁ (suffix r : V → V) via suffixGraph r :=
  .mk fun v => by simp [suffixGraph,(drop_defined r).df,sndIdx_defined.df,suffix]
instance box_defined (x : BoxSt) : 𝚺ᴬ₁-Function₂ (fun xs t : V => box xs x t) via boxGraph x := by
  cases x with
  | mark r => exact .mk fun v => by simp [boxGraph,(front_defined r).df,(value_defined r).df,(suffix_defined r).df,
        CarryCode.right_defined.df,repeat_defined.df,box]
  | plain e =>
    cases e with
    | none => exact .mk fun v => by simp [boxGraph,CarryCode.right_defined.df,box]
    | inc r => exact .mk fun v => by simp [boxGraph,(front_defined r).df,(value_defined r).df,(suffix_defined r).df,
          CarryCode.right_defined.df,repeat_defined.df,box]
    | dec r => exact .mk fun v => by simp [boxGraph,(front_defined r).df,(value_defined r).df,(suffix_defined r).df,
          CarryCode.right_defined.df,repeat_defined.df,sub_defined.df,box]
end Models
#print axioms box_defined
end PA211.UserCandidate.PA.InternalTrace.FileBoxes

