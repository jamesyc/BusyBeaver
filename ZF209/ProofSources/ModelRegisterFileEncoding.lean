module
public import ModelBitRuns
public import M209.StartupFrame
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Physical file cell: delimiter0 followed by value+1 one bits. -/
noncomputable def registerBlock (value tail:M) : M := 2*bitRun (value+1) 1 tail
/-- The spare register has value1, hence bit block011, numerical action6+8*tail. -/
def spareRunBlueprint : PR.Blueprint 1 where
 zero := .mkSigma “z tail. z=tail”
 succ := .mkSigma “u z i tail. u=6+8*z”
noncomputable def spareRunConstruction : PR.Construction M spareRunBlueprint where
 zero := fun v=>v 0
 succ := fun _ _ z=>6+8*z
 zero_defined := .mk (by intro v; simp [spareRunBlueprint,numeral_eq_natCast])
 succ_defined := .mk (by intro v; simp [spareRunBlueprint,numeral_eq_natCast])
noncomputable def spareRun (n tail:M) : M := spareRunConstruction.result ![tail] n
def spareRunGraph : 𝚺ᴬ₁.Semisentence 3 := spareRunBlueprint.resultDef
lemma spareRun_defined : 𝚺ᴬ₁.DefinedFunction₂ (spareRun (M:=M)) spareRunGraph := .mk (by
 intro v
 have hv:v=![v 0,v 1,v 2] := by
  funext i; refine Fin.cases rfl (fun j=>?_) i
  refine Fin.cases rfl (fun j=>?_) j
  exact Fin.cases rfl (fun j=>Fin.elim0 j) j
 rw [hv]; exact spareRunConstruction.result_defined_iff _)
instance spareRun_definable : 𝚺ᴬ₁-Function₂ (spareRun (M:=M)) := spareRun_defined.to_definable
lemma spareRun_zero (tail:M) : spareRun 0 tail=tail := spareRunConstruction.result_zero ![tail]
lemma spareRun_succ (n tail:M) : spareRun (n+1) tail=6+8*spareRun n tail :=
 spareRunConstruction.result_succ ![tail] n
lemma spareRun_commute (n tail:M) : spareRun n (6+8*tail)=spareRun (n+1) tail := by
 induction n using ISigma1.sigma1_succ_induction
 · definability
 case zero => rw [spareRun_zero,spareRun_succ,spareRun_zero]
 case succ n ih => rw [spareRun_succ,ih,spareRun_succ (n+1)]
lemma registerBlock_one (tail:M) : registerBlock 1 tail=6+8*tail := by
 unfold registerBlock
 rw [bitRun_succ,show (1:M)=0+1 by simp,bitRun_succ,bitRun_zero]
 norm_num [mul_add,←mul_assoc,add_assoc]
 rw [←add_assoc]
 norm_num
/-- Fixed nine-entry vector. This external arity is fixed; register values and
spare count below are arbitrary elements of the PA model. -/
noncomputable def primaryBlocks (r:Fin 9→M) (tail:M) : M :=
 [r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8].foldr registerBlock tail
noncomputable def registerFileWithTail (r:Fin 9→M) (spares tail:M) : M :=
 primaryBlocks r (spareRun spares tail)
noncomputable def registerFile (r:Fin 9→M) (spares:M) : M := registerFileWithTail r spares 0
lemma registerBlock_nat (v:Nat) (tail:List Bool) :
 registerBlock (v:M) (bitsCode tail)=bitsCode (false::List.replicate (v+1) true++tail) := by
 unfold registerBlock
 have hc:((v+1:Nat):M)=(v:M)+1 := by simp
 rw [←hc,show (1:M)=bitValue true by rfl,bitRun_nat]
 simp [bitsCode,bitValue]
lemma spareRun_nat (n:Nat) (tail:List Bool) :
 spareRun (n:M) (bitsCode tail)=bitsCode (M6.Runtime.sepsR (List.replicate n 1)++tail) := by
 induction n with
 | zero => simp [spareRun_zero,M6.Runtime.sepsR,bitsCode]
 | succ n ih =>
  have hc:((n+1:Nat):M)=(n:M)+1 := by simp
  rw [hc,spareRun_succ,←registerBlock_one,ih]
  rw [show (1:M)=(1:Nat) by simp,registerBlock_nat]
  simp [M6.Runtime.sepsR,List.replicate_succ,List.flatMap_cons,List.append_assoc]
lemma registerBlocks_nat (vs:List Nat) (tail:List Bool) :
 (vs.map (fun v:Nat=>(v:M))).foldr registerBlock (bitsCode tail)=bitsCode (M6.Runtime.sepsR vs++tail) := by
 induction vs with
 | nil => simp [M6.Runtime.sepsR]
 | cons v vs ih =>
  simp only [List.map_cons,List.foldr_cons,ih]
  rw [registerBlock_nat]
  simp [M6.Runtime.sepsR,List.flatMap_cons,List.append_assoc]
lemma registerFileWithTail_nat (r:Fin 9→Nat) (n:Nat) (tail:List Bool) :
 registerFileWithTail (fun i=>(r i:M)) (n:M) (bitsCode tail)=
 bitsCode (M6.Runtime.sepsR ([r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8]++List.replicate n 1)++tail) := by
 unfold registerFileWithTail primaryBlocks
 rw [spareRun_nat]
 have h:=registerBlocks_nat (M:=M) [r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8]
  (M6.Runtime.sepsR (List.replicate n 1)++tail)
 simpa [M6.Runtime.sepsR,List.flatMap_append,List.append_assoc] using h
lemma registerFile_nat (r:Fin 9→Nat) (n:Nat) :
 registerFile (fun i=>(r i:M)) (n:M)=
 bitsCode (M6.Runtime.sepsR ([r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8]++List.replicate n 1)) := by
 simpa only [registerFile,bitsCode,List.append_nil] using registerFileWithTail_nat (M:=M) r n []
def initialPrimary : Fin 9→Nat := ![0,0,0,0,0,0,2,0,0]
attribute [irreducible] spareRunGraph
end ZF209.BinaryTape
