module
public import ZF192.Simulation.Frames.Contracts
public import ZF192.Tape.Halting.StandardModel
public import ZF192.Machine.FrameLayout
@[expose] public section
/-! # Standard frames of ZF192

The same frames as `nativeFrame`, as external zipper configurations with natural-number
registers, padding and finite tails, and the exact correspondence `encode_frameN`. -/
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192.BinaryTape
open ZFR.ArithmeticRepresentation M192 M192.Window M192.Paths M192.Sites RegisterMachine.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma ones_nat (n:Nat) (t:List Bool) : ones (n:M) (bitsCode t)=bitsCode (List.replicate n true++t) := by
 simpa [ones,bitValue] using bitRun_nat (M:=M) n true t

lemma file_nat (vs:List Nat) (X:List Bool) :
 file (vs.map (fun v:Nat=>(v:M))) (bitsCode X)=bitsCode (fileN vs X) := by
 induction vs with
 | nil => rfl
 | cons v vs ih =>
  have e:file ((v::vs).map (fun v:Nat=>(v:M))) (bitsCode X)=blk (v:M) (file (vs.map (fun v:Nat=>(v:M))) (bitsCode X)) := rfl
  have hc:((v+1:Nat):M)=(v:M)+1 := by simp
  rw [e,ih,blk,←hc,show (2:M)*bitsCode (fileN vs X)=bitsCode (false::fileN vs X) by simp [bitsCode,bitValue],ones_nat]
  rfl

lemma left_code (r:Fin 9→Nat) (n:Nat) :
 bitsCode (M:=M) (leftN r n)=ones (n:M) (2*(2*file (regList (fun i=>(r i:M))) 0)) := by
 have hf:file (regList (fun i=>(r i:M))) 0=bitsCode (fileN (regListN r) []) := by
  simpa [regList,regListN,bitsCode,List.map_ofFn] using file_nat (M:=M) (regListN r) []
 rw [hf,leftN,←ones_nat]
 simp [bitsCode,bitValue]

lemma encode_frameN (pc:Nat) (r:Fin 9→Nat) (n:Nat) (ρ:List Bool) :
 encode (M:=M) (frameN pc r n ρ)=nativeFrame pc (fun i=>(r i:M)) (n:M) (bitsCode ρ) := by
 simp only [frameN,encode,BinaryTape.zc,bitsCode_trim,nativeFrame,cell]
 rw [show bitsCode (M:=M) (winL (fpath pc)++leftN r n)=bitPrefix (winL (fpath pc)) (bitsCode (leftN r n))
   from (bitPrefix_bits _ _).symm,
  show bitsCode (M:=M) (winR (fpath pc)++ρ)=bitPrefix (winR (fpath pc)) (bitsCode ρ) from (bitPrefix_bits _ _).symm,
  left_code]

end ZF192.BinaryTape
