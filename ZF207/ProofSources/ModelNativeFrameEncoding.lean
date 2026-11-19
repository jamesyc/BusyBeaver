module
public import ModelNativePhysicalStartup
public import ModelPhysicalReaches
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def bitPrefix : List Bool → M → M
 | [], t => t
 | b::bs,t => bitValue b+2*bitPrefix bs t
lemma bitPrefix_bits (path tail:List Bool) : bitPrefix path (bitsCode (M:=M) tail)=bitsCode (path++tail) := by
 induction path with
 | nil => rfl
 | cons b bs ih => simp only [bitPrefix,List.cons_append,bitsCode,ih]
noncomputable def nativeFrame (pc:Nat) (gap:M) (regs:Fin 9→M) (spares:M) : State M :=
 namedState (M207.inverse 74) 1
  (bitPrefix (M207.Source.paths pc)
   (bitRun (gap+((48-(M207.Source.paths pc).length:Nat):M)) 0 (1+2*registerFile regs spares)))
lemma nativeFrame_nat (pc gap spares:Nat) (r:Fin 9→Nat) :
 nativeFrame pc (gap:M) (fun i=>(r i:M)) (spares:M) =
 encode (M207.Source.frame M207.Source.paths
 ⟨pc,gap,[r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8]++List.replicate spares 1⟩) := by
 unfold nativeFrame
 rw [registerFile_nat]
 have hb : (1:M)+2*bitsCode (M6.Runtime.sepsR ([r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8]++List.replicate spares 1)) =
  bitsCode (true::M6.Runtime.sepsR ([r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8]++List.replicate spares 1)) := rfl
 rw [hb,←Nat.cast_add]
 rw [show (0:M)=bitValue false from rfl,bitRun_nat,bitPrefix_bits]
 simp [M207.Source.frame,M207.Source.rootFrame,M207.mapConf,M6.Runtime.conc,M6.Runtime.flat,
 M6.Runtime.segList,M6.Runtime.boxList,M6.Zip.zc,encode,namedState,bitsCode_trim,
 List.flatMap_append,List.flatMap_map,Function.comp_def,bitsCode,bitValue]
lemma nativeFrame_initial :
 nativeFrame 25 0 (ZF207.NativeCommands.nativeInitial (M:=M)).registers 26 =
 ZF207.NativeCommands.physicalStartupEnd := by
 have h:=nativeFrame_nat (M:=M) 25 0 26 initialPrimary
 have he:(fun i=>(initialPrimary i:M))=(ZF207.NativeCommands.nativeInitial (M:=M)).registers := by
  funext i
  rcases i with ⟨i,hi⟩
  have hh:i=0∨i=1∨i=2∨i=3∨i=4∨i=5∨i=6∨i=7∨i=8:=by omega
  rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst i <;> simp [initialPrimary,ZF207.NativeCommands.nativeInitial]
 rw [he] at h
 simpa [initialPrimary,ZF207.NativeCommands.nativeInitial,ZF207.NativeCommands.physicalStartupEnd,
 M207.Source.initialState,M207.Startup.initialFile] using h
theorem blank_to_native_initial_frame : ∃hist:M,
 runHistory blankCode hist ∧
 ZFR.ArithmeticRepresentation.modelListHead hist=stateCode
  (nativeFrame 25 0 (ZF207.NativeCommands.nativeInitial (M:=M)).registers 26) := by
 rw [nativeFrame_initial]
 exact ZF207.NativeCommands.physical_startup_prefix
end ZF207.BinaryTape
