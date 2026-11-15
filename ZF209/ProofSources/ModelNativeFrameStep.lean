module
public import ModelNativeFrameRelation
public import ModelFrameRegisterAudit
public import M209.SourceCoverage
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativePhysicalLift
open ZFR.ArithmeticRepresentation ZF209.BinaryTape M209.Source ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma native_code_injective {s t:NativeSource.State M} (he:NativeSource.stateCode s=NativeSource.stateCode t) : s=t := by
 unfold NativeSource.stateCode at he
 rcases modelCantor_injective he with ⟨hp,he⟩
 rcases modelCantor_injective he with ⟨h0,he⟩
 rcases modelCantor_injective he with ⟨h1,he⟩
 rcases modelCantor_injective he with ⟨h2,he⟩
 rcases modelCantor_injective he with ⟨h3,he⟩
 rcases modelCantor_injective he with ⟨h4,he⟩
 rcases modelCantor_injective he with ⟨h5,he⟩
 rcases modelCantor_injective he with ⟨h6,he⟩
 rcases modelCantor_injective he with ⟨h7,h8⟩
 have hr:s.registers=t.registers:=by
  funext j;rcases j with ⟨j,hj⟩
  have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8:=by omega
  rcases hh with hh|hh|hh|hh|hh|hh|hh|hh|hh <;> subst j <;> assumption
 cases s;cases t;cases hp;cases hr;rfl
lemma cast_injective {a b:Nat} (h:(a:M)=(b:M)) : a=b := by
 rcases lt_trichotomy a b with hl|he|hg
 · exact False.elim ((model_natCast_lt (M:=M) hl).ne h)
 · exact he
 · exact False.elim ((model_natCast_lt (M:=M) hg).ne h.symm)
lemma execute_frame (pc:Nat) (code:Instruction) (hb:instructionBound 4341 code)
 (hc:FrameImplements (M:=M) pc code) (gap spares:M) (regs:Fin 9→M) (t:NativeSource.State M)
 (he:NativeSource.execute code ⟨(pc:M),regs⟩=some t) :
 ∃pc':Nat,pc'<4341 ∧ ∃gap' spares':M,∃regs':Fin 9→M,
 t=⟨(pc':M),regs'⟩ ∧ Reaches (nativeFrame pc gap regs (spares+1)) (nativeFrame pc' gap' regs' (spares'+1)) := by
 cases code with
 | inc r k=>
  obtain ⟨hr,hc⟩:=hc
  simp only [NativeSource.execute,Option.some.injEq] at he
  subst t
  refine ⟨k,hb.2,gap,spares+1,incrementRegisters regs ⟨r,hr⟩,?_,?_⟩
  · rw [audit_increment_registers]
  · simpa only [add_assoc,show (1:M)+1=2 by norm_num] using hc gap spares regs
 | dec r z p=>
  obtain ⟨hr,hc⟩:=hc
  have hi:=audit_register_index r hr
  by_cases hz:regs ⟨r,hr⟩=0
  · simp only [NativeSource.execute,hi,hz,ite_true,Option.some.injEq] at he
    subst t
    exact ⟨z,hb.2.1,gap,spares,regs,rfl,(hc gap spares regs).1 hz⟩
  · simp only [NativeSource.execute,hi,hz,ite_false,Option.some.injEq] at he
    subst t
    refine ⟨p,hb.2.2,gap+1,spares,decrementRegisters regs ⟨r,hr⟩,?_,(hc gap spares regs).2 hz⟩
    rw [audit_decrement_registers]
 | jump k=>
  simp only [NativeSource.execute,Option.some.injEq] at he
  subst t
  exact ⟨k,hb,gap,spares,regs,rfl,hc gap spares regs⟩
 | halt=>simp [NativeSource.execute] at he
/-- Exact finite-site coverage is the ONLY remaining premise here. -/
theorem frame_step_contract
 (coverage:∀pc:Nat,pc<4341→∃code,program pc=some code ∧ FrameImplements (M:=M) pc code) :
 StepContract (FrameRelation (M:=M)) := by
 intro a b q hs hr root hist hh hhead
 obtain ⟨s,t,rfl,rfl,pc,hpc,hspc,code,hcode,hexec⟩:=hs
 obtain ⟨k,hk,g,sp,r,hsc,hq⟩:=hr
 have hstate:s=⟨(k:M),r⟩:=native_code_injective hsc
 have hkp:k=pc:=cast_injective (hstate.symm ▸ hspc)
 subst k
 subst s
 obtain ⟨other,hother,himpl⟩:=coverage pc hpc
 have he:other=code:=Option.some.inj (hother.symm.trans hcode)
 subst other
 obtain ⟨bounded,hbounded,hbound,_⟩:=M209.Source.Coverage.complete pc hpc
 have he:bounded=code:=Option.some.inj (hbounded.symm.trans hcode)
 subst bounded
 obtain ⟨pc',hpc',g',sp',r',ht,hreach⟩:=execute_frame pc code hbound himpl g sp r t hexec
 obtain ⟨out,hout,ho⟩:=hreach root hist hh (hhead.trans hq)
 refine ⟨out,_,hout,ho,pc',hpc',g',sp',r',?_,rfl⟩
 rw [ht]
end ZF209.NativePhysicalLift
