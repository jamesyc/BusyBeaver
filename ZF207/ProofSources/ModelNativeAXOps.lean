module
public import ModelNativeCons
public import ModelNativePush
public import ModelNativeCopy
public import ModelNativeCopyA
public import ModelNativeCopyH
public import ModelAXFieldDUnpair
public import ModelAXFieldHUnpair
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeAX
open ZF207.NativeSource ZFR.ArithmeticRepresentation ZF207.ModelCommands ZF207.MM0ModelReplay M207.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
structure Store (M:Type*) where
 t:M
 a:M
 d:M
 h:M
 l:M
 w:M
noncomputable def config (pc:Nat) (n:M) (s:Store M) : NativeSource.State M :=
 ⟨(pc:M),![s.w,s.l,s.t,s.d,s.a,0,n,s.h,0]⟩
noncomputable def frame (n:M) (s:Store M) : Nat→M :=
 fun i=>if i=0 then s.w else if i=1 then s.l else if i=2 then s.t else if i=3 then s.d else if i=4 then s.a else if i=6 then n else if i=7 then s.h else 0
lemma push {base:Nat} (hb:NativePush.Bound base) (n:M) (s:Store M) :
 nativeReaches (config base n s) (config (base+19) n {s with t:=0,w:=modelCantor s.t s.w}) := by
 have hh:=NativePush.native_push hb (frame n s) s.t s.w
 simpa [config,NativePair.pairState,frame] using hh
lemma cons {base:Nat} (hp:NativePop.Bound base) (hq:NativePair.Bound (base+11))
 (ht:NativeTimesFour.Bound (base+21)) (n:M) (s:Store M) :
 nativeReaches (config base n s) (config (base+27) n {s with t:=t299 (modelUnpairLeft s.w) s.t,w:=modelUnpairRight s.w}) := by
 have hh:=NativeCons.native_cons hp hq ht (frame n s) s.t s.w
 simpa [config,NativePair.pairState,frame,modelImp_value] using hh
lemma copyD {base:Nat} (hb:NativeCopy.Bound base) (n:M) (s:Store M) :
 nativeReaches (config base n s) (config (base+7) n {s with t:=s.t+s.d}) := by
 have hh:=NativeCopy.native_copy hb (frame n s) s.d s.t
 simpa [config,NativeCopy.drainState,frame] using hh
lemma copyA {base:Nat} (hb:NativeCopyA.Bound base) (n:M) (s:Store M) :
 nativeReaches (config base n s) (config (base+7) n {s with t:=s.t+s.a}) := by
 have hh:=NativeCopyA.native_copy hb (frame n s) s.a s.t
 simpa [config,NativeCopyA.drainState,frame] using hh
lemma copyH {base:Nat} (hb:NativeCopyH.Bound base) (n:M) (s:Store M) :
 nativeReaches (config base n s) (config (base+7) n {s with t:=s.t+s.h}) := by
 have hh:=NativeCopyH.native_copy hb (frame n s) s.h s.t
 simpa [config,NativeCopyH.drainState,frame] using hh
lemma readD (n:M) (s:Store M) :
 nativeReaches (config 224 n s) (config 238 n {s with d:=s.d+modelUnpairLeft s.l,l:=modelUnpairRight s.l}) := by
 have hh:=AXFieldDSource.native_unpair_add (frame n s) s.l s.d
 simpa [config,AXFieldDSource.unpairState,frame] using hh
lemma readH (n:M) (s:Store M) :
 nativeReaches (config 131 n s) (config 145 n {s with h:=s.h+modelUnpairLeft s.l,l:=modelUnpairRight s.l}) := by
 have hh:=AXFieldHSource.native_unpair_add (frame n s) s.l s.h
 simpa [config,AXFieldHSource.unpairState,frame] using hh
lemma incT {base:Nat} (hr:base<4341) (hb:program base=some (.inc 2 (base+1))) (n:M) (s:Store M) :
 nativeReaches (config base n s) (config (base+1) n {s with t:=s.t+1}) := by
 apply nativeReaches_step
 refine ⟨base,hr,rfl,.inc 2 (base+1),hb,?_⟩
 simp only [NativeSource.execute,config]
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp
end ZF207.NativeAX
