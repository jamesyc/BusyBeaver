module
public import ModelNativeCommandBoundary
public import ModelMPFieldUnpair
public import ModelNativePush
public import ModelNativeCopy
public import ModelNativeCons
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeMP
open ZF207.NativeSource ZF207.NativeCommands ZFR.ArithmeticRepresentation ZF207.ModelCommands ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def frame (n l d h:M) : Nat→M := fun i=>if i=1 then l else if i=3 then d else if i=6 then n else if i=7 then h else 0
lemma push {base:Nat} (hb:NativePush.Bound base) (n l t w d h:M) :
 nativeReaches (commandState (base:M) n l 0 ⟨t,w,d,h⟩)
 (commandState ((base+19:Nat):M) n l 0 ⟨0,modelCantor t w,d,h⟩) := by
 have ht:=NativePush.native_push hb (frame n l d h) t w
 simpa [NativePair.pairState,commandState,frame] using ht
lemma copy {base:Nat} (hb:NativeCopy.Bound base) (n l t w d h:M) :
 nativeReaches (commandState (base:M) n l 0 ⟨t,w,d,h⟩)
 (commandState ((base+7:Nat):M) n l 0 ⟨t+d,w,d,h⟩) := by
 let f:Nat→M:=fun i=>if i=0 then w else frame n l d h i
 have ht:=NativeCopy.native_copy hb f d t
 simpa [NativeCopy.drainState,commandState,frame,f] using ht
lemma cons (n l t w d h:M) :
 nativeReaches (commandState 4262 n l 0 ⟨t,w,d,h⟩)
 (commandState 4289 n l 0 ⟨t299 (modelUnpairLeft w) t,modelUnpairRight w,d,h⟩) := by
 have ht:=NativeCons.native_cons NativePop.bound_4262 NativePair.mp_pair_bound NativeTimesFour.bound_4283 (frame n l d h) t w
 simpa [NativePair.pairState,commandState,frame,modelImp_value] using ht
lemma field (n t w d h l:M) :
 nativeReaches (commandState 4222 n l 0 ⟨t,w,d,h⟩)
 (commandState 4236 n (modelUnpairRight l) 0 ⟨t,w,d+modelUnpairLeft l,h⟩) := by
 let f:Nat→M:=fun i=>if i=0 then w else if i=2 then t else frame n l d h i
 have ht:=MPFieldSource.native_unpair_add f l d
 simpa [MPFieldSource.unpairState,commandState,frame,f] using ht
lemma pre_guard (n l t w d h:M) :
 nativeReaches (commandState 4236 n l 0 ⟨t,w,d,h⟩)
 (commandState 4289 n l 0 ⟨t299 t d,w,d,h⟩) := by
 have a:=push NativePush.bound_4236 n l t w d h
 have b:=copy NativeCopy.bound_4255 n l 0 (modelCantor t w) d h
 rw [zero_add] at b
 have c:=cons n l d (modelCantor t w) d h
 rw [modelUnpairLeft_pair,modelUnpairRight_pair] at c
 exact nativeReaches_trans a (nativeReaches_trans b c)
/-- Native MP field+constructor prefix, through exact guard entry4289. -/
theorem native_mp_prefix (n tail t w d h x:M) :
 nativeReaches (bodyEntry (.mp x) n tail ⟨t,w,d,h⟩)
 (commandState 4289 n tail 0 ⟨t299 t (d+x),w,d+x,h⟩) := by
 have a:=field n t w d h (modelCantor x tail)
 rw [modelUnpairLeft_pair,modelUnpairRight_pair] at a
 exact nativeReaches_trans a (pre_guard n tail t w (d+x) h)
end ZF207.NativeMP
