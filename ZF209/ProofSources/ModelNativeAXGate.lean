module
public import ModelNativeAXGateCore
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeAXGate
open ZF209.NativeSource ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma copyBound : NativeAXCopy.Bound 4187 := by constructor <;> decide +kernel
lemma yBound : NativeTransfer.Bound 4203 5 8 := by constructor <;> decide +kernel
lemma dBound : NativeTransfer.Bound 4206 3 7 := by constructor <;> decide +kernel
lemma transfer_y (pc n l w t a d h x y u v:M) :
 NativeTransfer.transferState 5 8 (frame n l w t a d h x y) pc u v=cfg pc n l w t a d h v u := by
 unfold NativeTransfer.transferState cfg
 congr 1
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8:=by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [frame]
lemma transfer_d (pc n l w t a d h x y u v:M) :
 NativeTransfer.transferState 3 7 (frame n l w t a d h x y) pc u v=cfg pc n l w t a u v x y := by
 unfold NativeTransfer.transferState cfg
 congr 1
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8:=by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [frame]
lemma y_to_x (n l w t a d h x y:M) :
 nativeReaches (cfg 4203 n l w t a d h x y) (cfg 4206 n l w t a d h (x+y) 0) := by
 have hr:=NativeTransfer.native_transfer yBound (frame n l w t a d h x y) y x
 change nativeReaches _ (NativeTransfer.transferState 5 8 _ 4206 0 (x+y)) at hr
 simpa [transfer_y] using hr
lemma d_to_h (n l w t a d h x y:M) :
 nativeReaches (cfg 4206 n l w t a d h x y) (cfg 4209 n l w t a 0 (h+d) x y) := by
 have hr:=NativeTransfer.native_transfer dBound (frame n l w t a d h x y) d h
 change nativeReaches _ (NativeTransfer.transferState 3 7 _ 4209 0 (h+d)) at hr
 simpa [transfer_d] using hr
lemma copy_a (n l w t a d h:M) :
 nativeReaches (cfg 4187 n l w t a d h 0 0) (cfg 4191 n l w t 0 d h a a) := by
 have hr:=NativeAXCopy.drain_terminates copyBound (frame n l w t a d h 0 0) a 0 0
 simpa [NativeAXCopy.drainTerminates,NativeAXCopy.drainState,frame,cfg] using hr
lemma return_fetch (n l w t:M) : nativeReaches (cfg 4221 n l w t 0 0 0 0 0) (cfg 25 n l w t 0 0 0 0 0) := by
 apply nativeReaches_trans (t:=cfg 4328 n l w t 0 0 0 0 0)
 · apply nativeReaches_step
   refine ⟨4221,by decide,rfl,.jump 4328,by decide,?_⟩
   simp [NativeSource.execute,cfg]
 · apply nativeReaches_step
   refine ⟨4328,by decide,rfl,.jump 25,by decide,?_⟩
   simp [NativeSource.execute,cfg]
theorem native_ax_gate (n:M) (s:NativeAX.Store M) :
 nativeReaches (NativeAX.config 4187 n s)
 (NativeAX.config 25 n ⟨if s.a≠s.d ∧ s.a≠s.h then s.t else 0,0,0,0,s.l,s.w⟩) := by
 rcases s with ⟨t,a,d,h,l,w⟩
 have h1:=copy_a n l w t a d h
 have h2:=compareH n l w t 0 d h a a
 have h3:=y_to_x n l w (if h=a then 0 else t) 0 d 0 0 a
 have h4:=d_to_h n l w (if h=a then 0 else t) 0 d 0 a 0
 simp only [zero_add] at h3 h4
 have h5:=compareD n l w (if h=a then 0 else t) 0 0 d a 0
 have h6:=return_fetch n l w (if d=a then 0 else if h=a then 0 else t)
 have hr:=nativeReaches_trans h1 (nativeReaches_trans h2 (nativeReaches_trans h3 (nativeReaches_trans h4 (nativeReaches_trans h5 h6))))
 by_cases hd:a=d <;> by_cases hh:a=h <;> simpa [NativeAX.config,cfg,hd,hh,eq_comm] using hr
end ZF209.NativeAXGate
