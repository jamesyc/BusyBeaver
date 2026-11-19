module
public import ModelNativeAXSymbolic
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeAXSymbolic
open ZF207.NativeSource ZFR.ArithmeticRepresentation ZF207.ModelCommands ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def eval (v:Fin 6→M) : Expr→M
 | .zero=>0
 | .atom i=>v i
 | .succ x=>eval v x+1
 | .add x y=>eval v x+eval v y
 | .im x y=>t299 (eval v x) (eval v y)
lemma eval_plus (v:Fin 6→M) (x y:Expr) : eval v (plus x y)=eval v x+eval v y := by
 cases x <;> cases y <;> simp [plus,eval]
noncomputable def listCode (v:Fin 6→M) (xs:List Expr) (tail:M) : M :=
 (xs.map (eval v)).foldr modelCantor tail
noncomputable def materialize (v:Fin 6→M) (tail bottom:M) (s:Store) : NativeAX.Store M :=
 ⟨eval v s.t,eval v s.a,eval v s.d,eval v s.h,listCode v s.fields tail,listCode v s.stack bottom⟩
def Realizes (op:Op) (start stop:Nat) : Prop := ∀s s',exec op s=some s'→∀(n:M)(v:Fin 6→M)(tail bottom:M),
 nativeReaches (NativeAX.config start n (materialize v tail bottom s))
 (NativeAX.config stop n (materialize v tail bottom s'))
lemma push_realizes {base:Nat} (hb:NativePush.Bound base) : Realizes (M:=M) .push base (base+19) := by
 intro s s' he n v tail bottom
 simp only [exec,Option.some.injEq] at he
 subst s'
 simpa [materialize,listCode,eval] using NativeAX.push hb n (materialize v tail bottom s)
lemma cons_realizes {base:Nat} (hp:NativePop.Bound base) (hq:NativePair.Bound (base+11))
 (ht:NativeTimesFour.Bound (base+21)) : Realizes (M:=M) .cons base (base+27) := by
 intro s s' he n v tail bottom
 cases hs:s.stack with
 | nil=>simp [exec,hs] at he
 | cons x xs=>
  simp only [exec,hs,Option.some.injEq] at he
  subst s'
  simpa [materialize,listCode,eval,hs,modelUnpairLeft_pair,modelUnpairRight_pair] using
   NativeAX.cons hp hq ht n (materialize v tail bottom s)
lemma copyA_realizes {base:Nat} (hb:NativeCopyA.Bound base) : Realizes (M:=M) .copyA base (base+7) := by
 intro s s' he n v tail bottom
 simp only [exec,Option.some.injEq] at he
 subst s'
 simpa [materialize,eval_plus] using NativeAX.copyA hb n (materialize v tail bottom s)
lemma copyD_realizes {base:Nat} (hb:NativeCopy.Bound base) : Realizes (M:=M) .copyD base (base+7) := by
 intro s s' he n v tail bottom
 simp only [exec,Option.some.injEq] at he
 subst s'
 simpa [materialize,eval_plus] using NativeAX.copyD hb n (materialize v tail bottom s)
lemma copyH_realizes {base:Nat} (hb:NativeCopyH.Bound base) : Realizes (M:=M) .copyH base (base+7) := by
 intro s s' he n v tail bottom
 simp only [exec,Option.some.injEq] at he
 subst s'
 simpa [materialize,eval_plus] using NativeAX.copyH hb n (materialize v tail bottom s)
lemma readD_realizes : Realizes (M:=M) .readD 224 238 := by
 intro s s' he n v tail bottom
 cases hs:s.fields with
 | nil=>simp [exec,hs] at he
 | cons x xs=>
  simp only [exec,hs,Option.some.injEq] at he
  subst s'
  simpa [materialize,listCode,eval_plus,hs,modelUnpairLeft_pair,modelUnpairRight_pair] using
   NativeAX.readD n (materialize v tail bottom s)
lemma readH_realizes : Realizes (M:=M) .readH 131 145 := by
 intro s s' he n v tail bottom
 cases hs:s.fields with
 | nil=>simp [exec,hs] at he
 | cons x xs=>
  simp only [exec,hs,Option.some.injEq] at he
  subst s'
  simpa [materialize,listCode,eval_plus,hs,modelUnpairLeft_pair,modelUnpairRight_pair] using
   NativeAX.readH n (materialize v tail bottom s)
lemma incT_realizes {base:Nat} (hr:base<4341) (hb:M207.Source.program base=some (.inc 2 (base+1))) :
 Realizes (M:=M) .incT base (base+1) := by
 intro s s' he n v tail bottom
 simp only [exec,Option.some.injEq] at he
 subst s'
 simpa [materialize,eval] using NativeAX.incT hr hb n (materialize v tail bottom s)
end ZF207.NativeAXSymbolic
