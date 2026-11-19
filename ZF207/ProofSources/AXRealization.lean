module
public import AXActualSpec
public import PrimitivePush
public import PrimitiveConsCore
public import PrimitiveCopyA
public import PrimitiveCopyH
public import PrimitiveMPCopy
public import PrimitiveAXReadD
public import PrimitiveAXReadH
@[expose] public section
namespace C207Search.AXMacro
open C207Search.Primitive M207.Source

def registers (s : Store) (bottom : Nat) (f : Registers) : Registers := fun r =>
 if r=2 then s.t else if r=0 then stackCode s.stack bottom else
 if r=4 then s.a else if r=3 then s.d else if r=7 then s.h else
 if r=8 then 0 else if r=5 then 0 else if r=1 then s.l else f r

def configAt (pc : Nat) (s : Store) (bottom : Nat) (f : Registers) : Configuration :=
 ⟨pc,registers s bottom f⟩

def Realizes (op : Op) (start stop : Nat) : Prop :=
 ∀ s s', exec op s = some s' → ∀ bottom f,
 ∃n,0<n ∧ Steps n (configAt start s bottom f) (configAt stop s' bottom f)

private theorem push_registers (s : Store) (t : Nat) (stack : List Nat) (bottom : Nat) (f : Registers) :
 PairCore.registers ⟨t,stackCode stack bottom,0,0,registers s bottom f⟩ =
 registers {s with t:=t,stack:=stack} bottom f := by
 funext r
 by_cases h0:r=0 <;> by_cases h1:r=1 <;> by_cases h2:r=2 <;>
 by_cases h3:r=3 <;> by_cases h4:r=4 <;> by_cases h5:r=5 <;>
 by_cases h7:r=7 <;> by_cases h8:r=8 <;>
 simp_all [registers,PairCore.registers]

theorem push_realizes {offset : Nat} (hb : Push.Bound offset) : Realizes .push offset (offset+19) := by
 intro s s' he bottom f
 simp only [exec,Option.some.injEq] at he
 subst s'
 obtain ⟨n,hn,hs⟩ := Push.push hb s.t (stackCode s.stack bottom) (registers s bottom f)
 refine ⟨n,hn,?_⟩
 have hw : M6.Source.Cantor.pair s.t (stackCode s.stack bottom) = stackCode (s.t::s.stack) bottom := rfl
 rw [hw] at hs
 simpa only [Push.configAt,PairCore.configAt,push_registers,configAt,Nat.add_zero] using hs

theorem cons_realizes {offset : Nat} (hp : PopCore.Bound offset)
 (hq : PairCore.Bound (offset+11)) (hm : TimesFour.Bound (offset+21)) :
 Realizes .cons offset (offset+27) := by
 intro s s' he bottom f
 cases hstack : s.stack with
 | nil => simp [exec,hstack] at he
 | cons v vs =>
   simp only [exec,hstack,Option.some.injEq] at he
   subst s'
   obtain ⟨n,hn,hs⟩ := ConsCore.cons hp hq hm s.t (stackCode s.stack bottom) (registers s bottom f)
   have hw : stackCode s.stack bottom = M6.Source.Cantor.pair v (stackCode vs bottom) := by rw [hstack]; rfl
   have hd : M6.Source.Cantor.decode (stackCode s.stack bottom) = (v,stackCode vs bottom) := by rw [hw,M6.Source.Cantor.decode_pair]
   rw [hd] at hs
   refine ⟨n,hn,?_⟩
   simpa only [PairCore.configAt,push_registers,configAt,Nat.add_zero] using hs

private theorem CopyA_registers (s : Store) (t bottom : Nat) (f : Registers) :
 CopyA.registers s.a t 0 (registers s bottom f) = registers {s with t:=t} bottom f := by
 funext r
 by_cases h0:r=0 <;> by_cases h1:r=1 <;> by_cases h2:r=2 <;>
 by_cases h3:r=3 <;> by_cases h4:r=4 <;> by_cases h5:r=5 <;>
 by_cases h7:r=7 <;> by_cases h8:r=8 <;>
 simp_all [registers,CopyA.registers]

theorem copyA_realizes {offset : Nat} (hb : CopyA.Bound offset) : Realizes .copyA offset (offset+7) := by
 intro s s' he bottom f
 simp only [exec,Option.some.injEq] at he
 subst s'
 refine ⟨7*s.a+2,by omega,?_⟩
 have hs := CopyA.copy hb s.a s.t (registers s bottom f)
 simpa only [CopyA.config,CopyA_registers,configAt,Nat.add_zero] using hs

private theorem CopyH_registers (s : Store) (t bottom : Nat) (f : Registers) :
 CopyH.registers s.h t 0 (registers s bottom f) = registers {s with t:=t} bottom f := by
 funext r
 by_cases h0:r=0 <;> by_cases h1:r=1 <;> by_cases h2:r=2 <;>
 by_cases h3:r=3 <;> by_cases h4:r=4 <;> by_cases h5:r=5 <;>
 by_cases h7:r=7 <;> by_cases h8:r=8 <;>
 simp_all [registers,CopyH.registers]

theorem copyH_realizes {offset : Nat} (hb : CopyH.Bound offset) : Realizes .copyH offset (offset+7) := by
 intro s s' he bottom f
 simp only [exec,Option.some.injEq] at he
 subst s'
 refine ⟨7*s.h+2,by omega,?_⟩
 have hs := CopyH.copy hb s.h s.t (registers s bottom f)
 simpa only [CopyH.config,CopyH_registers,configAt,Nat.add_zero] using hs

private theorem MPCopy_registers (s : Store) (t bottom : Nat) (f : Registers) :
 MPCopy.registers s.d t 0 (registers s bottom f) = registers {s with t:=t} bottom f := by
 funext r
 by_cases h0:r=0 <;> by_cases h1:r=1 <;> by_cases h2:r=2 <;>
 by_cases h3:r=3 <;> by_cases h4:r=4 <;> by_cases h5:r=5 <;>
 by_cases h7:r=7 <;> by_cases h8:r=8 <;>
 simp_all [registers,MPCopy.registers]

theorem copyD_realizes {offset : Nat} (hb : MPCopy.Bound offset) : Realizes .copyD offset (offset+7) := by
 intro s s' he bottom f
 simp only [exec,Option.some.injEq] at he
 subst s'
 refine ⟨7*s.d+2,by omega,?_⟩
 have hs := MPCopy.copy hb s.d s.t (registers s bottom f)
 simpa only [MPCopy.config,MPCopy_registers,configAt,Nat.add_zero] using hs


private theorem AXReadH_registers (s : Store) (l h bottom : Nat) (f : Registers) :
 AXReadH.registers ⟨l,h,0,0,registers s bottom f⟩ = registers {s with l:=l,h:=h} bottom f := by
 funext r
 by_cases h0:r=0 <;> by_cases h1:r=1 <;> by_cases h2:r=2 <;>
 by_cases h3:r=3 <;> by_cases h4:r=4 <;> by_cases h5:r=5 <;>
 by_cases h7:r=7 <;> by_cases h8:r=8 <;>
 simp_all [registers,AXReadH.registers]

theorem readH_realizes : Realizes .readH 131 145 := by
 intro s s' he bottom f
 simp only [exec,Option.some.injEq] at he
 subst s'
 have hs := AXReadH.unpair_add s.l s.h (registers s bottom f)
 refine ⟨AXReadH.loopCost s.l (0,0)+(3*(M6.Source.Cantor.decode s.l).2+1)+(3*(M6.Source.Cantor.decode s.l).1+1),by omega,?_⟩
 simpa only [AXReadH.configAt,AXReadH.exitAt,AXReadH_registers,configAt] using hs

private theorem AXReadD_registers (s : Store) (l d bottom : Nat) (f : Registers) :
 AXReadD.registers ⟨l,d,0,0,registers s bottom f⟩ = registers {s with l:=l,d:=d} bottom f := by
 funext r
 by_cases h0:r=0 <;> by_cases h1:r=1 <;> by_cases h2:r=2 <;>
 by_cases h3:r=3 <;> by_cases h4:r=4 <;> by_cases h5:r=5 <;>
 by_cases h7:r=7 <;> by_cases h8:r=8 <;>
 simp_all [registers,AXReadD.registers]

theorem readD_realizes : Realizes .readD 224 238 := by
 intro s s' he bottom f
 simp only [exec,Option.some.injEq] at he
 subst s'
 have hs := AXReadD.unpair_add s.l s.d (registers s bottom f)
 refine ⟨AXReadD.loopCost s.l (0,0)+(3*(M6.Source.Cantor.decode s.l).2+1)+(3*(M6.Source.Cantor.decode s.l).1+1),by omega,?_⟩
 simpa only [AXReadD.configAt,AXReadD.exitAt,AXReadD_registers,configAt] using hs

theorem incT_realizes {offset : Nat} (hb : M207.Source.program offset = some (.inc 2 (offset+1))) : Realizes .incT offset (offset+1) := by
 intro s s' he bottom f
 simp only [exec,Option.some.injEq] at he
 subst s'
 refine ⟨1,by omega,Steps.cons ?_⟩
 have hh : step (configAt offset s bottom f) = configAt (offset+1) {s with t:=s.t+1} bottom f := by
  unfold step scalarNext configAt
  rw [hb]
  simp only [Option.bind_some,scalarExecute,Option.getD_some]
  apply congrArg (ScalarState.mk (offset+1))
  funext r
  have hval : r.val=2 ↔ r=2 := by
   constructor
   · intro h; apply Fin.ext; exact h
   · intro h; subst r; rfl
  by_cases h2:r=2 <;> simp_all [registers]
 rw [hh]
 exact Steps.refl _
end C207Search.AXMacro
