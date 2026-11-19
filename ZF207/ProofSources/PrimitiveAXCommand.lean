module
public import AXPrefixCertificate
public import PrimitiveAXGate
@[expose] public section
namespace C207Search.Primitive.AXCommand
open M207.Source C207Soundness

def input (t a d h x y tail : Nat) : AXMacro.Store :=
 ⟨t,a,d,h,M6.Source.Cantor.pair y (M6.Source.Cantor.pair x tail),[]⟩
def result (t a d h x y tail : Nat) : AXMacro.Store :=
 ⟨C207Search.gate a (d+x) (h+y),0,0,0,tail,
  C207Search.heads a (d+x) (h+y) d h ++ [t]⟩

private theorem gate_registers (s : AXMacro.Store) (t a d h bottom : Nat) (f : Registers) :
 AXGate.registers ⟨t,a,d,h,0,0,AXMacro.registers s bottom f⟩ =
 AXMacro.registers {s with t:=t,a:=a,d:=d,h:=h} bottom f := by
 funext r
 by_cases h0:r=0 <;> by_cases h1:r=1 <;> by_cases h2:r=2 <;>
 by_cases h3:r=3 <;> by_cases h4:r=4 <;> by_cases h5:r=5 <;>
 by_cases h7:r=7 <;> by_cases h8:r=8 <;>
 simp_all [AXMacro.registers,AXGate.registers]

/-- Full literal AX source branch50–4221 followed by actual return4328→25.
Its 305 arithmetic primitives implement exactly six heads, restrictedrho8,
saved universal, saved T, and the guarded pointed gate. -/
theorem command (t a d h x y tail w : Nat) (f : Registers) :
 ∃n,0<n ∧ Steps n
  (AXMacro.configAt 50 (input t a d h x y tail) w f)
  (AXMacro.configAt 25 (result t a d h x y tail) w f) := by
 have hs := AXSymbolic.macro_actual t a d h y x tail
 obtain ⟨n,hn,hprefix⟩ := AXMacro.certificate_sound AXMacro.prefix_certificate hs w f
 have hp : AXMacro.program ≠ [] := by decide +kernel
 have hn' := hn hp
 obtain ⟨m,hm,hgate⟩ := AXGate.gate_fetch (pointedGateCode a (d+x) (h+y)) a (d+x) (h+y)
  (AXMacro.registers
   ⟨pointedGateCode a (d+x) (h+y),a,d+x,h+y,tail,
    C207Search.heads a (d+x) (h+y) d h ++ [t]⟩ w f)
 simp only [AXGate.configAt,gate_registers] at hgate
 refine ⟨n+m,by omega,?_⟩
 exact steps_trans hprefix hgate

theorem run_command (t a d h x y tail w : Nat) (f : Registers) :
 ∃n,0<n ∧ runSource n
  (AXMacro.configAt 50 (input t a d h x y tail) w f) =
  some (AXMacro.configAt 25 (result t a d h x y tail) w f) := by
 obtain ⟨n,hn,hs⟩ := command t a d h x y tail w f
 refine ⟨n,hn,steps_real _ _ _ hs ?_⟩
 have row : M207.Source.program 25 = some (.dec 1 27 26) := by decide +kernel
 unfold scalarNext AXMacro.configAt
 rw [row]
 simp only [Option.bind_some,scalarExecute]
 split <;> simp
end C207Search.Primitive.AXCommand
