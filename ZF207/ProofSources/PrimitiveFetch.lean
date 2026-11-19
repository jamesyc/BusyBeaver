module
public import PrimitiveFetchPrefix
@[expose] public section
namespace C207Search.Primitive.Fetch
open M207.Source

def registers (n l a : Nat) (f : Registers) : Registers :=
 Residual.registers ⟨l,a,0,0,write f 6 n⟩
def start (n l : Nat) (f : Registers) : Configuration := ⟨25, registers n l 0 f⟩
def selected (n seed : Nat) (f : Registers) : Configuration :=
 ⟨48, registers n (M6.Source.Cantor.decode seed).2 (M6.Source.Cantor.decode seed).1 f⟩

def decodeCost (seed : Nat) : Nat :=
 Residual.loopCost seed (0,0) + (3*(M6.Source.Cantor.decode seed).2+1) +
 (3*(M6.Source.Cantor.decode seed).1+1)

private theorem bridge (n l : Nat) (f : Registers) :
 FetchPrefix.registers ⟨n,l,0,Residual.registers ⟨0,0,0,0,f⟩⟩ = registers n l 0 f := by
 funext r
 by_cases h0 : r=6 <;> by_cases h1 : r=1 <;> by_cases h4 : r=4 <;>
 by_cases h8 : r=8 <;> by_cases h5 : r=5 <;>
 simp_all [FetchPrefix.registers,Residual.registers,registers,write]

theorem positive (n l : Nat) (f : Registers) :
 Steps (2+decodeCost l) (start n (l+1) f) (selected n l f) := by
 have hp := FetchPrefix.positive n l (Residual.registers ⟨0,0,0,0,f⟩)
 simp only [FetchPrefix.configAt,bridge] at hp
 exact steps_trans hp (Residual.unpair l (write f 6 n))

theorem fresh (n : Nat) (f : Registers) :
 Steps (7*n+4+decodeCost n) (start n 0 f) (selected (n+1) n f) := by
 have hp := FetchPrefix.fresh n (Residual.registers ⟨0,0,0,0,f⟩)
 simp only [FetchPrefix.configAt,bridge] at hp
 exact steps_trans hp (Residual.unpair n (write f 6 (n+1)))

private theorem row48 : program 48 = some (.dec 4 4329 49) := by decide +kernel
end C207Search.Primitive.Fetch
