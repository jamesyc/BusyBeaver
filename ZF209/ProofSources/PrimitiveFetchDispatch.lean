module
public import PrimitiveDispatch
@[expose] public section
namespace C209Search.Primitive.FetchDispatch
open M209.Source

def seed (n l : Nat) : Nat := if l=0 then n else l-1
def nextN (n l : Nat) : Nat := if l=0 then n+1 else n
def commandEntry (n l : Nat) (f : Registers) : Configuration :=
 let p := M6.Source.Cantor.decode (seed n l)
 ⟨Dispatch.target p.1,Fetch.registers (nextN n l) p.2 (p.1-2) f⟩

private theorem write_a (n l a b : Nat) (f : Registers) :
 write (Fetch.registers n l a f) 4 b = Fetch.registers n l b f := by
 funext r
 by_cases h1 : r=1 <;> by_cases h4 : r=4 <;> by_cases h8 : r=8 <;> by_cases h5 : r=5 <;>
 simp_all [write,Fetch.registers,Residual.registers]

theorem fetch_steps (n l : Nat) (f : Registers) :
 ∃m, 0<m ∧ Steps m (Fetch.start n l f) (Fetch.selected (nextN n l) (seed n l) f) := by
 cases l with
 | zero => exact ⟨_,by omega,Fetch.fresh n f⟩
 | succ l => exact ⟨2+Fetch.decodeCost l,by omega,Fetch.positive n l f⟩

/-- Concrete source dispatch reaches exactly S, MP or AX with the selector
minus two. This still precedes parsing each command's additional arguments. -/
theorem total (n l : Nat) (f : Registers) :
 ∃m, 0<m ∧ Steps m (Fetch.start n l f) (commandEntry n l f) := by
 obtain ⟨m,hm,hfetch⟩ := fetch_steps n l f
 have hd := Dispatch.total (M6.Source.Cantor.decode (seed n l)).1
  (Fetch.registers (nextN n l) (M6.Source.Cantor.decode (seed n l)).2
   (M6.Source.Cantor.decode (seed n l)).1 f)
  (by simp [Fetch.registers,Residual.registers])
 rw [write_a] at hd
 exact ⟨_,by omega,steps_trans hfetch hd⟩
end C209Search.Primitive.FetchDispatch
