module
public import PrimitivePopCore
public import PrimitiveTimesFour
public import SearchCommands
@[expose] public section
namespace C209Search.Primitive.ConsCore
open M209.Source
private theorem registers_bridge (t w x y : Nat) (f : Registers) :
 PopCore.registers ⟨w,f 7,x,y,write f 2 t⟩ = PairCore.registers ⟨t,w,x,y,f⟩ := by
 funext r
 by_cases h0:r=0 <;> by_cases h2:r=2 <;> by_cases h5:r=5 <;> by_cases h7:r=7 <;> by_cases h8:r=8 <;>
 simp_all [PopCore.registers,PairCore.registers,write]

theorem cons {offset : Nat} (hp : PopCore.Bound offset)
 (hq : PairCore.Bound (offset+11)) (hfour : TimesFour.Bound (offset+21))
 (t w : Nat) (f : Registers) :
 ∃ n, 0<n ∧ Steps n (PairCore.configAt offset 0 ⟨t,w,0,0,f⟩)
 (PairCore.configAt offset 27 ⟨C209Soundness.impCode (M6.Source.Cantor.decode w).1 t,(M6.Source.Cantor.decode w).2,0,0,f⟩) := by
 have a := PopCore.decode_prefix hp w (f 7) (write f 2 t)
 have aa : Steps (PopCore.loopCost w (0,0)+(3*(M6.Source.Cantor.decode w).2+1))
  (PairCore.configAt offset 0 ⟨t,w,0,0,f⟩)
  (PairCore.configAt (offset+11) 0 ⟨t,(M6.Source.Cantor.decode w).2,(M6.Source.Cantor.decode w).1,0,f⟩) := by
  simpa only [PopCore.configAt,PairCore.configAt,registers_bridge,Nat.add_zero] using a
 obtain ⟨n,hn,hb⟩ := PairCore.pair hq t (M6.Source.Cantor.decode w).2 (M6.Source.Cantor.decode w).1 f
 have c := TimesFour.times4 hfour 0 (M6.Source.Cantor.decode w).2 0 (M6.Source.Cantor.pair (M6.Source.Cantor.decode w).1 t) f
 have cc : Steps (6*M6.Source.Cantor.pair (M6.Source.Cantor.decode w).1 t+1)
  (PairCore.configAt (offset+11) 10 ⟨0,(M6.Source.Cantor.decode w).2,0,M6.Source.Cantor.pair (M6.Source.Cantor.decode w).1 t,f⟩)
  (PairCore.configAt offset 27 ⟨C209Soundness.impCode (M6.Source.Cantor.decode w).1 t,(M6.Source.Cantor.decode w).2,0,0,f⟩) := by
  simpa only [TimesFour.configAt,PairCore.configAt,Nat.add_assoc,Nat.reduceAdd,Nat.add_zero,C209Soundness.impCode,C209Search.pair_eq_cantor,Nat.zero_add] using c
 exact ⟨_,by omega,steps_trans (steps_trans aa hb) cc⟩
end C209Search.Primitive.ConsCore
