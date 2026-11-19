module
public import DirectTypedFrames
public import DirectFrameEquality
@[expose] public section
namespace RosserDirect

def readTokenBits : List Symbol → List Bool × List Symbol
 | .bit0 :: xs => let (bs,rest) := readTokenBits xs; (false :: bs,rest)
 | .bit1 :: xs => let (bs,rest) := readTokenBits xs; (true :: bs,rest)
 | .tokenEnd :: xs => ([],xs)
 | xs => ([],xs)

theorem read_bits (bs : List Bool) (rest : List Symbol) :
 readTokenBits (bs.map bitSymbol ++ .tokenEnd :: rest) = (bs,rest) := by
 induction bs with
 | nil => rfl
 | cons b bs ih => cases b <;> simp [List.map, bitSymbol, readTokenBits, ih]

theorem read_token (n : Nat) (rest : List Symbol) :
 readTokenBits (tokenBits n ++ rest) = (n.bits,rest) := by
 simpa [tokenBits, List.append_assoc] using read_bits n.bits rest

theorem fold_bits (n : Nat) : n.bits.foldr Nat.bit 0 = n := by
 induction n using Nat.binaryRec' with
 | zero => rfl
 | bit b n h ih => simp [Nat.bits_append_bit _ _ h, ih]

theorem bits_injective : Function.Injective Nat.bits := by
 intro a b h
 have hf := congrArg (fun l => l.foldr Nat.bit 0) h
 simpa only [fold_bits] using hf

theorem payloadBits_injective : Function.Injective payloadBits := by
 intro xs
 induction xs with
 | nil =>
   intro ys h
   cases ys with
   | nil => rfl
   | cons y ys =>
     have hl := congrArg List.length h
     simp [payloadBits, tokenBits] at hl
 | cons x xs ih =>
   intro ys h
   cases ys with
   | nil =>
     have hl := congrArg List.length h
     simp [payloadBits, tokenBits] at hl
   | cons y ys =>
     have hr := congrArg readTokenBits h
     simp only [payloadBits, List.flatMap_cons, read_token] at hr
     have hxy := bits_injective (congrArg Prod.fst hr)
     have hrest := congrArg Prod.snd hr
     exact congrArg₂ List.cons hxy (ih hrest)

theorem emitFormula_injective : Function.Injective ZFR.TokenVM.emitFormula := by
 intro a b h
 have hr := congrArg (fun ts => ZFR.TokenVM.run ts []) h
 simpa using hr

end RosserDirect
