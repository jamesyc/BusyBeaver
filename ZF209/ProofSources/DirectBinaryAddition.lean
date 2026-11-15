module
public import DirectBinaryCompare
@[expose] public section
namespace RosserDirect.BinaryAddition
open Turing Segment
set_option backward.isDefEq.respectTransparency false

def sumBit (a b c : Bool) : Bool := xor (xor a b) c
def carry (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)
def one (c : Bool) (bs : List Bool) : List Bool := if c then BinarySuccessor.inc bs else bs

def add (c : Bool) : List Bool → List Bool → List Bool
 | [], bs => one c bs
 | bs, [] => one c bs
 | a :: as, b :: bs => sumBit a b c :: add (carry a b c) as bs

theorem one_bits (c : Bool) (n : Nat) : one c n.bits = (n+c.toNat).bits := by
 cases c <;> simp [one,BinarySuccessor.inc_bits]

theorem add_bits (c : Bool) (n m : Nat) : add c n.bits m.bits = (n+m+c.toNat).bits := by
 induction n using Nat.binaryRec' generalizing m c with
 | zero => simpa [Nat.zero_bits,add] using one_bits c m
 | bit b n hn ih =>
   rw [Nat.bits_append_bit n b hn]
   by_cases hm : m = 0
   · subst m
     simp only [Nat.zero_bits]
     change one c (b :: n.bits) = (Nat.bit b n + 0 + c.toNat).bits
     simpa only [Nat.add_zero,← Nat.bits_append_bit n b hn] using one_bits c (Nat.bit b n)
   · have he : Nat.bit m.bodd m.div2 = m := Nat.bit_bodd_div2 m
     have hp : m.div2 = 0 → m.bodd = true := by
       intro hz
       cases hb : m.bodd
       · simp [hz,hb,Nat.bit] at he; omega
       · rfl
     have hb : m.bits = m.bodd :: m.div2.bits := by
       conv_lhs => rw [← he]
       exact Nat.bits_append_bit _ _ hp
     rw [hb,add,ih]
     have harith : Nat.bit b n + Nat.bit m.bodd m.div2 + c.toNat =
       Nat.bit (sumBit b m.bodd c) (n + m.div2 + (carry b m.bodd c).toNat) := by
       cases b <;> cases h : m.bodd <;> cases c <;> simp [sumBit,carry,Nat.bit] <;> omega
     have hcanon : n + m.div2 + (carry b m.bodd c).toNat = 0 → sumBit b m.bodd c = true := by
       cases b <;> cases h : m.bodd <;> cases c <;> simp_all [sumBit,carry] <;> omega
     conv_rhs => rw [← he,harith,Nat.bits_append_bit _ _ hcanon]



theorem one_cons (c b : Bool) (bs : List Bool) :
 one c (b :: bs) = xor b c :: one (b && c) bs := by
 cases c <;> cases b <;> rfl

inductive Q where
 | scan (c : Bool) | right (c b : Bool) | leftOnly (c : Bool) | rightOnly (c : Bool)
 | flush | done | reject
 deriving DecidableEq, Fintype, Inhabited

def finish (c : Bool) : Stmt Q :=
 if c then .push .scratch (fun _ => .bit1) (.push .scratch (fun _ => .tokenEnd) (.goto (fun _ => .flush)))
 else .push .scratch (fun _ => .tokenEnd) (.goto (fun _ => .flush))

def machine : Q → Stmt Q
 | .scan c => .pop .input (fun _ x => x)
   (.branch (fun x => x == some .tokenEnd) (.goto (fun _ => .rightOnly c))
    (.branch (fun x => x == some .bit0 || x == some .bit1)
     (.goto (fun x => .right c (x == some .bit1))) (.goto (fun _ => .reject))))
 | .right c b => .pop .output (fun _ x => x)
   (.branch (fun x => x == some .tokenEnd)
     (.push .scratch (fun _ => bitSymbol (xor b c)) (.goto (fun _ => .leftOnly (b && c))))
     (.branch (fun x => x == some .bit0 || x == some .bit1)
      (.push .scratch (fun x => bitSymbol (sumBit b (x == some .bit1) c))
       (.goto (fun x => .scan (carry b (x == some .bit1) c)))) (.goto (fun _ => .reject))))
 | .leftOnly c => .pop .input (fun _ x => x)
   (.branch (fun x => x == some .tokenEnd) (finish c)
    (.branch (fun x => x == some .bit0 || x == some .bit1)
     (.push .scratch (fun x => bitSymbol (xor (x == some .bit1) c))
      (.goto (fun x => .leftOnly ((x == some .bit1) && c)))) (.goto (fun _ => .reject))))
 | .rightOnly c => .pop .output (fun _ x => x)
   (.branch (fun x => x == some .tokenEnd) (finish c)
    (.branch (fun x => x == some .bit0 || x == some .bit1)
     (.push .scratch (fun x => bitSymbol (xor (x == some .bit1) c))
      (.goto (fun x => .rightOnly ((x == some .bit1) && c)))) (.goto (fun _ => .reject))))
 | .flush => flushStmt .flush .done
 | .done | .reject => .halt

@[simp] theorem bit0_beq_bit1 : (Symbol.bit0 == Symbol.bit1) = false := by decide

theorem scan_bit (c b : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config (.scan c) v (bitSymbol b :: a) s out) =
 some (config (.right c b) (some (bitSymbol b)) a s out) := by
 cases b <;> simp [machine,bitSymbol,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem scan_end (c : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config (.scan c) v (.tokenEnd :: a) s out) =
 some (config (.rightOnly c) (some .tokenEnd) a s out) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage]
 funext k; cases k <;> rfl

theorem right_bit (c b d : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config (.right c b) v a s (bitSymbol d :: out)) =
 some (config (.scan (carry b d c)) (some (bitSymbol d)) a (bitSymbol (sumBit b d c) :: s) out) := by
 cases d <;> simp [machine,bitSymbol,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem right_end (c b : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config (.right c b) v a s (.tokenEnd :: out)) =
 some (config (.leftOnly (b && c)) (some .tokenEnd) a (bitSymbol (xor b c) :: s) out) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage]
 funext k; cases k <;> rfl

theorem left_bit (c b : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config (.leftOnly c) v (bitSymbol b :: a) s out) =
 some (config (.leftOnly (b && c)) (some (bitSymbol b)) a (bitSymbol (xor b c) :: s) out) := by
 cases b <;> simp [machine,bitSymbol,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem only_right_bit (c b : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config (.rightOnly c) v a s (bitSymbol b :: out)) =
 some (config (.rightOnly (b && c)) (some (bitSymbol b)) a (bitSymbol (xor b c) :: s) out) := by
 cases b <;> simp [machine,bitSymbol,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem left_end (c : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config (.leftOnly c) v (.tokenEnd :: a) s out) =
 some (config .flush (some .tokenEnd) a (.tokenEnd :: (((one c []).map bitSymbol).reverse ++ s)) out) := by
 cases c <;> simp [machine,finish,one,BinarySuccessor.inc,bitSymbol,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem only_right_end (c : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config (.rightOnly c) v a s (.tokenEnd :: out)) =
 some (config .flush (some .tokenEnd) a (.tokenEnd :: (((one c []).map bitSymbol).reverse ++ s)) out) := by
 cases c <;> simp [machine,finish,one,BinarySuccessor.inc,bitSymbol,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem left_run (bs : List Bool) (c : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.Reaches machine (config (.leftOnly c) v (bs.map bitSymbol ++ .tokenEnd :: a) s out)
 (config .flush (some .tokenEnd) a (.tokenEnd :: (((one c bs).map bitSymbol).reverse ++ s)) out) := by
 induction bs generalizing c v s with
 | nil => exact TypedContext.reach_step (left_end c v a s out)
 | cons b bs ih =>
   have h := TypedContext.reach_step (left_bit c b v (bs.map bitSymbol ++ .tokenEnd :: a) s out)
   simpa [TM2.Reaches,one_cons,List.reverse_cons,List.append_assoc] using
     h.trans (ih (b && c) (some (bitSymbol b)) (bitSymbol (xor b c) :: s))

theorem right_run (bs : List Bool) (c : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.Reaches machine (config (.rightOnly c) v a s (bs.map bitSymbol ++ .tokenEnd :: out))
 (config .flush (some .tokenEnd) a (.tokenEnd :: (((one c bs).map bitSymbol).reverse ++ s)) out) := by
 induction bs generalizing c v s with
 | nil => exact TypedContext.reach_step (only_right_end c v a s out)
 | cons b bs ih =>
   have h := TypedContext.reach_step (only_right_bit c b v a s (bs.map bitSymbol ++ .tokenEnd :: out))
   simpa [TM2.Reaches,one_cons,List.reverse_cons,List.append_assoc] using
     h.trans (ih (b && c) (some (bitSymbol b)) (bitSymbol (xor b c) :: s))

theorem scan_run (as bs : List Bool) (c : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.Reaches machine (config (.scan c) v (as.map bitSymbol ++ .tokenEnd :: a) s (bs.map bitSymbol ++ .tokenEnd :: out))
 (config .flush (some .tokenEnd) a (.tokenEnd :: (((add c as bs).map bitSymbol).reverse ++ s)) out) := by
 induction as generalizing bs c v s with
 | nil =>
   have h := TypedContext.reach_step (scan_end c v a s (bs.map bitSymbol ++ .tokenEnd :: out))
   simpa [TM2.Reaches,add] using h.trans (right_run bs c (some .tokenEnd) a s out)
 | cons b as ih =>
   have h0 := TypedContext.reach_step (scan_bit c b v (as.map bitSymbol ++ .tokenEnd :: a) s (bs.map bitSymbol ++ .tokenEnd :: out))
   cases bs with
   | nil =>
     have h1 := TypedContext.reach_step (right_end c b (some (bitSymbol b)) (as.map bitSymbol ++ .tokenEnd :: a) s out)
     have h2 := left_run as (b && c) (some .tokenEnd) a (bitSymbol (xor b c) :: s) out
     simpa [TM2.Reaches,add,one_cons,List.reverse_cons,List.append_assoc] using h0.trans (h1.trans h2)
   | cons d bs =>
     have h1 := TypedContext.reach_step (right_bit c b d (some (bitSymbol b)) (as.map bitSymbol ++ .tokenEnd :: a) s (bs.map bitSymbol ++ .tokenEnd :: out))
     have h2 := ih bs (carry b d c) (some (bitSymbol d)) (bitSymbol (sumBit b d c) :: s)
     simpa [TM2.Reaches,add,List.reverse_cons,List.append_assoc] using h0.trans (h1.trans h2)

/-- Linear binary addition over two canonical little-endian tokens. Both input
numbers are consumed; arbitrary tails remain intact and scratch is emptied. -/
theorem addition (n m : Nat) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine (config (.scan false) v (tokenBits n ++ src) [] (tokenBits m ++ dst))
 (config .done none src [] (tokenBits (n+m) ++ dst)) := by
 have h := (scan_run n.bits m.bits false v src [] dst).trans
   (Segment.flush_frame machine .flush .done rfl (some .tokenEnd) src
    (.tokenEnd :: (((add false n.bits m.bits).map bitSymbol).reverse ++ [])) dst)
 simpa [TM2.Reaches,tokenBits,add_bits,List.reverse_cons,List.append_assoc] using h

end RosserDirect.BinaryAddition
