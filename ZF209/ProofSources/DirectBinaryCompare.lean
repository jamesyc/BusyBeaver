module
public import DirectTypedNatUnary
@[expose] public section
namespace RosserDirect.BinaryCompare
open Turing Segment
set_option backward.isDefEq.respectTransparency false

def low (o : Ordering) (b c : Bool) : Ordering := if b = c then o else if b then .gt else .lt

def cmp (o : Ordering) : List Bool → List Bool → Ordering
 | [], [] => o
 | [], _ :: _ => .lt
 | _ :: _, [] => .gt
 | b :: bs, c :: cs => cmp (low o b c) bs cs

def order (o : Ordering) (n m : Nat) : Ordering := if n < m then .lt else if m < n then .gt else o

theorem low_order (o : Ordering) (b c : Bool) (n m : Nat) :
 order (low o b c) n m = order o (Nat.bit b n) (Nat.bit c m) := by
 cases o <;> cases b <;> cases c <;> simp [order,low,Nat.bit] <;> split_ifs <;> first | rfl | omega

theorem bits_ne_nil (n : Nat) (hn : n ≠ 0) : n.bits ≠ [] := by
 intro h
 have hf := fold_bits n
 rw [h] at hf
 exact hn hf.symm

theorem cmp_bits (n m : Nat) (o : Ordering) : cmp o n.bits m.bits = order o n m := by
 induction n using Nat.binaryRec' generalizing m o with
 | zero =>
   by_cases hm : m = 0
   · subst m; simp [Nat.zero_bits,cmp,order]
   · have hne := bits_ne_nil m hm
     cases h : m.bits with
     | nil => exact False.elim (hne h)
     | cons b bs => simp [Nat.zero_bits,cmp,order]; omega
 | bit b n hn ih =>
   rw [Nat.bits_append_bit n b hn]
   by_cases hm : m = 0
   · subst m
     have hpos : 0 < Nat.bit b n := by cases b <;> simp_all [Nat.bit] <;> omega
     simp [Nat.zero_bits,cmp,order,hpos]
   · have he : Nat.bit m.bodd m.div2 = m := Nat.bit_bodd_div2 m
     have hp : m.div2 = 0 → m.bodd = true := by
       intro hz
       cases hb : m.bodd
       · simp [hz,hb,Nat.bit] at he; omega
       · rfl
     have hb : m.bits = m.bodd :: m.div2.bits := by
       conv_lhs => rw [← he]
       exact Nat.bits_append_bit _ _ hp
     rw [hb,cmp,ih,low_order,he]

inductive Q where
 | scan (o : Ordering) | right (o : Ordering) (b : Bool) | leftEnd (o : Ordering)
 | skipLeft | skipRight | done (o : Ordering) | reject
 deriving DecidableEq, Fintype, Repr, Inhabited

def machine : Q → Stmt Q
 | .scan o => .pop .input (fun _ x => x)
   (.branch (fun x => x == some .tokenEnd) (.goto (fun _ => .leftEnd o))
    (.branch (fun x => x == some .bit0 || x == some .bit1)
     (.goto (fun x => .right o (x == some .bit1))) (.goto (fun _ => .reject))))
 | .right o b => .pop .output (fun _ x => x)
   (.branch (fun x => x == some .tokenEnd) (.goto (fun _ => .skipLeft))
    (.branch (fun x => x == some .bit0 || x == some .bit1)
     (.goto (fun x => .scan (low o b (x == some .bit1)))) (.goto (fun _ => .reject))))
 | .leftEnd o => .pop .output (fun _ x => x)
   (.branch (fun x => x == some .tokenEnd) (.load (fun _ => none) (.goto (fun _ => .done o)))
    (.branch (fun x => x == some .bit0 || x == some .bit1)
     (.goto (fun _ => .skipRight)) (.goto (fun _ => .reject))))
 | .skipLeft => .pop .input (fun _ x => x)
   (.branch (fun x => x == some .tokenEnd) (.load (fun _ => none) (.goto (fun _ => .done .gt)))
    (.branch (fun x => x == some .bit0 || x == some .bit1)
     (.goto (fun _ => .skipLeft)) (.goto (fun _ => .reject))))
 | .skipRight => .pop .output (fun _ x => x)
   (.branch (fun x => x == some .tokenEnd) (.load (fun _ => none) (.goto (fun _ => .done .lt)))
    (.branch (fun x => x == some .bit0 || x == some .bit1)
     (.goto (fun _ => .skipRight)) (.goto (fun _ => .reject))))
 | .done _ | .reject => .halt

theorem scan_bit (o : Ordering) (b : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config (.scan o) v (bitSymbol b :: a) s out) =
 some (config (.right o b) (some (bitSymbol b)) a s out) := by
 cases b <;> simp [machine,bitSymbol,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem scan_end (o : Ordering) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config (.scan o) v (.tokenEnd :: a) s out) =
 some (config (.leftEnd o) (some .tokenEnd) a s out) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 funext k; cases k <;> rfl

theorem right_bit (o : Ordering) (b c : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config (.right o b) v a s (bitSymbol c :: out)) =
 some (config (.scan (low o b c)) (some (bitSymbol c)) a s out) := by
 cases c <;> simp [machine,bitSymbol,config,TM2.step,TM2.stepAux,storage,Function.update,show (Symbol.bit0 == Symbol.bit1) = false from rfl]
 all_goals funext k; cases k <;> rfl

theorem right_end (o : Ordering) (b : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config (.right o b) v a s (.tokenEnd :: out)) =
 some (config .skipLeft (some .tokenEnd) a s out) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 funext k; cases k <;> rfl

theorem left_end_bit (o : Ordering) (c : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config (.leftEnd o) v a s (bitSymbol c :: out)) =
 some (config .skipRight (some (bitSymbol c)) a s out) := by
 cases c <;> simp [machine,bitSymbol,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem left_end_end (o : Ordering) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config (.leftEnd o) v a s (.tokenEnd :: out)) =
 some (config (.done o) none a s out) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 funext k; cases k <;> rfl

theorem skip_left_bit (b : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .skipLeft v (bitSymbol b :: a) s out) =
 some (config .skipLeft (some (bitSymbol b)) a s out) := by
 cases b <;> simp [machine,bitSymbol,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem skip_left_end (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .skipLeft v (.tokenEnd :: a) s out) =
 some (config (.done .gt) none a s out) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 funext k; cases k <;> rfl

theorem skip_right_bit (b : Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .skipRight v a s (bitSymbol b :: out)) =
 some (config .skipRight (some (bitSymbol b)) a s out) := by
 cases b <;> simp [machine,bitSymbol,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem skip_right_end (v : Option Symbol) (a s out : List Symbol) :
 TM2.step machine (config .skipRight v a s (.tokenEnd :: out)) =
 some (config (.done .lt) none a s out) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 funext k; cases k <;> rfl

theorem skip_left (bs : List Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.Reaches machine (config .skipLeft v (bs.map bitSymbol ++ .tokenEnd :: a) s out)
  (config (.done .gt) none a s out) := by
 induction bs generalizing v with
 | nil => exact Relation.ReflTransGen.single (skip_left_end v a s out)
 | cons b bs ih =>
   have one : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (skip_left_bit b v (bs.map bitSymbol ++ .tokenEnd :: a) s out)
   exact one.trans (ih (some (bitSymbol b)))

theorem skip_right (bs : List Bool) (v : Option Symbol) (a s out : List Symbol) :
 TM2.Reaches machine (config .skipRight v a s (bs.map bitSymbol ++ .tokenEnd :: out))
  (config (.done .lt) none a s out) := by
 induction bs generalizing v with
 | nil => exact Relation.ReflTransGen.single (skip_right_end v a s out)
 | cons b bs ih =>
   have one : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (skip_right_bit b v a s (bs.map bitSymbol ++ .tokenEnd :: out))
   exact one.trans (ih (some (bitSymbol b)))

theorem compare_bits (bs cs : List Bool) (o : Ordering) (v : Option Symbol) (a s out : List Symbol) :
 TM2.Reaches machine
  (config (.scan o) v (bs.map bitSymbol ++ .tokenEnd :: a) s (cs.map bitSymbol ++ .tokenEnd :: out))
  (config (.done (cmp o bs cs)) none a s out) := by
 induction bs generalizing cs o v with
 | nil =>
   have one : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (scan_end o v a s (cs.map bitSymbol ++ .tokenEnd :: out))
   cases cs with
   | nil => exact one.trans (Relation.ReflTransGen.single (left_end_end o (some .tokenEnd) a s out))
   | cons c cs =>
     have two : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (left_end_bit o c (some .tokenEnd) a s (cs.map bitSymbol ++ .tokenEnd :: out))
     exact one.trans (two.trans (skip_right cs (some (bitSymbol c)) a s out))
 | cons b bs ih =>
   have one : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (scan_bit o b v (bs.map bitSymbol ++ .tokenEnd :: a) s (cs.map bitSymbol ++ .tokenEnd :: out))
   cases cs with
   | nil =>
     have two : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (right_end o b (some (bitSymbol b)) (bs.map bitSymbol ++ .tokenEnd :: a) s out)
     exact one.trans (two.trans (skip_left bs (some .tokenEnd) a s out))
   | cons c cs =>
     have two : TM2.Reaches machine _ _ := Relation.ReflTransGen.single (right_bit o b c (some (bitSymbol b)) (bs.map bitSymbol ++ .tokenEnd :: a) s (cs.map bitSymbol ++ .tokenEnd :: out))
     exact one.trans (two.trans (ih cs (low o b c) (some (bitSymbol c))))

/-- Comparison consumes exactly one canonical numeral on either side, preserves
both suffixes and all scratch data; result is solely a finite control label. -/
theorem compare_nats (n m : Nat) (v : Option Symbol) (src scratch dst : List Symbol) :
 TM2.Reaches machine
  (config (.scan .eq) v (tokenBits n ++ src) scratch (tokenBits m ++ dst))
  (config (.done (order .eq n m)) none src scratch dst) := by
 simpa [TM2.Reaches,tokenBits,cmp_bits,List.append_assoc] using compare_bits n.bits m.bits .eq v src scratch dst

end RosserDirect.BinaryCompare
