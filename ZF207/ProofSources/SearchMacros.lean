module
public import SearchCommands
@[expose] public section
namespace C207Search
open C207Soundness M6.Source.Cantor M6.Source.Enumeration
set_option maxRecDepth 100000
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false

def POP : List Command := [.ax 0 0 0] ++ List.replicate 10 .shift
def PUSH : List Command := [.ax 0 0 0] ++ List.replicate 8 .shift ++ [.mp 0]
def DISCARD : List Command := [.mp 1,.ax 1 0 0] ++ List.replicate 9 .shift ++ [.mp 0]
def J (u : Nat) : List Command := if u=0 then [] else [.mp u]
def POPs : Nat → List Command
 | 0 => []
 | n+1 => POP ++ POPs n

theorem ax_step (a x y : Nat) (s : CommandStore) :
 commandEval (.ax a x y) s = some ⟨gate a (s.d+x) (s.h+y),
 (heads a (s.d+x) (s.h+y) s.d s.h ++ [s.t]).foldr pair s.w,0,0⟩ := rfl

@[simp] theorem imp_ne_one (a b : Nat) : impCode a b ≠ 1 := by unfold impCode; omega
@[simp] theorem imp_sum_ne_one (a b c d : Nat) : impCode a b + impCode c d ≠ 1 := by unfold impCode; omega
@[simp] theorem all_add_ne_one (i a b : Nat) : allCode i a+b ≠ 1 := by unfold allCode; omega
@[simp] theorem add_all_ne_one (i a b : Nat) : b+allCode i a ≠ 1 := by unfold allCode; omega
@[simp] theorem imp_ne_all (a b i c : Nat) : impCode a b ≠ allCode i c := by unfold impCode allCode; omega
@[simp] theorem gate_ne_one (a d h : Nat) : gate a d h ≠ 1 := by
 unfold gate
 split
 · unfold pointedGateCode
   exact imp_ne_one _ _
 · decide

@[simp] theorem imp_one_ne_zero (t : Nat) : impCode t 1 ≠ 0 := by
 have h := cantor_ge_right t 1
 unfold impCode
 omega
@[simp] theorem imp_all_zero_ne_zero (i a : Nat) : impCode (allCode i a) 0 ≠ 0 := by
 have h := cantor_ge_left (allCode i a) 0
 have h2 : 2 ≤ allCode i a := by unfold allCode; omega
 unfold impCode
 omega


@[simp] theorem imp_mod4 (a b : Nat) : impCode a b % 4 = 0 := by simp [impCode]
@[simp] theorem all_mod4 (i a : Nat) : allCode i a % 4 = 2 := by simp [allCode]
theorem gate_mod4 (a d h : Nat) : gate a d h % 4 = 0 := by
 unfold gate
 split
 · unfold pointedGateCode
   exact imp_mod4 _ _
 · decide
theorem head1_mod4 (a d h : Nat) : head1Code a d h % 4 = 0 := imp_mod4 _ _
theorem head2_mod4 (a d h : Nat) : head2Code a d h % 4 = 0 := imp_mod4 _ _
theorem head3_mod4 (a d h : Nat) : head3Code a d h % 4 = 0 := imp_mod4 _ _
theorem head4_mod4 (a d h : Nat) : head4Code a d h % 4 = 0 := imp_mod4 _ _
theorem head5_mod4 (a d h : Nat) : head5Code a d h % 4 = 0 := imp_mod4 _ _
theorem head6_mod4 (a d h : Nat) : head6Code a d h % 4 = 0 := imp_mod4 _ _
theorem rho_mod4 (a d h u : Nat) : rho8Code a d h u % 4 = 0 := imp_mod4 _ _

private theorem scaffold_shift2 (g x1 x2 x3 x4 x5 x6 r q t w : Nat)
 (hg : g%4=0) (h1 : x1%4=0) (h2 : x2%4=0) (h3 : x3%4=0)
 (h4 : x4%4=0) (h5 : x5%4=0) (h6 : x6%4=0) (hr : r%4=0) (hq : q%4=2) :
 commandsEval (List.replicate 2 .shift) ⟨g,[x1,x2,x3,x4,x5,x6,r,q,t].foldr pair w,0,0⟩ =
 some ⟨x1,[x3,x4,x5,x6,r,q,t].foldr pair w,0,x2⟩ := by
 have e0 : g ≠ 1 := by omega
 have e1 : x1 ≠ 1 := by omega
 have e2 : x1+x2 ≠ 1 := by omega
 have e3 : x2+x3 ≠ 1 := by omega
 have e4 : x3+x4 ≠ 1 := by omega
 have e5 : x4+x5 ≠ 1 := by omega
 have e6 : x5+x6 ≠ 1 := by omega
 have e7 : x6+r ≠ 1 := by omega
 have e8 : r+q ≠ 1 := by omega
 have e9 : q+t ≠ 1 := by omega
 simp only [List.replicate_succ,List.replicate_zero,List.foldr_cons,List.foldr_nil,
 commandsEval,commandEval,decode_pair,Nat.add_zero,Nat.zero_add,e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,ite_false,Option.bind_some]

private theorem scaffold_shift3 (g x1 x2 x3 x4 x5 x6 r q t w : Nat)
 (hg : g%4=0) (h1 : x1%4=0) (h2 : x2%4=0) (h3 : x3%4=0)
 (h4 : x4%4=0) (h5 : x5%4=0) (h6 : x6%4=0) (hr : r%4=0) (hq : q%4=2) :
 commandsEval (List.replicate 3 .shift) ⟨g,[x1,x2,x3,x4,x5,x6,r,q,t].foldr pair w,0,0⟩ =
 some ⟨x2,[x4,x5,x6,r,q,t].foldr pair w,0,x3⟩ := by
 have e0 : g ≠ 1 := by omega
 have e1 : x1 ≠ 1 := by omega
 have e2 : x1+x2 ≠ 1 := by omega
 have e3 : x2+x3 ≠ 1 := by omega
 have e4 : x3+x4 ≠ 1 := by omega
 have e5 : x4+x5 ≠ 1 := by omega
 have e6 : x5+x6 ≠ 1 := by omega
 have e7 : x6+r ≠ 1 := by omega
 have e8 : r+q ≠ 1 := by omega
 have e9 : q+t ≠ 1 := by omega
 simp only [List.replicate_succ,List.replicate_zero,List.foldr_cons,List.foldr_nil,
 commandsEval,commandEval,decode_pair,Nat.add_zero,Nat.zero_add,e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,ite_false,Option.bind_some]

private theorem scaffold_shift4 (g x1 x2 x3 x4 x5 x6 r q t w : Nat)
 (hg : g%4=0) (h1 : x1%4=0) (h2 : x2%4=0) (h3 : x3%4=0)
 (h4 : x4%4=0) (h5 : x5%4=0) (h6 : x6%4=0) (hr : r%4=0) (hq : q%4=2) :
 commandsEval (List.replicate 4 .shift) ⟨g,[x1,x2,x3,x4,x5,x6,r,q,t].foldr pair w,0,0⟩ =
 some ⟨x3,[x5,x6,r,q,t].foldr pair w,0,x4⟩ := by
 have e0 : g ≠ 1 := by omega
 have e1 : x1 ≠ 1 := by omega
 have e2 : x1+x2 ≠ 1 := by omega
 have e3 : x2+x3 ≠ 1 := by omega
 have e4 : x3+x4 ≠ 1 := by omega
 have e5 : x4+x5 ≠ 1 := by omega
 have e6 : x5+x6 ≠ 1 := by omega
 have e7 : x6+r ≠ 1 := by omega
 have e8 : r+q ≠ 1 := by omega
 have e9 : q+t ≠ 1 := by omega
 simp only [List.replicate_succ,List.replicate_zero,List.foldr_cons,List.foldr_nil,
 commandsEval,commandEval,decode_pair,Nat.add_zero,Nat.zero_add,e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,ite_false,Option.bind_some]

private theorem scaffold_shift5 (g x1 x2 x3 x4 x5 x6 r q t w : Nat)
 (hg : g%4=0) (h1 : x1%4=0) (h2 : x2%4=0) (h3 : x3%4=0)
 (h4 : x4%4=0) (h5 : x5%4=0) (h6 : x6%4=0) (hr : r%4=0) (hq : q%4=2) :
 commandsEval (List.replicate 5 .shift) ⟨g,[x1,x2,x3,x4,x5,x6,r,q,t].foldr pair w,0,0⟩ =
 some ⟨x4,[x6,r,q,t].foldr pair w,0,x5⟩ := by
 have e0 : g ≠ 1 := by omega
 have e1 : x1 ≠ 1 := by omega
 have e2 : x1+x2 ≠ 1 := by omega
 have e3 : x2+x3 ≠ 1 := by omega
 have e4 : x3+x4 ≠ 1 := by omega
 have e5 : x4+x5 ≠ 1 := by omega
 have e6 : x5+x6 ≠ 1 := by omega
 have e7 : x6+r ≠ 1 := by omega
 have e8 : r+q ≠ 1 := by omega
 have e9 : q+t ≠ 1 := by omega
 simp only [List.replicate_succ,List.replicate_zero,List.foldr_cons,List.foldr_nil,
 commandsEval,commandEval,decode_pair,Nat.add_zero,Nat.zero_add,e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,ite_false,Option.bind_some]

private theorem scaffold_shift6 (g x1 x2 x3 x4 x5 x6 r q t w : Nat)
 (hg : g%4=0) (h1 : x1%4=0) (h2 : x2%4=0) (h3 : x3%4=0)
 (h4 : x4%4=0) (h5 : x5%4=0) (h6 : x6%4=0) (hr : r%4=0) (hq : q%4=2) :
 commandsEval (List.replicate 6 .shift) ⟨g,[x1,x2,x3,x4,x5,x6,r,q,t].foldr pair w,0,0⟩ =
 some ⟨x5,[r,q,t].foldr pair w,0,x6⟩ := by
 have e0 : g ≠ 1 := by omega
 have e1 : x1 ≠ 1 := by omega
 have e2 : x1+x2 ≠ 1 := by omega
 have e3 : x2+x3 ≠ 1 := by omega
 have e4 : x3+x4 ≠ 1 := by omega
 have e5 : x4+x5 ≠ 1 := by omega
 have e6 : x5+x6 ≠ 1 := by omega
 have e7 : x6+r ≠ 1 := by omega
 have e8 : r+q ≠ 1 := by omega
 have e9 : q+t ≠ 1 := by omega
 simp only [List.replicate_succ,List.replicate_zero,List.foldr_cons,List.foldr_nil,
 commandsEval,commandEval,decode_pair,Nat.add_zero,Nat.zero_add,e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,ite_false,Option.bind_some]

private theorem scaffold_shift7 (g x1 x2 x3 x4 x5 x6 r q t w : Nat)
 (hg : g%4=0) (h1 : x1%4=0) (h2 : x2%4=0) (h3 : x3%4=0)
 (h4 : x4%4=0) (h5 : x5%4=0) (h6 : x6%4=0) (hr : r%4=0) (hq : q%4=2) :
 commandsEval (List.replicate 7 .shift) ⟨g,[x1,x2,x3,x4,x5,x6,r,q,t].foldr pair w,0,0⟩ =
 some ⟨x6,[q,t].foldr pair w,0,r⟩ := by
 have e0 : g ≠ 1 := by omega
 have e1 : x1 ≠ 1 := by omega
 have e2 : x1+x2 ≠ 1 := by omega
 have e3 : x2+x3 ≠ 1 := by omega
 have e4 : x3+x4 ≠ 1 := by omega
 have e5 : x4+x5 ≠ 1 := by omega
 have e6 : x5+x6 ≠ 1 := by omega
 have e7 : x6+r ≠ 1 := by omega
 have e8 : r+q ≠ 1 := by omega
 have e9 : q+t ≠ 1 := by omega
 simp only [List.replicate_succ,List.replicate_zero,List.foldr_cons,List.foldr_nil,
 commandsEval,commandEval,decode_pair,Nat.add_zero,Nat.zero_add,e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,ite_false,Option.bind_some]

private theorem scaffold_shift8 (g x1 x2 x3 x4 x5 x6 r q t w : Nat)
 (hg : g%4=0) (h1 : x1%4=0) (h2 : x2%4=0) (h3 : x3%4=0)
 (h4 : x4%4=0) (h5 : x5%4=0) (h6 : x6%4=0) (hr : r%4=0) (hq : q%4=2) :
 commandsEval (List.replicate 8 .shift) ⟨g,[x1,x2,x3,x4,x5,x6,r,q,t].foldr pair w,0,0⟩ =
 some ⟨r,[t].foldr pair w,0,q⟩ := by
 have e0 : g ≠ 1 := by omega
 have e1 : x1 ≠ 1 := by omega
 have e2 : x1+x2 ≠ 1 := by omega
 have e3 : x2+x3 ≠ 1 := by omega
 have e4 : x3+x4 ≠ 1 := by omega
 have e5 : x4+x5 ≠ 1 := by omega
 have e6 : x5+x6 ≠ 1 := by omega
 have e7 : x6+r ≠ 1 := by omega
 have e8 : r+q ≠ 1 := by omega
 have e9 : q+t ≠ 1 := by omega
 simp only [List.replicate_succ,List.replicate_zero,List.foldr_cons,List.foldr_nil,
 commandsEval,commandEval,decode_pair,Nat.add_zero,Nat.zero_add,e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,ite_false,Option.bind_some]

private theorem scaffold_shift9 (g x1 x2 x3 x4 x5 x6 r q t w : Nat)
 (hg : g%4=0) (h1 : x1%4=0) (h2 : x2%4=0) (h3 : x3%4=0)
 (h4 : x4%4=0) (h5 : x5%4=0) (h6 : x6%4=0) (hr : r%4=0) (hq : q%4=2) :
 commandsEval (List.replicate 9 .shift) ⟨g,[x1,x2,x3,x4,x5,x6,r,q,t].foldr pair w,0,0⟩ =
 some ⟨q,w,0,t⟩ := by
 have e0 : g ≠ 1 := by omega
 have e1 : x1 ≠ 1 := by omega
 have e2 : x1+x2 ≠ 1 := by omega
 have e3 : x2+x3 ≠ 1 := by omega
 have e4 : x3+x4 ≠ 1 := by omega
 have e5 : x4+x5 ≠ 1 := by omega
 have e6 : x5+x6 ≠ 1 := by omega
 have e7 : x6+r ≠ 1 := by omega
 have e8 : r+q ≠ 1 := by omega
 have e9 : q+t ≠ 1 := by omega
 simp only [List.replicate_succ,List.replicate_zero,List.foldr_cons,List.foldr_nil,
 commandsEval,commandEval,decode_pair,Nat.add_zero,Nat.zero_add,e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,ite_false,Option.bind_some]

private theorem scaffold_shift10 (g x1 x2 x3 x4 x5 x6 r q t w : Nat)
 (hg : g%4=0) (h1 : x1%4=0) (h2 : x2%4=0) (h3 : x3%4=0)
 (h4 : x4%4=0) (h5 : x5%4=0) (h6 : x6%4=0) (hr : r%4=0) (hq : q%4=2) :
 commandsEval (List.replicate 10 .shift) ⟨g,[x1,x2,x3,x4,x5,x6,r,q,t].foldr pair w,0,0⟩ =
 some ⟨t,(M6.Source.Cantor.decode w).2,0,(M6.Source.Cantor.decode w).1⟩ := by
 have e0 : g ≠ 1 := by omega
 have e1 : x1 ≠ 1 := by omega
 have e2 : x1+x2 ≠ 1 := by omega
 have e3 : x2+x3 ≠ 1 := by omega
 have e4 : x3+x4 ≠ 1 := by omega
 have e5 : x4+x5 ≠ 1 := by omega
 have e6 : x5+x6 ≠ 1 := by omega
 have e7 : x6+r ≠ 1 := by omega
 have e8 : r+q ≠ 1 := by omega
 have e9 : q+t ≠ 1 := by omega
 simp only [List.replicate_succ,List.replicate_zero,List.foldr_cons,List.foldr_nil,
 commandsEval,commandEval,decode_pair,Nat.add_zero,Nat.zero_add,e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,ite_false,Option.bind_some]

theorem AX_shift2 (a x y t w d h : Nat) :
 commandsEval ([.ax a x y] ++ List.replicate 2 .shift) ⟨t,w,d,h⟩ =
 some ⟨head1Code a (d+x) (h+y),[head3Code a (d+x) (h+y),head4Code a (d+x) (h+y),head5Code a (d+x) (h+y),head6Code a (d+x) (h+y),rho8Code a (d+x) (h+y) d,allCode d h,t].foldr pair w,0,head2Code a (d+x) (h+y)⟩ := by
 rw [commandsEval_append]
 change commandsEval (List.replicate 2 .shift) ⟨gate a (d+x) (h+y),
   (heads a (d+x) (h+y) d h ++ [t]).foldr pair w,0,0⟩ = _
 exact scaffold_shift2 _ _ _ _ _ _ _ _ _ _ _ (gate_mod4 _ _ _) (head1_mod4 _ _ _)
  (head2_mod4 _ _ _) (head3_mod4 _ _ _) (head4_mod4 _ _ _) (head5_mod4 _ _ _) (head6_mod4 _ _ _)
  (rho_mod4 _ _ _ _) (all_mod4 _ _)

theorem AX_shift3 (a x y t w d h : Nat) :
 commandsEval ([.ax a x y] ++ List.replicate 3 .shift) ⟨t,w,d,h⟩ =
 some ⟨head2Code a (d+x) (h+y),[head4Code a (d+x) (h+y),head5Code a (d+x) (h+y),head6Code a (d+x) (h+y),rho8Code a (d+x) (h+y) d,allCode d h,t].foldr pair w,0,head3Code a (d+x) (h+y)⟩ := by
 rw [commandsEval_append]
 change commandsEval (List.replicate 3 .shift) ⟨gate a (d+x) (h+y),
   (heads a (d+x) (h+y) d h ++ [t]).foldr pair w,0,0⟩ = _
 exact scaffold_shift3 _ _ _ _ _ _ _ _ _ _ _ (gate_mod4 _ _ _) (head1_mod4 _ _ _)
  (head2_mod4 _ _ _) (head3_mod4 _ _ _) (head4_mod4 _ _ _) (head5_mod4 _ _ _) (head6_mod4 _ _ _)
  (rho_mod4 _ _ _ _) (all_mod4 _ _)

theorem AX_shift4 (a x y t w d h : Nat) :
 commandsEval ([.ax a x y] ++ List.replicate 4 .shift) ⟨t,w,d,h⟩ =
 some ⟨head3Code a (d+x) (h+y),[head5Code a (d+x) (h+y),head6Code a (d+x) (h+y),rho8Code a (d+x) (h+y) d,allCode d h,t].foldr pair w,0,head4Code a (d+x) (h+y)⟩ := by
 rw [commandsEval_append]
 change commandsEval (List.replicate 4 .shift) ⟨gate a (d+x) (h+y),
   (heads a (d+x) (h+y) d h ++ [t]).foldr pair w,0,0⟩ = _
 exact scaffold_shift4 _ _ _ _ _ _ _ _ _ _ _ (gate_mod4 _ _ _) (head1_mod4 _ _ _)
  (head2_mod4 _ _ _) (head3_mod4 _ _ _) (head4_mod4 _ _ _) (head5_mod4 _ _ _) (head6_mod4 _ _ _)
  (rho_mod4 _ _ _ _) (all_mod4 _ _)

theorem AX_shift5 (a x y t w d h : Nat) :
 commandsEval ([.ax a x y] ++ List.replicate 5 .shift) ⟨t,w,d,h⟩ =
 some ⟨head4Code a (d+x) (h+y),[head6Code a (d+x) (h+y),rho8Code a (d+x) (h+y) d,allCode d h,t].foldr pair w,0,head5Code a (d+x) (h+y)⟩ := by
 rw [commandsEval_append]
 change commandsEval (List.replicate 5 .shift) ⟨gate a (d+x) (h+y),
   (heads a (d+x) (h+y) d h ++ [t]).foldr pair w,0,0⟩ = _
 exact scaffold_shift5 _ _ _ _ _ _ _ _ _ _ _ (gate_mod4 _ _ _) (head1_mod4 _ _ _)
  (head2_mod4 _ _ _) (head3_mod4 _ _ _) (head4_mod4 _ _ _) (head5_mod4 _ _ _) (head6_mod4 _ _ _)
  (rho_mod4 _ _ _ _) (all_mod4 _ _)

theorem AX_shift6 (a x y t w d h : Nat) :
 commandsEval ([.ax a x y] ++ List.replicate 6 .shift) ⟨t,w,d,h⟩ =
 some ⟨head5Code a (d+x) (h+y),[rho8Code a (d+x) (h+y) d,allCode d h,t].foldr pair w,0,head6Code a (d+x) (h+y)⟩ := by
 rw [commandsEval_append]
 change commandsEval (List.replicate 6 .shift) ⟨gate a (d+x) (h+y),
   (heads a (d+x) (h+y) d h ++ [t]).foldr pair w,0,0⟩ = _
 exact scaffold_shift6 _ _ _ _ _ _ _ _ _ _ _ (gate_mod4 _ _ _) (head1_mod4 _ _ _)
  (head2_mod4 _ _ _) (head3_mod4 _ _ _) (head4_mod4 _ _ _) (head5_mod4 _ _ _) (head6_mod4 _ _ _)
  (rho_mod4 _ _ _ _) (all_mod4 _ _)

theorem AX_shift7 (a x y t w d h : Nat) :
 commandsEval ([.ax a x y] ++ List.replicate 7 .shift) ⟨t,w,d,h⟩ =
 some ⟨head6Code a (d+x) (h+y),[allCode d h,t].foldr pair w,0,rho8Code a (d+x) (h+y) d⟩ := by
 rw [commandsEval_append]
 change commandsEval (List.replicate 7 .shift) ⟨gate a (d+x) (h+y),
   (heads a (d+x) (h+y) d h ++ [t]).foldr pair w,0,0⟩ = _
 exact scaffold_shift7 _ _ _ _ _ _ _ _ _ _ _ (gate_mod4 _ _ _) (head1_mod4 _ _ _)
  (head2_mod4 _ _ _) (head3_mod4 _ _ _) (head4_mod4 _ _ _) (head5_mod4 _ _ _) (head6_mod4 _ _ _)
  (rho_mod4 _ _ _ _) (all_mod4 _ _)

theorem AX_shift8 (a x y t w d h : Nat) :
 commandsEval ([.ax a x y] ++ List.replicate 8 .shift) ⟨t,w,d,h⟩ =
 some ⟨rho8Code a (d+x) (h+y) d,[t].foldr pair w,0,allCode d h⟩ := by
 rw [commandsEval_append]
 change commandsEval (List.replicate 8 .shift) ⟨gate a (d+x) (h+y),
   (heads a (d+x) (h+y) d h ++ [t]).foldr pair w,0,0⟩ = _
 exact scaffold_shift8 _ _ _ _ _ _ _ _ _ _ _ (gate_mod4 _ _ _) (head1_mod4 _ _ _)
  (head2_mod4 _ _ _) (head3_mod4 _ _ _) (head4_mod4 _ _ _) (head5_mod4 _ _ _) (head6_mod4 _ _ _)
  (rho_mod4 _ _ _ _) (all_mod4 _ _)

theorem AX_shift9 (a x y t w d h : Nat) :
 commandsEval ([.ax a x y] ++ List.replicate 9 .shift) ⟨t,w,d,h⟩ =
 some ⟨allCode d h,w,0,t⟩ := by
 rw [commandsEval_append]
 change commandsEval (List.replicate 9 .shift) ⟨gate a (d+x) (h+y),
   (heads a (d+x) (h+y) d h ++ [t]).foldr pair w,0,0⟩ = _
 exact scaffold_shift9 _ _ _ _ _ _ _ _ _ _ _ (gate_mod4 _ _ _) (head1_mod4 _ _ _)
  (head2_mod4 _ _ _) (head3_mod4 _ _ _) (head4_mod4 _ _ _) (head5_mod4 _ _ _) (head6_mod4 _ _ _)
  (rho_mod4 _ _ _ _) (all_mod4 _ _)

theorem AX_shift10 (a x y t w d h : Nat) :
 commandsEval ([.ax a x y] ++ List.replicate 10 .shift) ⟨t,w,d,h⟩ =
 some ⟨t,(M6.Source.Cantor.decode w).2,0,(M6.Source.Cantor.decode w).1⟩ := by
 rw [commandsEval_append]
 change commandsEval (List.replicate 10 .shift) ⟨gate a (d+x) (h+y),
   (heads a (d+x) (h+y) d h ++ [t]).foldr pair w,0,0⟩ = _
 exact scaffold_shift10 _ _ _ _ _ _ _ _ _ _ _ (gate_mod4 _ _ _) (head1_mod4 _ _ _)
  (head2_mod4 _ _ _) (head3_mod4 _ _ _) (head4_mod4 _ _ _) (head5_mod4 _ _ _) (head6_mod4 _ _ _)
  (rho_mod4 _ _ _ _) (all_mod4 _ _)
theorem POP_total (t w d h : Nat) : commandsEval POP ⟨t,w,d,h⟩ = some ⟨t,(M6.Source.Cantor.decode w).2,0,(M6.Source.Cantor.decode w).1⟩ :=
 AX_shift10 0 0 0 t w d h

theorem POP_pair (t x w d h : Nat) : commandsEval POP ⟨t,pair x w,d,h⟩ = some ⟨t,w,0,x⟩ := by
 rw [POP_total,decode_pair]

theorem PUSH_total (t w d h : Nat) : commandsEval PUSH ⟨t,w,d,h⟩ = some ⟨0,pair t w,0,0⟩ := by
 rw [PUSH,commandsEval_append,AX_shift8]
 simp [commandsEval,commandEval]

theorem DISCARD_total (t w : Nat) : commandsEval DISCARD ⟨t,w,0,0⟩ = some ⟨0,w,0,0⟩ := by
 have he : [Command.mp 1,Command.ax 1 0 0] ++ List.replicate 9 .shift ++ [.mp 0] =
   [Command.mp 1] ++ ([Command.ax 1 0 0] ++ List.replicate 9 .shift) ++ [.mp 0] := rfl
 have hmp : commandsEval [.mp 1] ⟨t,w,0,0⟩ = some ⟨0,w,1,0⟩ := by
   simp [commandsEval,commandEval]
 rw [DISCARD,he,commandsEval_append,commandsEval_append,hmp]
 simp only [Option.bind_some]
 rw [AX_shift9]
 simp only [Option.bind_some]
 change commandsEval [.mp 0] ⟨allCode 1 0,w,0,0⟩ = some ⟨0,w,0,0⟩
 simp [commandsEval,commandEval]

theorem J_total (u w : Nat) : commandsEval (J u) ⟨0,w,0,0⟩ = some ⟨0,w,u,0⟩ := by
 by_cases hu : u=0
 · simp [J,hu,commandsEval]
 · have h := cantor_ge_right 0 u
   have he : impCode 0 u ≠ 0 := by unfold impCode; omega
   simp [J,hu,commandsEval,commandEval,he]

attribute [local irreducible] commandsEval

theorem POPs_clear (xs : List Nat) (t w d h : Nat) :
 commandsEval (POPs (xs.length+1)) ⟨t,(xs++[0]).foldr pair w,d,h⟩ = some ⟨t,w,0,0⟩ := by
 induction xs generalizing d h with
 | nil =>
   simp only [List.length_nil,Nat.zero_add,List.nil_append,List.foldr_cons,List.foldr_nil]
   rw [POPs,commandsEval_append,POP_pair]
   simp only [Option.bind_some,POPs,commandsEval]
 | cons x xs ih =>
   rw [List.length_cons,List.cons_append,List.foldr_cons,POPs,commandsEval_append,POP_pair]
   simp only [Option.bind_some]
   exact ih 0 x


def supplyHead (j a d h : Nat) : List Command :=
 DISCARD ++ (([.ax a d h] ++ List.replicate (j+1) .shift) ++ POPs (8-j))
def supplyGate (a d h : Nat) : List Command := DISCARD ++ ([.ax a d h] ++ POPs 9)
def supplyRho (a d h u : Nat) : List Command :=
 DISCARD ++ (J u ++ (([.ax a (d-u) h] ++ List.replicate 8 .shift) ++ POP))


/-- Checked opaque abstraction: the stored equality is part of this value's
verified type. It prevents kernel reduction of enormous encoded-stack values
while composing already-proved contracts; it adds no assumption. -/
opaque certifiedEval : {f : List Command → CommandStore → Option CommandStore //
 ∀ cs s, f cs s = commandsEval cs s} := ⟨commandsEval,fun _ _ => rfl⟩
def abstractEval := certifiedEval.val
theorem abstractEval_eq (cs : List Command) (s : CommandStore) : abstractEval cs s = commandsEval cs s := certifiedEval.property cs s
theorem abstractEval_append (xs ys : List Command) (s : CommandStore) : abstractEval (xs++ys) s = (abstractEval xs s).bind (abstractEval ys) := by
 rw [show abstractEval ys = commandsEval ys from funext (abstractEval_eq ys)]
 simp only [abstractEval_eq,commandsEval_append]
private theorem E_discard (t w : Nat) : abstractEval DISCARD ⟨t,w,0,0⟩ = some ⟨0,w,0,0⟩ := by rw [abstractEval_eq]; exact DISCARD_total t w
private theorem E_J (u w : Nat) : abstractEval (J u) ⟨0,w,0,0⟩ = some ⟨0,w,u,0⟩ := by rw [abstractEval_eq]; exact J_total u w
private theorem E_pop (t x w d h : Nat) : abstractEval POP ⟨t,pair x w,d,h⟩ = some ⟨t,w,0,x⟩ := by rw [abstractEval_eq]; exact POP_pair t x w d h
private theorem E_pops (xs : List Nat) (t w d h : Nat) : abstractEval (POPs (xs.length+1)) ⟨t,(xs++[0]).foldr pair w,d,h⟩ = some ⟨t,w,0,0⟩ := by rw [abstractEval_eq]; exact POPs_clear xs t w d h
private theorem E_ax (a x y : Nat) (s : CommandStore) : abstractEval [.ax a x y] s = some ⟨gate a (s.d+x) (s.h+y), (heads a (s.d+x) (s.h+y) s.d s.h ++ [s.t]).foldr pair s.w,0,0⟩ := by rw [abstractEval_eq]; simp only [commandsEval,ax_step,Option.bind_some]
private theorem E_shift2 (a x y t w d h : Nat) :
 abstractEval ([.ax a x y] ++ List.replicate 2 .shift) ⟨t,w,d,h⟩ =
 some ⟨head1Code a (d+x) (h+y),[head3Code a (d+x) (h+y),head4Code a (d+x) (h+y),head5Code a (d+x) (h+y),head6Code a (d+x) (h+y),rho8Code a (d+x) (h+y) d,allCode d h,t].foldr pair w,0,head2Code a (d+x) (h+y)⟩ := by rw [abstractEval_eq]; exact AX_shift2 a x y t w d h
private theorem E_shift3 (a x y t w d h : Nat) :
 abstractEval ([.ax a x y] ++ List.replicate 3 .shift) ⟨t,w,d,h⟩ =
 some ⟨head2Code a (d+x) (h+y),[head4Code a (d+x) (h+y),head5Code a (d+x) (h+y),head6Code a (d+x) (h+y),rho8Code a (d+x) (h+y) d,allCode d h,t].foldr pair w,0,head3Code a (d+x) (h+y)⟩ := by rw [abstractEval_eq]; exact AX_shift3 a x y t w d h
private theorem E_shift4 (a x y t w d h : Nat) :
 abstractEval ([.ax a x y] ++ List.replicate 4 .shift) ⟨t,w,d,h⟩ =
 some ⟨head3Code a (d+x) (h+y),[head5Code a (d+x) (h+y),head6Code a (d+x) (h+y),rho8Code a (d+x) (h+y) d,allCode d h,t].foldr pair w,0,head4Code a (d+x) (h+y)⟩ := by rw [abstractEval_eq]; exact AX_shift4 a x y t w d h
private theorem E_shift5 (a x y t w d h : Nat) :
 abstractEval ([.ax a x y] ++ List.replicate 5 .shift) ⟨t,w,d,h⟩ =
 some ⟨head4Code a (d+x) (h+y),[head6Code a (d+x) (h+y),rho8Code a (d+x) (h+y) d,allCode d h,t].foldr pair w,0,head5Code a (d+x) (h+y)⟩ := by rw [abstractEval_eq]; exact AX_shift5 a x y t w d h
private theorem E_shift6 (a x y t w d h : Nat) :
 abstractEval ([.ax a x y] ++ List.replicate 6 .shift) ⟨t,w,d,h⟩ =
 some ⟨head5Code a (d+x) (h+y),[rho8Code a (d+x) (h+y) d,allCode d h,t].foldr pair w,0,head6Code a (d+x) (h+y)⟩ := by rw [abstractEval_eq]; exact AX_shift6 a x y t w d h
private theorem E_shift7 (a x y t w d h : Nat) :
 abstractEval ([.ax a x y] ++ List.replicate 7 .shift) ⟨t,w,d,h⟩ =
 some ⟨head6Code a (d+x) (h+y),[allCode d h,t].foldr pair w,0,rho8Code a (d+x) (h+y) d⟩ := by rw [abstractEval_eq]; exact AX_shift7 a x y t w d h
private theorem E_shift8 (a x y t w d h : Nat) :
 abstractEval ([.ax a x y] ++ List.replicate 8 .shift) ⟨t,w,d,h⟩ =
 some ⟨rho8Code a (d+x) (h+y) d,[t].foldr pair w,0,allCode d h⟩ := by rw [abstractEval_eq]; exact AX_shift8 a x y t w d h
private theorem opaque_supplyHead1_total (a d h t w : Nat) :
 abstractEval (supplyHead 1 a d h) ⟨t,w,0,0⟩ = some ⟨head1Code a d h,w,0,0⟩ := by
 rw [supplyHead,abstractEval_append,E_discard]
 simp only [Option.bind_some]
 rw [abstractEval_append,E_shift2]
 simp only [Option.bind_some,Nat.zero_add]
 simpa only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,List.cons_append,List.nil_append] using E_pops [head3Code a d h,head4Code a d h,head5Code a d h,head6Code a d h,rho8Code a d h 0,allCode 0 0] (head1Code a d h) w 0 (head2Code a d h)


private theorem opaque_supplyHead2_total (a d h t w : Nat) :
 abstractEval (supplyHead 2 a d h) ⟨t,w,0,0⟩ = some ⟨head2Code a d h,w,0,0⟩ := by
 rw [supplyHead,abstractEval_append,E_discard]
 simp only [Option.bind_some]
 rw [abstractEval_append,E_shift3]
 simp only [Option.bind_some,Nat.zero_add]
 simpa only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,List.cons_append,List.nil_append] using E_pops [head4Code a d h,head5Code a d h,head6Code a d h,rho8Code a d h 0,allCode 0 0] (head2Code a d h) w 0 (head3Code a d h)


private theorem opaque_supplyHead3_total (a d h t w : Nat) :
 abstractEval (supplyHead 3 a d h) ⟨t,w,0,0⟩ = some ⟨head3Code a d h,w,0,0⟩ := by
 rw [supplyHead,abstractEval_append,E_discard]
 simp only [Option.bind_some]
 rw [abstractEval_append,E_shift4]
 simp only [Option.bind_some,Nat.zero_add]
 simpa only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,List.cons_append,List.nil_append] using E_pops [head5Code a d h,head6Code a d h,rho8Code a d h 0,allCode 0 0] (head3Code a d h) w 0 (head4Code a d h)


private theorem opaque_supplyHead4_total (a d h t w : Nat) :
 abstractEval (supplyHead 4 a d h) ⟨t,w,0,0⟩ = some ⟨head4Code a d h,w,0,0⟩ := by
 rw [supplyHead,abstractEval_append,E_discard]
 simp only [Option.bind_some]
 rw [abstractEval_append,E_shift5]
 simp only [Option.bind_some,Nat.zero_add]
 simpa only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,List.cons_append,List.nil_append] using E_pops [head6Code a d h,rho8Code a d h 0,allCode 0 0] (head4Code a d h) w 0 (head5Code a d h)


private theorem opaque_supplyHead5_total (a d h t w : Nat) :
 abstractEval (supplyHead 5 a d h) ⟨t,w,0,0⟩ = some ⟨head5Code a d h,w,0,0⟩ := by
 rw [supplyHead,abstractEval_append,E_discard]
 simp only [Option.bind_some]
 rw [abstractEval_append,E_shift6]
 simp only [Option.bind_some,Nat.zero_add]
 simpa only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,List.cons_append,List.nil_append] using E_pops [rho8Code a d h 0,allCode 0 0] (head5Code a d h) w 0 (head6Code a d h)


private theorem opaque_supplyHead6_total (a d h t w : Nat) :
 abstractEval (supplyHead 6 a d h) ⟨t,w,0,0⟩ = some ⟨head6Code a d h,w,0,0⟩ := by
 rw [supplyHead,abstractEval_append,E_discard]
 simp only [Option.bind_some]
 rw [abstractEval_append,E_shift7]
 simp only [Option.bind_some,Nat.zero_add]
 simpa only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,List.cons_append,List.nil_append] using E_pops [allCode 0 0] (head6Code a d h) w 0 (rho8Code a d h 0)


private theorem opaque_supplyGate_total (a d h t w : Nat) :
 abstractEval (supplyGate a d h) ⟨t,w,0,0⟩ = some ⟨gate a d h,w,0,0⟩ := by
 rw [supplyGate,abstractEval_append,E_discard]
 simp only [Option.bind_some]
 rw [abstractEval_append]
 rw [E_ax]
 simp only [Option.bind_some,Nat.zero_add]
 simpa only [heads,List.length_cons,List.length_nil,Nat.reduceAdd,List.cons_append,List.nil_append] using E_pops (heads a d h 0 0) (gate a d h) w 0 0


private theorem opaque_supplyRho_total (a d h u t w : Nat) (hu : u ≤ d) :
 abstractEval (supplyRho a d h u) ⟨t,w,0,0⟩ = some ⟨rho8Code a d h u,w,0,0⟩ := by
 rw [supplyRho,abstractEval_append,E_discard]
 simp only [Option.bind_some]
 rw [abstractEval_append,E_J]
 simp only [Option.bind_some]
 rw [abstractEval_append,E_shift8]
 simp only [Option.bind_some,Nat.zero_add]
 rw [show u+(d-u)=d by omega]
 simp only [List.foldr_cons,List.foldr_nil]
 rw [E_pop]

theorem supplyHead1_total (a d h t w : Nat) : commandsEval (supplyHead 1 a d h) ⟨t,w,0,0⟩ = some ⟨head1Code a d h,w,0,0⟩ := by
 rw [← abstractEval_eq]
 exact opaque_supplyHead1_total a d h t w

theorem supplyHead2_total (a d h t w : Nat) : commandsEval (supplyHead 2 a d h) ⟨t,w,0,0⟩ = some ⟨head2Code a d h,w,0,0⟩ := by
 rw [← abstractEval_eq]
 exact opaque_supplyHead2_total a d h t w

theorem supplyHead3_total (a d h t w : Nat) : commandsEval (supplyHead 3 a d h) ⟨t,w,0,0⟩ = some ⟨head3Code a d h,w,0,0⟩ := by
 rw [← abstractEval_eq]
 exact opaque_supplyHead3_total a d h t w

theorem supplyHead4_total (a d h t w : Nat) : commandsEval (supplyHead 4 a d h) ⟨t,w,0,0⟩ = some ⟨head4Code a d h,w,0,0⟩ := by
 rw [← abstractEval_eq]
 exact opaque_supplyHead4_total a d h t w

theorem supplyHead5_total (a d h t w : Nat) : commandsEval (supplyHead 5 a d h) ⟨t,w,0,0⟩ = some ⟨head5Code a d h,w,0,0⟩ := by
 rw [← abstractEval_eq]
 exact opaque_supplyHead5_total a d h t w

theorem supplyHead6_total (a d h t w : Nat) : commandsEval (supplyHead 6 a d h) ⟨t,w,0,0⟩ = some ⟨head6Code a d h,w,0,0⟩ := by
 rw [← abstractEval_eq]
 exact opaque_supplyHead6_total a d h t w

theorem supplyGate_total (a d h t w : Nat) : commandsEval (supplyGate a d h) ⟨t,w,0,0⟩ = some ⟨gate a d h,w,0,0⟩ := by
 rw [← abstractEval_eq]
 exact opaque_supplyGate_total a d h t w

theorem supplyRho_total (a d h u t w : Nat) (hu : u ≤ d) : commandsEval (supplyRho a d h u) ⟨t,w,0,0⟩ = some ⟨rho8Code a d h u,w,0,0⟩ := by
 rw [← abstractEval_eq]
 exact opaque_supplyRho_total a d h u t w hu
end C207Search
