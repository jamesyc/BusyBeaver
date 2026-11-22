module
public import ZF192.Tape.Scan
public import ZF192.Tape.Uncons
public import ZF192.Machine.RegisterProtocol
@[expose] public section
/-! # Literal ZF192 moves on numerically coded tapes

A tape side is a little-endian numeral (`bitsCode`), so it holds an arbitrary element of the
PA model. `cell q l r` has the head on the first cell of `r`; `cellL q l r` on the first cell
of `l`. The register file of ZF192 is read outward from the gate: register value `v` is the
block `1^(v+1) 0` (`blk`), and the machine maintains a blank tail after the last active block.
Every lemma below is a finite composition of literal rows and self-loop scans of model length. -/
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192.BinaryTape
open ZFR.ArithmeticRepresentation M192
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Head on the first cell of `r`; `l` lists the cells to its left, nearest first. -/
def cell (q:Nat) (l r:M) : State M := ⟨(q:M),l,r⟩
/-- Head on the first cell of `l`. -/
noncomputable def cellL (q:Nat) (l r:M) : State M := ⟨(q:M),tailBits l,lowBit l+2*r⟩

lemma cellL_bit (q:Nat) (b:Bool) (l r:M) : cellL q (bitValue b+2*l) r=cell q l (bitValue b+2*r) := by
 simp only [cellL,cell,lowBit_cons,tailBits_cons]
lemma cellL_zero (q:Nat) (l r:M) : cellL q (2*l) r=cell q l (2*r) := by
 simpa [bitValue] using cellL_bit (M:=M) q false l r
lemma cellL_one (q:Nat) (l r:M) : cellL q (1+2*l) r=cell q l (1+2*r) := by
 simpa [bitValue] using cellL_bit (M:=M) q true l r

lemma stepR {q t:Nat} {b w:Bool} (row:M192.literal q b=some (w,true,t)) (l r:M) :
 Reaches (cell q l (bitValue b+2*r)) (cell t (bitValue w+2*l) r) :=
 Reaches.step (physical_right q t b w l r row)
lemma stepL {q t:Nat} {b w:Bool} (row:M192.literal q b=some (w,false,t)) (l r:M) :
 Reaches (cell q l (bitValue b+2*r)) (cellL t l (bitValue w+2*r)) := by
 obtain ⟨c,lt,rfl⟩:=bits_surjective l
 rw [cellL_bit]
 have h4:(2:M)*2=4 := by norm_num
 simpa only [cell,mul_add,←mul_assoc,h4,add_assoc] using Reaches.step (physical_left q t b w c lt r row)

lemma stepR0 {q t:Nat} {w:Bool} (row:M192.literal q false=some (w,true,t)) (l r:M) :
 Reaches (cell q l (2*r)) (cell t (bitValue w+2*l) r) := by
 simpa [bitValue] using stepR row l r
lemma stepR1 {q t:Nat} {w:Bool} (row:M192.literal q true=some (w,true,t)) (l r:M) :
 Reaches (cell q l (1+2*r)) (cell t (bitValue w+2*l) r) := by
 simpa [bitValue] using stepR row l r
lemma stepL0 {q t:Nat} {w:Bool} (row:M192.literal q false=some (w,false,t)) (l r:M) :
 Reaches (cell q l (2*r)) (cellL t l (bitValue w+2*r)) := by
 simpa [bitValue] using stepL row l r
lemma stepL1 {q t:Nat} {w:Bool} (row:M192.literal q true=some (w,false,t)) (l r:M) :
 Reaches (cell q l (1+2*r)) (cellL t l (bitValue w+2*r)) := by
 simpa [bitValue] using stepL row l r

/-- A run of `n` ones in front of `t`. -/
noncomputable def ones (n t:M) : M := bitRun n 1 t
lemma ones_zero (t:M) : ones 0 t=t := bitRun_zero _ _
lemma ones_succ (n t:M) : ones (n+1) t=1+2*ones n t := bitRun_succ _ _ _
lemma ones_commute (n t:M) : ones n (1+2*t)=ones (n+1) t := bitRun_commute _ _ _

lemma scanR1 {q:Nat} (row:M192.literal q true=some (true,true,q)) (n l r:M) :
 Reaches (cell q l (ones n r)) (cell q (ones n l) r) := by
 have h:=scan_right q true n l r row
 simpa [ones,cell,bitValue] using h
lemma scanL1 {q:Nat} (row:M192.literal q true=some (true,false,q)) (n l r:M) :
 Reaches (cellL q (ones n l) r) (cellL q l (ones n r)) := by
 by_cases hn:n=0
 · subst n; simp only [ones_zero]; exact Reaches.refl _
 · obtain ⟨k,hk⟩:=eq_succ_of_pos (pos_iff_ne_zero.mpr hn)
   subst hk
   rw [ones_succ,cellL_one]
   have hs:Reaches (cell q (ones k l) (1+2*r)) (cell q l (ones k (1+2*r))) := by
    intro initial hist hh he
    have h:=physical_scan_left q true row k l r initial hist hh (by simpa [cell,ones,bitValue] using he)
    simpa [cell,ones,bitValue] using h
   rw [ones_commute,ones_succ] at hs
   refine hs.trans ?_
   have hm:=stepL1 row l (ones k r)
   simpa [bitValue,←ones_succ] using hm

/-! ## Register blocks -/

/-- Register value `v`, read outward: `v+1` ones, then the separator 0, then `t`. -/
noncomputable def blk (v t:M) : M := ones (v+1) (2*t)
/-- The same block as it lies on the gate side of the head after being crossed outward. -/
noncomputable def rblk (v r:M) : M := 2*ones (v+1) r
noncomputable def file (vs:List M) (x:M) : M := vs.foldr blk x
noncomputable def revPush : List M → M → M
 | [], r => r
 | v::vs, r => revPush vs (rblk v r)

lemma file_nil (x:M) : file [] x=x := rfl
lemma file_cons (v:M) (vs:List M) (x:M) : file (v::vs) x=blk v (file vs x) := rfl
lemma file_append (a b:List M) (x:M) : file (a++b) x=file a (file b x) := by
 simp [file,List.foldr_append]
lemma blk_eq (v t:M) : blk v t=1+2*ones v (2*t) := by
 rw [blk,ones_succ]
lemma blk_ones (v t:M) : ones (v+1) (1+2*(2*t))=blk (v+1) t := by
 rw [ones_commute,blk]
lemma rblk_eq (v r:M) : rblk v r=2*(1+2*ones v r) := by
 rw [rblk,ones_succ]
/-! ## Selecting a register: the issue chain counts separators -/

section Chain
variable {chain:List Nat} (hc:ChainRows chain)
include hc

lemma chain_cross (k:Nat) (hk:k<10) (v t r:M) :
 Reaches (cellL (chain.getD (k+1) 0) (blk v t) r) (cellL (chain.getD k 0) t (rblk v r)) := by
 have h1:=hc.2 ⟨k,hk⟩
 have h0:=hc.1 ⟨k,hk⟩
 refine (scanL1 h1 (v+1) (2*t) r).trans ?_
 rw [cellL_zero]
 simpa [bitValue,rblk] using stepL0 h0 t (ones (v+1) r)

lemma chain_blocks : ∀ (pre:List M) (k:Nat), k+pre.length≤10 → ∀ (t r:M),
 Reaches (cellL (chain.getD (k+pre.length) 0) (file pre t) r) (cellL (chain.getD k 0) t (revPush pre r))
 | [], k, _, t, r => by simpa [file_nil,revPush] using Reaches.refl (cellL (chain.getD k 0) t r)
 | v::pre, k, hk, t, r => by
   simp only [List.length_cons] at hk ⊢
   rw [show k+(pre.length+1)=(k+pre.length)+1 by omega,file_cons]
   refine (chain_cross hc (k+pre.length) (by omega) v (file pre t) r).trans ?_
   exact chain_blocks pre k (by omega) t (rblk v r)

lemma chain_gate (k:Nat) (hk:k+2≤10) (F y:M) :
 Reaches (cell (chain.getD (k+2) 0) (2*F) (2*y)) (cellL (chain.getD k 0) F (2*(2*y))) := by
 have ha:=hc.1 ⟨k+1,by omega⟩
 have hb:=hc.1 ⟨k,by omega⟩
 simp only at ha hb
 refine (stepL0 ha (2*F) y).trans ?_
 simp only [bitValue,Bool.false_eq_true,ite_false,zero_add]
 rw [cellL_zero]
 simpa [bitValue] using stepL0 hb F (2*y)
end Chain

/-! ## Increment carry -/

lemma copy0_block (v t r:M) :
 Reaches (cellL copy0 (blk v t) r) (cellL copy1 t (1+2*ones (v+1) r)) := by
 refine (scanL1 row_copy0_1 (v+1) (2*t) r).trans ?_
 rw [cellL_zero]
 simpa [bitValue] using stepL0 row_copy0_0 t (ones (v+1) r)

end ZF192.BinaryTape
