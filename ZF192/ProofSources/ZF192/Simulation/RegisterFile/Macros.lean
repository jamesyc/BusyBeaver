module
public import ZF192.Simulation.RegisterFile.Marker
@[expose] public section

/-! # The three register macros

The selector counts the blocks before the operand. The moving marker
returns after a successful change and shifts the gate outward by one cell.
The zero return preserves the tape. The increment copy uses the blank
exterior after the active file, and its result preserves that invariant. -/
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192.BinaryTape
open ZFR.ArithmeticRepresentation M192
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma select_register {chain : List Nat} (hc : ChainRows chain) (pre : List M)
    (hp : pre.length + 2 ≤ 10) (t y : M) :
    Reaches (cell (chain.getD (pre.length + 2) 0) (b0 (file pre t)) (b0 y))
      (cellL (chain.getD 0 0) t (revPush pre (b0 (b0 y)))) := by
  refine (chain_gate hc pre.length hp (file pre t) y).trans ?_
  simpa only [Nat.zero_add] using chain_blocks hc pre 0 (by omega) t (b0 (b0 y))

/-- Carry a separator through the remaining blocks, turn at the blank
exterior, and copy those blocks back past the pending marker. -/
lemma copy_suffix (post : List M) (r : M) :
    Reaches (cellL copy1 (file post 0) (b1 r))
      (cell retS (b0 (b1 (b0 (file post 0)))) r) := by
  induction post generalizing r with
  | nil =>
    have blank : cellL copy1 (0 : M) (b1 r) = cell copy1 0 (b0 (b1 r)) := by
      simpa only [mul_zero] using cellL_zero copy1 (0 : M) (b1 r)
    rw [file_nil, blank]
    simpa only [mul_zero] using copy1_cap_bit (0 : M) r
  | cons v post ih =>
    let t := file post 0
    rw [file_cons, blk_eq, cellL_one]
    refine (copy1_body (ones v (b0 t)) r).trans ?_
    refine (scanL1 row_copy0_1 v (b0 t) (b0 (b1 r))).trans ?_
    rw [cellL_zero]
    have carry := stepL0 row_copy0_0 t (ones v (b0 (b1 r)))
    simp only [bitValue, ite_true] at carry
    refine carry.trans ?_
    refine (ih (ones v (b0 (b1 r)))).trans ?_
    refine (marker_scan v (b1 (b0 t)) (b0 (b1 r))).trans ?_
    have finish := marker_separator (ones v (b1 (b0 t))) r
    simpa only [ones_commute, ones_succ] using finish

lemma zero_cross (v l r : M) :
    Reaches (cell retZ l (rblk v r)) (cell retZ (blk v l) r) := by
  rw [rblk_eq]
  refine (zero_cross_separator l (ones v r)).trans ?_
  have h := scanR1 row_retZ_1 (v+1) (b0 l) r
  rw [blk_eq]
  simpa only [ones_succ] using h

lemma zero_blocks (pre : List M) (l r : M) :
    Reaches (cell retZ l (revPush pre r)) (cell retZ (file pre l) r) := by
  induction pre generalizing r with
  | nil => exact Reaches.refl _
  | cons v pre ih =>
    rw [revPush, file_cons]
    exact (ih (rblk v r)).trans (zero_cross v (file pre l) r)

theorem inc_macro (pre post : List M) (hp : pre.length + 2 ≤ 10) (v y : M) :
    Reaches (cell (chainI.getD (pre.length+2) 0) (b0 (file (pre++v::post) 0)) (b0 (b1 y)))
      (cell readSuccess (b1 (b0 (b0 (file (pre++(v+1)::post) 0)))) (b1 y)) := by
  rw [file_append, file_cons, file_append, file_cons]
  refine (select_register chainI_rows pre hp _ (b1 y)).trans ?_
  rw [chainI_zero]
  refine (copy0_block v (file post 0) _).trans ?_
  refine (copy_suffix post _).trans ?_
  refine (marker_scan (v+1) (b1 (b0 (file post 0))) _).trans ?_
  rw [blk_ones]
  exact (marker_blocks pre _ _).trans (marker_gate _ y)

theorem dec_zero_macro (pre post : List M) (hp : pre.length + 2 ≤ 10) (y : M) :
    Reaches (cell (chainD.getD (pre.length+2) 0) (b0 (file (pre++0::post) 0)) (b0 y))
      (cell readZero (b0 (b0 (file (pre++0::post) 0))) y) := by
  rw [file_append, file_cons]
  refine (select_register chainD_rows pre hp _ y).trans ?_
  rw [chainD_zero, blk_eq, ones_zero, cellL_one]
  exact (dec_zero_begin (file post 0) _).trans
    ((zero_blocks pre _ _).trans (zero_gate _ y))

theorem dec_pos_macro (pre post : List M) (hp : pre.length + 2 ≤ 10) (v y : M) :
    Reaches (cell (chainD.getD (pre.length+2) 0) (b0 (file (pre++(v+1)::post) 0)) (b0 (b1 y)))
      (cell readSuccess (b1 (b0 (b0 (file (pre++v::post) 0)))) (b1 y)) := by
  rw [file_append, file_cons, file_append, file_cons]
  refine (select_register chainD_rows pre hp _ (b1 y)).trans ?_
  rw [chainD_zero, blk_eq (v+1), ones_succ, cellL_one, ← blk_eq v]
  let t := file post 0
  let padding := b0 (b0 (b1 y))
  have enter : Reaches (cell delBegin (blk v t) (b1 (revPush pre padding)))
      (cell retS (b0 (blk v t)) (revPush pre padding)) := by
    simpa only [blk_eq] using dec_plant (ones v (b0 t)) (revPush pre padding)
  refine enter.trans ((marker_blocks pre (blk v t) padding).trans ?_)
  exact marker_gate (file pre (blk v t)) y

end ZF192.BinaryTape
