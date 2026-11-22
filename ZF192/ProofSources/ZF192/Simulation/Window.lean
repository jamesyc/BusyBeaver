module
public import ZF192.Simulation.RegisterFile.Operations
public import ZF192.Machine.Decoder.Window
@[expose] public section
/-! # Window runs inside PA

A finite word in front of an arbitrary numeral: `bitPrefix w t`. A successful window run
(`M192.Window.wrun`) is an actual physical run for arbitrary model-sized tape outside the
window, on both sides. -/
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192.BinaryTape
open ZFR.ArithmeticRepresentation M192 M192.Window
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

noncomputable def bitPrefix : List Bool → M → M
 | [], t => t
 | b::bs, t => bitValue b+2*bitPrefix bs t

lemma bitPrefix_bits (path tail:List Bool) : bitPrefix path (bitsCode (M:=M) tail)=bitsCode (path++tail) := by
 induction path with
 | nil => rfl
 | cons b bs ih => simp only [bitPrefix,List.cons_append,bitsCode,ih]

lemma model_wstep {q q':Nat} {wl wr wl' wr':List Bool} (h:wstep q wl wr=some (q',wl',wr')) (lx ρ:M) :
 literalStep (cell q (bitPrefix wl lx) (bitPrefix wr ρ)) (cell q' (bitPrefix wl' lx) (bitPrefix wr' ρ)) := by
 cases wr with
 | nil => simp [wstep] at h
 | cons c rs =>
  simp only [wstep] at h
  split at h
  · simp at h
  · rename_i b q2 hrow
    simp only [Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl,rfl⟩:=h
    exact physical_right q q2 c b (bitPrefix wl lx) (bitPrefix rs ρ) hrow
  · rename_i b q2 hrow
    cases wl with
    | nil => simp at h
    | cons a ls =>
      simp only [Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl,rfl⟩:=h
      have four : (2 : M) * 2 = 4 := by norm_num
      simpa only [bitPrefix, cell, mul_add, ←mul_assoc, four, add_assoc] using
        physical_left q q2 c b a (bitPrefix ls lx) (bitPrefix rs ρ) hrow

lemma model_wrun {stop:Nat→List Bool→Bool} (lx ρ:M) : ∀ (f q:Nat) (wl wr:List Bool) {q':Nat}
 {wl' wr':List Bool}, wrun stop f q wl wr=some (q',wl',wr') →
 stop q' wl'=true ∧ Reaches (cell q (bitPrefix wl lx) (bitPrefix wr ρ)) (cell q' (bitPrefix wl' lx) (bitPrefix wr' ρ))
 | 0, _, _, _, _, _, _, h => by simp [wrun] at h
 | f+1, q, wl, wr, q', wl', wr', h => by
  simp only [wrun] at h
  split at h
  · rename_i hs
    simp only [Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl,rfl⟩:=h
    exact ⟨hs,Reaches.refl _⟩
  · split at h
    · simp at h
    · rename_i q2 wl2 wr2 hstep
      obtain ⟨hs,hr⟩:=model_wrun lx ρ f q2 wl2 wr2 h
      exact ⟨hs,(Reaches.step (model_wstep hstep lx ρ)).trans hr⟩

lemma model_wrun1 {stop:Nat→List Bool→Bool} (lx ρ:M) {f q q':Nat} {wl wr wl' wr':List Bool}
 (h:wrun1 stop f q wl wr=some (q',wl',wr')) :
 stop q' wl'=true ∧ Reaches1 (cell q (bitPrefix wl lx) (bitPrefix wr ρ)) (cell q' (bitPrefix wl' lx) (bitPrefix wr' ρ)) := by
 simp only [wrun1] at h
 split at h
 · simp at h
 · rename_i q2 wl2 wr2 hstep
   obtain ⟨hs,hr⟩:=model_wrun lx ρ f q2 wl2 wr2 h
   exact ⟨hs, _, model_wstep hstep lx ρ, hr⟩

end ZF192.BinaryTape
