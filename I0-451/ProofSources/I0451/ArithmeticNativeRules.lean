module
public import I0451.ArithmeticNativeSentence
public import I0451.Logic.ImplicationBasis

/-! The native proof predicate is closed under the exact rule
constructors. Combining proofs concatenates their formula books and
uses the earlier indices in each half. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime
open I0451.Logic (AxiomEncoding ImplicationBasis implicationBasis_of_single)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def NativeDerivable (formula : V) : Prop := ∃ book, NativeProof book formula

theorem nativeDerivable_defined :
    𝚺ᴬ₁-Predicate[V] (NativeDerivable : V → Prop) via nativeDerivableDef :=
  .mk fun v => by
    rw [Matrix.fun_eq_vec_one v]
    exact nativeDerivable_eval _

/-- Moving a line and its premises along an order-preserving map
preserves the justification of that line. -/
private theorem NativeLine.transfer {before after i j f : V}
    (step : NativeLine before i f) (index : V → V)
    (earlier : ∀ k < i, index k < j)
    (agrees : ∀ k < i, znth after (index k) = znth before k) :
    NativeLine after j f := by
  cases step with
  | truth => exact .truth
  | foundation => exact .foundation
  | berkeley => exact .berkeley
  | head a b c x f member => exact .head a b c x f member
  | bundle a b c ha hb => exact .bundle a b c ha hb
  | generalize label k hk =>
    simpa only [agrees k hk] using (NativeLine.generalize (book := after) label _ (earlier k hk))
  | detach a b k l hk hl antecedent conditional =>
    exact .detach a f (index k) (index l) (earlier k hk) (earlier l hl)
      ((agrees k hk).trans antecedent) ((agrees l hl).trans conditional)

private theorem NativeProof.append {book f g : V} (old : NativeProof book f)
    (latest : NativeLine book (lh book) g) : NativeProof (book ⁀' g) g := by
  obtain ⟨seq, _, lines⟩ := old
  refine ⟨seq.seqCons _, ?_, ?_⟩
  · exact ⟨lh book, by simp [seq], znth_append_last seq g⟩
  · intro i iIn
    rw [seq.lh_seqCons] at iIn
    rcases eq_or_lt_of_le (lt_succ_iff_le.mp iIn) with rfl | before
    · rw [znth_append_last seq g]
      exact latest.transfer id (fun _ h => h) (fun _ h => znth_append_old seq _ h)
    · rw [znth_append_old seq g before]
      exact (lines i before).transfer id (fun _ h => h) (fun _ h => znth_append_old seq _ (lt_trans h before))

private theorem NativeDerivable.single {f : V} (first : NativeLine (∅ : V) 0 f) :
    NativeDerivable f := by
  have seq : Seq (∅ : V) := by simp
  refine ⟨(∅ : V) ⁀' f, seq.seqCons f, ⟨0, by simp [seq], by simpa using znth_append_last seq f⟩, ?_⟩
  intro i iIn
  rw [seq.lh_seqCons, lh_empty, zero_add] at iIn
  have eq : i = 0 := by simpa using iIn
  subst i
  rw [show znth ((∅ : V) ⁀' f) 0 = f by simpa using znth_append_last seq f]
  exact first.transfer id (fun _ h => (not_lt_zero h).elim) (fun _ h => (not_lt_zero h).elim)

private theorem AppendedPrefix.nativeProofs {left right joined a b : V}
    (concat : AppendedPrefix left right (lh right) joined)
    (l : NativeProof left a) (r : NativeProof right b) :
    NativeProof joined a ∧ ∃ j < lh joined, znth joined j = b := by
  obtain ⟨_, ⟨i, hi, foundA⟩, lLines⟩ := l
  obtain ⟨_, ⟨j, hj, foundB⟩, rLines⟩ := r
  have inLeft (k : V) (hk : k < lh left) : k < lh joined := by
    rw [concat.length]
    exact lt_of_lt_of_le hk (by simp)
  have inRight (k : V) (hk : k < lh right) : lh left + k < lh joined := by
    rw [concat.length, add_comm (lh left) k, add_comm (lh left) (lh right)]
    exact add_lt_add_left hk _
  refine ⟨⟨concat.sequence, ⟨i, inLeft i hi, (concat.first i hi).trans foundA⟩, ?_⟩,
    ⟨lh left + j, inRight j hj, (concat.last j hj).trans foundB⟩⟩
  intro k kIn
  by_cases first : k < lh left
  · rw [concat.first k first]
    exact (lLines k first).transfer id (fun _ h => h) (fun n h => concat.first n (lt_trans h first))
  · have ge : lh left ≤ k := le_of_not_gt first
    let t := k - lh left
    have indexEq : k = lh left + t := by
      rw [add_comm, tsub_add_cancel_of_le ge]
    have earlier : t < lh right := by
      rw [indexEq, concat.length, add_comm (lh left) t, add_comm (lh left) (lh right)] at kIn
      exact lt_of_add_lt_add_right kIn
    rw [indexEq, concat.last _ earlier]
    exact (rLines t earlier).transfer (lh left + ·)
      (fun n h => by simpa [add_comm (lh left)] using add_lt_add_left h (lh left))
      (fun n h => concat.last n (lt_trans h earlier))

namespace NativeDerivable

theorem truth : NativeDerivable (0 : V) := .single .truth

theorem head {a b c x f : V} (member : f ∈ modelEncoding.heads a b c x) :
    NativeDerivable f :=
  .single (.head a b c x f member)

theorem bundle {a b c : V} (ha : c ≠ a) (hb : c ≠ b) :
    NativeDerivable (modelEncoding.bundle a b c) :=
  .single (.bundle a b c ha hb)

theorem foundation : NativeDerivable (Runtime.literalFoundationCode : V) :=
  .single .foundation

theorem berkeley : NativeDerivable (Runtime.literalBerkeleyCode : V) :=
  .single .berkeley

theorem generalize (label : V) {f : V} (proof : NativeDerivable f) :
    NativeDerivable (modelEncoding.all label f) := by
  obtain ⟨book, proof⟩ := proof
  obtain ⟨i, hi, atI⟩ := proof.2.1
  exact ⟨_, proof.append (atI ▸ NativeLine.generalize label i hi)⟩

theorem detach {a b : V} (premise : NativeDerivable a) (conditional : NativeDerivable (modelImp a b)) :
    NativeDerivable b := by
  obtain ⟨left, l⟩ := premise
  obtain ⟨right, r⟩ := conditional
  obtain ⟨joined, concat⟩ := appendedSequence_exists l.1 right
  obtain ⟨together, j, hj, rightAt⟩ := concat.nativeProofs l r
  obtain ⟨i, hi, leftAt⟩ := together.2.1
  exact ⟨_, together.append (.detach a b i j hi hj leftAt rightAt)⟩

theorem implicationBasis : ImplicationBasis (P := NativeDerivable (V := V)) modelImp :=
  implicationBasis_of_single modelImp (fun a b => a.detach b) fun a x c d =>
    head (a := c) (b := d) (c := a) (x := x) (by simp [AxiomEncoding.heads, modelEncoding])

end NativeDerivable

end I0451.Arithmetization
