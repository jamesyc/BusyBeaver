module
public import I0451.ArithmeticSequence
public import I0451.ArithmeticPackedCommands
public import I0451.ArithmeticValueDefinability

/-! Pack an internally finite command sequence into the literal queue.
Each sequence cell holds a command packet. Packing replaces each packet's
tail with the already packed suffix and adds the delimiter used by the machine. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open I0451.Logic (Command)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def packetWithTail (packet tail : V) : V :=
  let selector := cantorLeft packet
  let fields := cantorRight packet
  let parameters := cantorRight fields
  let axTail := cantor (cantorLeft parameters) (cantor (cantorLeft (cantorRight parameters)) tail)
  cantor selector (cantor (cantorLeft fields) (if selector < 4 then tail else axTail))

private theorem packetWithTail_defined {k : Nat} (p t : (Fin k → V) → V)
    (dp : 𝚺ᴬ₁.DefinableFunction (V := V) p) (dt : 𝚺ᴬ₁.DefinableFunction (V := V) t) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun v => packetWithTail (p v) (t v)) := by
  let mode (v : Fin k → V) := cantorLeft (p v)
  let fields (v : Fin k → V) := cantorRight (p v)
  let extra (v : Fin k → V) := cantorRight (fields v)
  let suffix (v : Fin k → V) :=
    cantor (cantorLeft (extra v)) (cantor (cantorLeft (cantorRight (extra v))) (t v))
  have dm : 𝚺ᴬ₁.DefinableFunction (V := V) mode := by dsimp [mode]; definability
  have df : 𝚺ᴬ₁.DefinableFunction (V := V) fields := by dsimp [fields]; definability
  have de : 𝚺ᴬ₁.DefinableFunction (V := V) extra := by dsimp only [extra]; definability
  have dx : 𝚺ᴬ₁.DefinableFunction (V := V) suffix := by dsimp only [suffix]; definability
  let choice (v : Fin k → V) := if mode v < 4 then t v else suffix v
  have dc : 𝚺ᴬ₁.DefinableFunction (V := V) choice := by
    have equation (v : Fin k → V) : choice v = (if mode v - 3 = 0 then t v else suffix v) := by
      have test : mode v < 4 ↔ mode v - 3 = 0 := by
        rw [sub_eq_zero_iff_le]
        exact lt_succ_iff_le
      by_cases short : mode v < 4
      · simp only [choice, ite_eq_left short, ite_eq_left (test.mp short)]
      · exact (ite_eq_right short).trans (ite_eq_right (fun zero => short (test.mpr zero))).symm
    exact (arithmeticCompare_defined (fun v => mode v - 3) (fun _ => 0) t suffix
      (by definability) (by definability) dt dx).of_eq _ (fun v => (equation v).symm)
  change 𝚺ᴬ₁.DefinableFunction (V := V)
    (fun v => cantor (mode v) (cantor (cantorLeft (fields v)) (choice v)))
  definability

theorem packetWithTail_packModelCommand (cmd : Command V) (old new : V) :
    packetWithTail (packModelCommand cmd old) new = packModelCommand cmd new := by
  have lt0 : (0 : V) < 4 := by norm_num
  have lt1 : (1 : V) < 4 := by norm_num
  have lt2 : (2 : V) < 4 := (Nat.cast_lt (α := V)).mpr (by decide : (2 : Nat) < 4)
  have lt3 : (3 : V) < 4 := (Nat.cast_lt (α := V)).mpr (by decide : (3 : Nat) < 4)
  cases cmd <;> simp [packModelCommand, packetWithTail, lt0, lt1, lt2, lt3]

noncomputable def queueWriter (word : V) (state : V) : V :=
  let n := π₁ state + 1
  let packet := znth word (lh word - n)
  ⟪n, packetWithTail packet (π₂ state) + 1⟫

theorem queueWriter_defined (word : V) :
    𝚺ᴬ₁-Function₁[V] (queueWriter word) := by
  have payload := packetWithTail_defined
    (fun v : Fin 1 → V => znth word (lh word - (π₁ (v 0) + 1))) (fun v => π₂ (v 0))
    (by definability) (by definability)
  unfold queueWriter
  definability

/-- The queue from a given position through the end of the word,
with the tail provided as the initial value of the backwards writer. -/
noncomputable def encodedQueueAt (word written position : V) : V :=
  π₂ (znth written (lh word - position))

theorem encodedQueueAt_definable (word written : V) :
    𝚺ᴬ₁-Function₁[V] (encodedQueueAt word written) := by
  unfold encodedQueueAt
  definability

theorem queueWriter_index {word history tail : V}
    (ran : Iteration (queueWriter word) ⟪0, tail⟫ history (lh word)) :
    ∀ i ≤ lh word, π₁ (znth history i) = i := by
  exact ran.clock (pi₁_pair _ _) (fun state => by simp [queueWriter])

theorem encodedQueueAt_end {word history tail : V}
    (ran : Iteration (queueWriter word) ⟪0, tail⟫ history (lh word)) :
    encodedQueueAt word history (lh word) = tail := by
  simp [encodedQueueAt, ran.begins]

theorem encodedQueueAt_cons {word history tail i : V}
    (ran : Iteration (queueWriter word) ⟪0, tail⟫ history (lh word)) (hi : i < lh word) :
    encodedQueueAt word history i = packetWithTail (znth word i)
      (encodedQueueAt word history (i + 1)) + 1 := by
  let later := lh word - (i + 1)
  have clock : lh word - i = later + 1 := by
    simpa only [zero_add, add_zero] using (sub_succ_add_succ hi (0 : V)).symm
  have bound : later < lh word := by
    have pred : lh word - i ≤ lh word := sub_le_self _ _
    exact succ_le_iff_lt.mp (clock ▸ pred)
  have idx : lh word - (later + 1) = i := by
    rw [← clock, tsub_tsub_cancel_of_le (le_of_lt hi)]
  unfold encodedQueueAt
  rw [clock, ran.advances later bound]
  simp [queueWriter, queueWriter_index ran later (le_of_lt bound), idx, later]

theorem queueWriter_exists (word tail : V) :
    ∃ history, Iteration (queueWriter word) ⟪0, tail⟫ history (lh word) :=
  Iteration.exists _ (queueWriter_defined word) _ _

end I0451.Arithmetization
