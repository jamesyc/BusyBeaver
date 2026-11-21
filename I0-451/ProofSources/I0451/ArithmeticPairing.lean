module
public import I0451.ArithmeticLoops
public import I0451.ArithmeticCantor

/-! The literal pairing loop in arithmetic. Its invariant is conservation
of the sum of the accumulator and the Cantor code of the remaining pair. -/

@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def modelFillPair (a b out : Fin 9) (s : Fin 9 → V) : Fin 9 → V :=
  putRegister (modelAddAt (fun j => j == a || j == out) (s b) s) b 0

def modelRotatePair (a b out : Fin 9) (s : Fin 9 → V) : Fin 9 → V :=
  modelTransfer a b (putRegister s out (s out + 1))

noncomputable def modelPaired (a b out : Fin 9) (s : Fin 9 → V) : Fin 9 → V :=
  putRegister (putRegister (putRegister s a 0) b 0) out (s out + cantor (s a) (s b))

private theorem zero_case_definable (x : V) (f : V → V) (defined : 𝚺ᴬ₁-Function₁[V] f) :
    𝚺ᴬ₁-Function₁[V] (fun j => if j = 0 then x else f j) := by
  change 𝚺ᴬ₁.Definable (V := V) (fun v : Fin 2 → V => v 0 = if v 1 = 0 then x else f (v 1))
  have graph : (fun v : Fin 2 → V => v 0 = if v 1 = 0 then x else f (v 1)) =
      (fun v : Fin 2 → V => (v 1 = 0 ∧ v 0 = x) ∨ (v 1 ≠ 0 ∧ v 0 = f (v 1))) := by
    funext v
    apply propext
    by_cases zero : v 1 = 0 <;> simp [zero]
  rw [graph]
  definability

/-- Exact effect of the concrete pairing-loop shape. -/
theorem model_pair {root test cycle : Cursor} {fill move : Edge} {a b out : Fin 9}
    (ab : a ≠ b) (ao : a ≠ out) (bo : b ≠ out)
    (left : outgoing root false = some fill)
    (right : outgoing root true = some (.branch test))
    (dec : outgoing test false = some (.instruction (.dec a)))
    (onPositive : outgoing test true = some (.branch cycle))
    (moveEdge : outgoing cycle false = some move)
    (backEdge : outgoing cycle true = some (.instruction (.restart 2)))
    (moveIn : ∀ s : Fin 9 → V, ModelEffect fill s .normal (modelFillPair a b out s))
    (moveBack : ∀ s : Fin 9 → V, ModelEffect move s .normal (modelRotatePair a b out s))
    (s : Fin 9 → V) :
    ModelEffect (.branch root) s .normal (modelPaired a b out s) := by
  let count := s a + s b
  let total := s out + cantor (s a) (s b)
  let states (j : V) (i : Fin 9) : V :=
    if j = 0 then s i
    else if i = a then 0
    else if i = b then count - j
    else if i = out then total - cantor 0 (count - j)
    else s i
  have start : states 0 = s := by funext i; simp [states]
  have defined (i : Fin 9) : 𝚺ᴬ₁-Function₁[V] (fun j => states j i) := by
    by_cases ia : i = a <;> by_cases ib : i = b <;> by_cases io : i = out <;>
      simp only [states, ia, ib, io, ite_true, ite_false] <;> apply zero_case_definable <;> definability
  have kept (j : V) (i : Fin 9) (ha : i ≠ a) (hb : i ≠ b) (ho : i ≠ out) :
      states j i = s i := by simp [states, ha, hb, ho]
  have sum (j : V) : states j a + states j b = count - j := by
    by_cases zero : j = 0 <;> simp [states, count, zero, Ne.symm ab]
  have conservation (j : V) (fits : j ≤ count) :
      states j out + cantor (states j a) (states j b) = total := by
    by_cases zero : j = 0
    · simp [states, total, zero]
    · have decompose : count - j + j = count := sub_add_self_of_le fits
      have reduced : count - j < count :=
        calc count - j < count - j + j := lt_add_of_pos_right _ (pos_iff_ne_zero.mpr zero)
          _ = count := decompose
      have smaller : cantor 0 (count - j) < cantor (s a) (s b) :=
        cantor_diagonal_lt 0 (count - j) (s a) (s b) (by simpa only [zero_add, count] using reduced)
      have below : cantor 0 (count - j) ≤ total :=
        le_trans (le_of_lt smaller) (by simp [total])
      simpa only [states, ite_eq_right zero, Ne.symm ao, Ne.symm bo, Ne.symm ab, ite_true, ite_false]
        using sub_add_self_of_le below
  have testLoop (j : V) (more : j < count) :
      ModelEffect (.branch test) (modelFillPair a b out (states j)) (.restart 0) (states (j + 1)) := by
    let n := count - (j + 1)
    let before := states j
    let filled := modelFillPair a b out before
    let reduced := putRegister filled a n
    let rotated := modelRotatePair a b out reduced
    have pos : count - j = n + 1 := by
      simpa only [n, add_zero, zero_add] using (sub_succ_add_succ more (0 : V)).symm
    have first : filled a = n + 1 := by
      simpa [filled, modelFillPair, modelAddAt, putRegister, ab, before, sum j] using pos
    have atB : filled b = 0 := putRegister_at _ _ _
    have accumulated : filled out = before out + before b := by
      simp [filled, modelFillPair, modelAddAt, putRegister, Ne.symm bo]
    have newA : rotated a = 0 := putRegister_at _ _ _
    have newB : rotated b = n := by
      simp [rotated, modelRotatePair, modelTransfer, putRegister, modelAddAt,
        Ne.symm ab, ao, bo, reduced, atB]
    have newOut : rotated out = before out + before b + 1 := by
      simp [rotated, modelRotatePair, modelTransfer, putRegister, modelAddAt,
        Ne.symm ao, Ne.symm bo, reduced, accumulated]
    have totalEq : total = (before out + before b + 1) + cantor 0 n := by
      have invariant := conservation j (le_of_lt more)
      have rewrite : cantor (before a) (before b) = before b + 1 + cantor 0 n :=
        cantor_descend ((sum j).trans pos)
      rw [rewrite] at invariant
      rw [← invariant]
      ac_rfl
    have newValue : total - cantor 0 n = before out + before b + 1 :=
      sub_remove_left totalEq
    have newValue' : total - cantor 0 (count - (j + 1)) = before out + before b + 1 := newValue
    have nonzero : j + 1 ≠ 0 := by simp
    have same : rotated = states (j + 1) := by
      funext i
      by_cases ia : i = a
      · subst i
        simpa only [states, ite_eq_right nonzero, ite_true] using newA
      · by_cases ib : i = b
        · subst i
          simpa only [states, ite_eq_right nonzero, ite_eq_right (Ne.symm ab), ite_true, n] using newB
        · by_cases io : i = out
          · subst i
            simpa only [states, ite_eq_right nonzero, ite_eq_right (Ne.symm ao),
              ite_eq_right (Ne.symm bo), ite_true, ite_false, newValue'] using newOut
          · simp only [kept _ _ ia ib io]
            simp [rotated, modelRotatePair, modelTransfer, putRegister, modelAddAt, ia, ib, io,
              reduced, filled, modelFillPair, before, kept _ _ ia ib io]
    have spin : ModelEffect (.branch cycle) reduced (.restart 1) rotated :=
      .rightExit moveEdge backEdge (moveBack reduced) (.restartLeaf 2 _) rfl
    rw [same] at spin
    exact .rightExit dec onPositive (.dec_pos a filled n first) spin rfl
  have finish : ModelEffect (.branch root) (states count) .normal (modelPaired a b out s) := by
    let final := states count
    have sumZero : final a + final b = 0 := by rw [sum count, Arithmetic.sub_self]
    have zeroA : final a = 0 := (add_eq_zero.mp sumZero).1
    have zeroB : final b = 0 := (add_eq_zero.mp sumZero).2
    have outTotal : final out = total := by
      have inv := conservation count (le_refl _)
      simpa only [final, zeroA, zeroB, cantor_zero, add_zero] using inv
    have result : modelFillPair a b out final = modelPaired a b out s := by
      funext i
      by_cases ia : i = a
      · subst i
        simp [modelFillPair, modelPaired, modelAddAt, putRegister, ab, ao, zeroA, zeroB]
      · by_cases ib : i = b
        · subst i
          simp [modelFillPair, modelPaired, putRegister, bo]
        · by_cases io : i = out
          · subst i
            simp [modelFillPair, modelPaired, modelAddAt, putRegister, Ne.symm bo, zeroB, outTotal, total]
          · simp [modelFillPair, modelPaired, modelAddAt, putRegister, ia, ib, io, final,
              kept count i ia ib io]
    have returned : ModelEffect (.branch test) (modelFillPair a b out final) .normal
        (modelFillPair a b out final) := by
      apply ModelEffect.leftExit dec (ModelEffect.dec_zero a _ ?_) rfl
      simp [modelFillPair, putRegister, modelAddAt, ab, zeroA, zeroB]
    rw [result] at returned
    have filled := moveIn final
    rw [result] at filled
    exact ModelEffect.sequence left right filled returned
  have all := ModelEffect.repeat_until left right states count defined (fun j _ => moveIn (states j))
    testLoop finish
  rwa [start] at all

end I0451.Arithmetization
