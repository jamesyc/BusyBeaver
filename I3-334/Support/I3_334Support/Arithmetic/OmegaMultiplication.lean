module
public import I3_334Support.Arithmetic.OmegaAddition
@[expose] public section

namespace PalomarI3380.Logic.Expanded.OmegaDomain

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {V : Type} {E G : V → V → Prop}
variable {L : ClassAxioms E G} {inhabited : Nonempty V} (D : OmegaDomain L inhabited)

local notation "W" => D.Points

theorem times_one (a : W) : a * 1 = a := by
  change a * D.successor 0 = a
  rw [D.times_succ,D.times_zero,D.zero_plus]

theorem zero_times (b : W) : 0 * b = 0 := by
  refine D.induction_via (P := fun i => 0*i = 0) (“i. 0 * i = 0” : ArithmeticSemisentence 1) Empty.elim
    (fun i => by simp) (D.times_zero 0) (fun i ih => ?_) b
  rw [D.times_succ,D.plus_zero,ih]

theorem succ_times (a b : W) : D.successor a * b = a*b+b := by
  refine D.induction_via (P := fun i => D.successor a * i = a*i+i) (“i. (&(0 : Fin 1) + 1) * i = &(0 : Fin 1) * i + i” :
    ArithmeticSemiformula (Fin 1) 1) ![a] (fun i => by simp [D.plus_one])
    (by rw [D.times_zero,D.times_zero,D.plus_zero]) (fun i ih => ?_) b
  rw [D.times_succ,ih,D.times_succ,D.plus_succ,D.plus_succ,D.plus_swap (a*i) i a]

theorem times_comm (a b : W) : a*b = b*a := by
  refine D.induction_via (P := fun i => a*i = i*a) (“i. &(0 : Fin 1) * i = i * &(0 : Fin 1)” :
    ArithmeticSemiformula (Fin 1) 1) ![a] (fun i => by simp)
    (by rw [D.times_zero,D.zero_times]) (fun i ih => ?_) b
  rw [D.times_succ,D.succ_times,ih]

theorem times_plus (a b c : W) : a*(b+c) = a*b+a*c := by
  refine D.induction_via (P := fun i => a*(b+i) = a*b+a*i) (“i. &(0 : Fin 2) * (&(1 : Fin 2) + i) =
    &(0 : Fin 2) * &(1 : Fin 2) + &(0 : Fin 2) * i” : ArithmeticSemiformula (Fin 2) 1)
    ![a,b] (fun i => by simp) (by rw [D.plus_zero,D.times_zero,D.plus_zero]) (fun i ih => ?_) c
  rw [D.plus_succ,D.times_succ,ih,D.times_succ,D.plus_assoc]

theorem times_assoc (a b c : W) : (a*b)*c = a*(b*c) := by
  refine D.induction_via (P := fun i => (a*b)*i = a*(b*i)) (“i. (&(0 : Fin 2) * &(1 : Fin 2)) * i = &(0 : Fin 2) * (&(1 : Fin 2) * i)” :
    ArithmeticSemiformula (Fin 2) 1) ![a,b] (fun i => by simp)
    (by rw [D.times_zero,D.times_zero,D.times_zero]) (fun i ih => ?_) c
  rw [D.times_succ,ih,D.times_succ,D.times_plus]

theorem times_lt_times {a b : W} (ab : a < b) {c : W} (pos : 0 < c) : a*c < b*c := by
  refine D.induction_via (P := fun i => 0 < i → a*i < b*i) (“i. 0 < i → &(0 : Fin 2) * i < &(1 : Fin 2) * i” :
    ArithmeticSemiformula (Fin 2) 1) ![a,b] (fun i => by simp)
    (fun h => (D.lt_irrefl 0 h).elim) (fun i ih _ => ?_) c pos
  rw [D.times_succ,D.times_succ]
  rcases D.zero_le i with h | rfl
  · exact D.lt_trans (D.plus_lt_plus (ih h) a) (D.plus_lt_plus_left ab (b*i))
  · simpa only [D.times_zero,D.zero_plus] using ab

end PalomarI3380.Logic.Expanded.OmegaDomain
