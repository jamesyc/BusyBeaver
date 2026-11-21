module
public import I3_380.Arithmetic.Numerals
public import I3_380.LiteralRows
@[expose] public section

namespace PalomarI3380.ArithmeticMachine

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

def totalStep (m : Machine) (c : Configuration) : Configuration := (PalomarI3380.step m c).getD c

def totalRun (m : Machine) : Nat → Configuration → Configuration
  | 0, c => c
  | n+1, c => totalRun m n (totalStep m c)

theorem totalRun_last (m : Machine) (n : Nat) (c : Configuration) :
    totalRun m (n+1) c = totalStep m (totalRun m n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => exact ih (totalStep m c)

noncomputable def encodeLiteral (c : Configuration) : Nat := encode c.state c.left c.right

@[simp] theorem encodeLiteral_blank : encodeLiteral blank = 0 := by
  simp [encodeLiteral,blank,encode,Arithmetic.pair]

theorem ofNat_nat (n : Nat) [n.AtLeastTwo] :
    @OfNat.ofNat Nat n (@instOfNatAtLeastTwo Nat n (Arithmetic.natCast Nat) _) = n :=
  Arithmetic.natCast_nat n

theorem tick_nat (m : Machine) (c : Configuration) :
    tick m.workingStates m.packedRows (encodeLiteral c) = encodeLiteral (totalStep m c) := by
  obtain ⟨q,l,r⟩ := c
  have row : digit m.packedRows q r = m.row q (Nat.mod r 2) := digit_nat_as_row m q r
  let d := m.row q (Nat.mod r 2)
  have decoded : tick m.workingStates m.packedRows (encodeLiteral ⟨q,l,r⟩) =
      if q < m.workingStates then
        if Nat.mod d 2 = 1 then encode (Nat.div d 4) (2*l+Nat.mod (Nat.div d 2) 2) (Nat.div r 2)
        else encode (Nat.div d 4) (Nat.div l 2)
          (4*Nat.div r 2 + 2*Nat.mod (Nat.div d 2) 2 + Nat.mod l 2)
      else encode q l r := by
    simp only [tick,encodeLiteral,encode,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair,row,Arithmetic.natCast_nat,
      ofNat_nat,remIn_nat,divIn_nat,d]
  by_cases work : q < m.workingStates
  · rw [decoded,ite_eq_left work,totalStep,step_from_row m q l r work]
    simp only [Option.getD_some]
    by_cases direction : Nat.mod d 2 = 1 <;> simp only [d, direction, ↓reduceIte,encodeLiteral]
  · have stop := (step_none_iff m ⟨q,l,r⟩).mpr (Nat.le_of_not_gt work)
    rw [decoded,ite_eq_right work,totalStep,stop,Option.getD_none]
    rfl

theorem clock_nat (m : Machine) (n : Nat) (c : Configuration) :
    clock m.workingStates m.packedRows n (encodeLiteral c) = encodeLiteral (totalRun m n c) := by
  induction n with
  | zero => exact clock_zero _ _ _
  | succ n ih => rw [clock_succ,ih,tick_nat,totalRun_last]

theorem totalRun_of_run (m : Machine) {n : Nat} {start stop : Configuration}
    (runTo : run m n start = some stop) : totalRun m n start = stop := by
  induction n generalizing start with
  | zero => exact Option.some.inj runTo
  | succ n ih =>
    cases first : PalomarI3380.step m start with
    | none => simp [run,first] at runTo
    | some next =>
      simpa only [totalRun,totalStep,first,Option.getD_some] using
        ih (by simpa only [run,first] using runTo)

theorem halts_iff_totalRun (m : Machine) (start : Configuration) :
    HaltsFrom m start ↔ ∃ n, PalomarI3380.step m (totalRun m n start) = none := by
  constructor
  · rintro ⟨n,finish,h,stop⟩
    exact ⟨n,(totalRun_of_run m h).symm ▸ stop⟩
  · rintro ⟨n,h⟩
    induction n generalizing start with
    | zero => exact ⟨0,start,rfl,h⟩
    | succ n ih =>
      cases first : PalomarI3380.step m start with
      | none => exact ⟨0,start,rfl,first⟩
      | some next =>
        obtain ⟨m,finish,running,stop⟩ := ih next (by simpa [totalRun,totalStep,first] using h)
        exact ⟨m+1,finish,by simpa only [run,first] using running,stop⟩

theorem haltsDef_nat_for (m : Machine) :
    (haltsDef m.workingStates m.packedRows).val.Evalb (![] : Fin 0 → Nat) ↔ HaltsFrom m blank := by
  rw [haltsDef_eval,halts_iff_totalRun,← encodeLiteral_blank]
  simp only [clock_nat]
  simp [encodeLiteral,encode,Arithmetic.pi₁_pair,Arithmetic.natCast_nat,step_none_iff,Nat.not_lt]

theorem haltsDef_nat :
    (haltsDef 380 packedLiteral).val.Evalb (![] : Fin 0 → Nat) ↔ HaltsFrom machine blank :=
  haltsDef_nat_for machine

end PalomarI3380.ArithmeticMachine
