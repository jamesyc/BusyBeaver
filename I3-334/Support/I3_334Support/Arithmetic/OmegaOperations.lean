module
public import I3_334Support.SetTheory.Recursion.NaturalIteration
public import I3_334Support.Logic.Arithmetic
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic
variable {A V : Type} {M : Algebra A}

namespace Definable

variable {N : SetContext M V}

theorem ternary_levels {r : V → V → V → Prop} (form : Nat → Nat → Nat → SetFormula)
    (bounded : ∀ {n a b c}, a < n → b < n → c < n → SetFormula.Scoped n (form a b c))
    (meaning : ∀ {n a b c} (env : Nat → V) (default : V), a < n → b < n → c < n →
      (SetFormula.holds N.mem (form a b c) n env default ↔ r (env a) (env b) (env c))) :
    Relation3 N r := by
  intro n a b c ha hb hc
  let i := n - (a+1)
  let j := n - (b+1)
  let k := n - (c+1)
  have hi : i < n := by dsimp [i]; omega
  have hj : j < n := by dsimp [j]; omega
  have hk : k < n := by dsimp [k]; omega
  have result := of_levels (S := N.square) (p := fun env => r (env i) (env j) (env k))
    (bounded hi hj hk) (fun env default => meaning env default hi hj hk)
  have vi : n - (i+1) = a := by dsimp [i]; omega
  have vj : n - (j+1) = b := by dsimp [j]; omega
  have vk : n - (k+1) = c := by dsimp [k]; omega
  simpa only [vi,vj,vk] using result

end Definable

namespace SetContext

variable (N : SetContext M V)

def IteratedValue (step : V → V → V → Prop) (a w start i x : V) : Prop :=
  ∃ graph, N.NaturalHistory step a graph w start i ∧ Internal.At N.mem graph i x

variable {step : V → V → V → Prop}

theorem iteratedValue_omega {a w start n x : V}
    (h : N.IteratedValue step a w start n x) : N.mem x w :=
  h.elim fun _ h => h.1.closed _ _ h.2

theorem iteratedValue_total {a w start n : V} (omega : Internal.Omega N.mem w)
    (startIn : N.mem start w) (nIn : N.mem n w) (stepDef : Definable.Relation3 N step)
    (total : ∀ x, N.mem x w → ∃ y, N.mem y w ∧ step a x y) :
    ∃ x, N.IteratedValue step a w start n x := by
  obtain ⟨g,history⟩ := N.naturalHistory_exists omega startIn stepDef total n nIn
  obtain ⟨x,edge,_⟩ := history.function.1 n ((N.mem_succ _ _).mpr (Or.inr rfl))
  exact ⟨x,g,history,edge⟩

theorem iteratedValue_unique {a w start n x y : V} (omega : Internal.Omega N.mem w) (ni : N.mem n w)
    (one : ∀ a u v w, step a u v → step a u w → v = w)
    (hx : N.IteratedValue step a w start n x) (hy : N.IteratedValue step a w start n y) : x = y := by
  obtain ⟨f,hf,fx⟩ := hx
  obtain ⟨g,hg,gy⟩ := hy
  have last := (N.mem_succ n n).mpr (Or.inr rfl)
  exact N.naturalHistory_agree omega ni ni hf hg one n ni last last x y fx gy

theorem iteratedValue_zero {a w start x : V} (startIn : N.mem start w) :
    N.IteratedValue step a w start N.empty x ↔ x = start := by
  constructor
  · rintro ⟨_,f,h⟩
    exact N.at_unique f.function h f.initial
  · rintro rfl
    obtain ⟨f,h⟩ := N.naturalHistory_zero (step := step) (a := a) startIn
    exact ⟨f,h,h.initial⟩

theorem iteratedValue_succ {a w start n x y : V} (omega : Internal.Omega N.mem w) (ni : N.mem n w)
    (one : ∀ a u v w, step a u v → step a u w → v = w)
    (total : ∀ x, N.mem x w → ∃ y, N.mem y w ∧ step a x y)
    (prev : N.IteratedValue step a w start n x) (next : step a x y) :
    N.IteratedValue step a w start (N.succ n) y := by
  obtain ⟨f,hf,first⟩ := prev
  obtain ⟨g,hg,keep⟩ := N.naturalHistory_extend omega ni hf total
  obtain ⟨before,after,read,written,update⟩ := hg.stepwise n ((N.mem_succ _ _).mpr (Or.inr rfl))
  have source := N.at_unique hg.function read (keep _ _ first)
  subst before
  have target := one a x after y update next
  exact ⟨g,hg,target ▸ written⟩

def AddStep (_ x y : V) : Prop := Internal.Succ N.mem x y

theorem addStep_def : Definable.Relation3 N N.AddStep :=
  fun _ hx hy => Definable.successor hx hy

theorem addStep_unique (a x y z : V) (left : N.AddStep a x y) (right : N.AddStep a x z) : y = z :=
  ((N.internal_succ _ _).mp left).trans ((N.internal_succ _ _).mp right).symm

theorem addStep_total {w : V} (omega : Internal.Omega N.mem w) (a x : V) (hx : N.mem x w) :
    ∃ y, N.mem y w ∧ N.AddStep a x y :=
  ⟨N.succ x,N.omega_succ omega hx,N.mem_succ x⟩

private theorem finite_iteration_iff {w a b c : V} (omega : Internal.Omega N.mem w)
    (start : V → V) :
    (Internal.NatObject N.mem a ∧ Internal.NatObject N.mem b ∧ Internal.NatObject N.mem c ∧
      ∃ z d f, Internal.Empty N.mem z ∧ Internal.Succ N.mem b d ∧
        Internal.FunctionOn N.mem f d ∧ Internal.At N.mem f z (start z) ∧ Internal.At N.mem f b c ∧
        (∀ i x, N.mem i d → Internal.At N.mem f i x → Internal.NatObject N.mem x) ∧
        ∀ i, N.mem i b → ∃ j x y, Internal.Succ N.mem i j ∧ Internal.At N.mem f i x ∧
          Internal.At N.mem f j y ∧ step a x y) ↔
      N.mem a w ∧ N.mem b w ∧ N.IteratedValue step a w (start N.empty) b c := by
  constructor
  · rintro ⟨ha,hb,_,z,d,f,hz,hd,fn,initial,last,closed,updates⟩
    have eqZ := (N.empty_unique z).mp hz
    have eqD := (N.internal_succ b d).mp hd
    subst z d
    refine ⟨(N.natObject_iff omega _).mp ha,(N.natObject_iff omega _).mp hb,f,
      ⟨fn,initial,fun i x edge => (N.natObject_iff omega _).mp (closed i x (SetRecursion.at_domain fn edge) edge),
       fun i hi => ?_⟩,last⟩
    obtain ⟨j,x,y,succ,first,next,update⟩ := updates i hi
    rw [(N.internal_succ i j).mp succ] at next
    exact ⟨x,y,first,next,update⟩
  · rintro ⟨aIn,bIn,f,hf,last⟩
    exact ⟨(N.natObject_iff omega _).mpr aIn,(N.natObject_iff omega _).mpr bIn,
      (N.natObject_iff omega _).mpr (hf.closed _ _ last),N.empty,N.succ b,f,N.empty_mem,N.mem_succ _,
      hf.function,hf.initial,last,fun i x _ edge => (N.natObject_iff omega _).mpr (hf.closed i x edge),
      fun i hi => by
        obtain ⟨x,y,first,next,step⟩ := hf.stepwise i hi
        exact ⟨N.succ i,x,y,N.mem_succ i,first,next,step⟩⟩

theorem add_iff_history {w a b c : V} (omega : Internal.Omega N.mem w) :
    Internal.Add N.mem a b c ↔ N.mem a w ∧ N.mem b w ∧ N.IteratedValue N.AddStep a w a b c :=
  N.finite_iteration_iff (step := N.AddStep) (a := a) (b := b) (c := c) omega (fun _ => a)

theorem add_total {w a b : V} (omega : Internal.Omega N.mem w) (ha : N.mem a w) (hb : N.mem b w) :
    ∃ c, Internal.Add N.mem a b c := by
  obtain ⟨c,hc⟩ := N.iteratedValue_total (a := a) omega ha hb N.addStep_def (N.addStep_total omega a)
  exact ⟨c,(N.add_iff_history omega).mpr ⟨ha,hb,hc⟩⟩

theorem add_unique {w a b c d : V} (omega : Internal.Omega N.mem w)
    (left : Internal.Add N.mem a b c) (right : Internal.Add N.mem a b d) : c = d := by
  have l := (N.add_iff_history omega).mp left
  have r := (N.add_iff_history omega).mp right
  exact N.iteratedValue_unique omega l.2.1 N.addStep_unique l.2.2 r.2.2

theorem add_zero {w a : V} (omega : Internal.Omega N.mem w) (ha : N.mem a w) :
    Internal.Add N.mem a N.empty a :=
  (N.add_iff_history omega).mpr ⟨ha,N.omega_zero omega,(N.iteratedValue_zero ha).mpr rfl⟩

theorem add_succ {w a b c : V} (omega : Internal.Omega N.mem w)
    (h : Internal.Add N.mem a b c) : Internal.Add N.mem a (N.succ b) (N.succ c) := by
  have stored := (N.add_iff_history omega).mp h
  exact (N.add_iff_history omega).mpr ⟨stored.1,N.omega_succ omega stored.2.1,
    N.iteratedValue_succ omega stored.2.1 N.addStep_unique (N.addStep_total omega a) stored.2.2 (N.mem_succ _)⟩

theorem add_def : Definable.Relation3 N (Internal.Add N.mem) :=
  Definable.ternary_levels SetFormula.addition SetFormula.scope_addition
    (fun env default => SetFormula.holds_addition (env := env) (default := default))

def MulStep (a x y : V) : Prop := Internal.Add N.mem x a y

theorem mulStep_def : Definable.Relation3 N N.MulStep :=
  fun ha hx hy => N.add_def hx ha hy

theorem mulStep_unique {w : V} (omega : Internal.Omega N.mem w)
    (a x y z : V) (left : N.MulStep a x y) (right : N.MulStep a x z) : y = z :=
  N.add_unique omega left right

theorem mulStep_total {w a : V} (omega : Internal.Omega N.mem w) (ha : N.mem a w) (x : V)
    (hx : N.mem x w) : ∃ y, N.mem y w ∧ N.MulStep a x y := by
  obtain ⟨y,hy⟩ := N.add_total omega hx ha
  exact ⟨y,(N.natObject_iff omega _).mp hy.2.2.1,hy⟩

theorem mul_iff_history {w a b c : V} (omega : Internal.Omega N.mem w) :
    Internal.Mul N.mem a b c ↔ N.mem a w ∧ N.mem b w ∧ N.IteratedValue N.MulStep a w N.empty b c :=
  N.finite_iteration_iff (step := N.MulStep) (a := a) (b := b) (c := c) omega id

theorem mul_total {w a b : V} (omega : Internal.Omega N.mem w) (ha : N.mem a w) (hb : N.mem b w) :
    ∃ c, Internal.Mul N.mem a b c := by
  obtain ⟨c,hc⟩ := N.iteratedValue_total omega (N.omega_zero omega) hb N.mulStep_def (N.mulStep_total omega ha)
  exact ⟨c,(N.mul_iff_history omega).mpr ⟨ha,hb,hc⟩⟩

theorem mul_unique {w a b c d : V} (omega : Internal.Omega N.mem w)
    (left : Internal.Mul N.mem a b c) (right : Internal.Mul N.mem a b d) : c = d := by
  have l := (N.mul_iff_history omega).mp left
  have r := (N.mul_iff_history omega).mp right
  exact N.iteratedValue_unique omega l.2.1 (N.mulStep_unique omega) l.2.2 r.2.2

theorem mul_zero {w a : V} (omega : Internal.Omega N.mem w) (ha : N.mem a w) :
    Internal.Mul N.mem a N.empty N.empty :=
  (N.mul_iff_history omega).mpr ⟨ha,N.omega_zero omega,
    (N.iteratedValue_zero (N.omega_zero omega)).mpr rfl⟩

theorem mul_succ {w a b c d : V} (omega : Internal.Omega N.mem w)
    (mul : Internal.Mul N.mem a b c) (add : Internal.Add N.mem c a d) :
    Internal.Mul N.mem a (N.succ b) d := by
  have stored := (N.mul_iff_history omega).mp mul
  exact (N.mul_iff_history omega).mpr ⟨stored.1,N.omega_succ omega stored.2.1,
    N.iteratedValue_succ omega stored.2.1 (N.mulStep_unique omega) (N.mulStep_total omega stored.1)
      stored.2.2 add⟩

theorem mul_def : Definable.Relation3 N (Internal.Mul N.mem) :=
  Definable.ternary_levels SetFormula.multiplication SetFormula.scope_multiplication
    (fun env default => SetFormula.holds_multiplication (env := env) (default := default))

theorem add_numerals {w : V} (omega : Internal.Omega N.mem w) (a b : Nat) :
    Internal.Add N.mem (N.numeral a) (N.numeral b) (N.numeral (a+b)) := by
  induction b with
  | zero => exact N.add_zero omega (N.numeral_in_omega omega a)
  | succ b h => exact N.add_succ omega h

theorem mul_numerals {w : V} (omega : Internal.Omega N.mem w) (a b : Nat) :
    Internal.Mul N.mem (N.numeral a) (N.numeral b) (N.numeral (a*b)) := by
  induction b with
  | zero => exact N.mul_zero omega (N.numeral_in_omega omega a)
  | succ b h => exact N.mul_succ omega h (N.add_numerals omega (a*b) a)

end SetContext
end PalomarI3380.SquareRepresentation
