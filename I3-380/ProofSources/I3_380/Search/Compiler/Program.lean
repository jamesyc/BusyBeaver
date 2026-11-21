module
public import Std
@[expose] public section

namespace PalomarI3380.Compiler

abbrev Register := Fin 12
abbrev Store (V : Type := Nat) := Register → V

def Store.set {V : Type} (s : Store V) (r : Register) (v : V) : Store V :=
  fun i => if i = r then v else s i

@[simp] theorem Store.get_set {V : Type} (s : Store V) (r : Register) (v : V) : s.set r v r = v := by
  simp [Store.set]

theorem Store.get_set_other {V : Type} (s : Store V) (r i : Register) (v : V) (different : i ≠ r) :
    s.set r v i = s i := by
  simp [Store.set, different]

namespace Store

theorem set_set {V : Type} (s : Store V) (r : Register) (a b : V) : (s.set r a).set r b = s.set r b := by
  funext i
  by_cases h : i = r <;> simp [set, h]

theorem set_comm {V : Type} (s : Store V) {a b : Register} (h : a ≠ b) (x y : V) :
    (s.set a x).set b y = (s.set b y).set a x := by
  funext i
  by_cases ha : i = a <;> by_cases hb : i = b <;> simp_all [set]

theorem set_same {V : Type} (s : Store V) (r : Register) : s.set r (s r) = s := by
  funext i
  by_cases h : i = r <;> simp [set, h]

end Store

inductive Op where
  | inc (r : Register)
  | decNZ (r : Register)
  | break_ (zeros : Nat)
  | continue_ (extraOnes : Nat)
  | halt
  deriving DecidableEq, Repr

inductive Program where
  | op (instruction : Op)
  | seq (left right : Program)
  deriving DecidableEq, Repr

/-- Control at a binary sequence. Break counts left edges and continue
counts right edges. The counts encoded in the table are lexical depths. -/
inductive Flow where
  | normal
  | escape (extraZeros : Nat)
  | repeatAt (extraOnes : Nat)
  | halt
  deriving DecidableEq, Repr

def Op.effect {V : Type} [OfNat V 0] [OfNat V 1] [Add V] [Sub V] [DecidableEq V] :
    Op → Store V → Flow × Store V
  | .inc r, s => (.normal, s.set r (s r + 1))
  | .decNZ r, s =>
    if s r = 0 then (.escape 0, s) else (.normal, s.set r (s r - 1))
  | .break_ 0, s => (.normal, s)
  | .break_ (n + 1), s => (.escape n, s)
  | .continue_ n, s => (.repeatAt n, s)
  | .halt, s => (.halt, s)

def Flow.fromLeft : Flow → Option Flow
  | .normal => none
  | .escape 0 => some .normal
  | .escape (n + 1) => some (.escape n)
  | other => some other

def Flow.fromRight : Flow → Option Flow
  | .repeatAt 0 => none
  | .repeatAt (n + 1) => some (.repeatAt n)
  | other => some other

/-- Structured evaluation of the binary register program. The loop rule
only applies after a continue at the owning right edge. -/
inductive Executes : Program → Store → Flow → Store → Prop where
  | instruction (op : Op) (s : Store) : Executes (.op op) s (op.effect s).1 (op.effect s).2
  | leftExit {flow : Flow} : Executes left s flow t → flow.fromLeft = some out →
      Executes (.seq left right) s out t
  | rightExit {flow : Flow} : Executes left s .normal middle → Executes right middle flow t →
      flow.fromRight = some out → Executes (.seq left right) s out t
  | reenter : Executes left s .normal middle → Executes right middle (.repeatAt 0) next →
      Executes (.seq left right) next out t → Executes (.seq left right) s out t

/-- A structural upper bound on the two kinds of unconsumed jump. -/
def Program.needs : Program → Nat × Nat
  | .op (.decNZ _) => (1, 0)
  | .op (.break_ n) => (n, 0)
  | .op (.continue_ n) => (0, n + 1)
  | .op _ => (0, 0)
  | .seq l r => (max (l.needs.1 - 1) r.needs.1, max l.needs.2 (r.needs.2 - 1))

def Flow.fits (out : Flow) (needs : Nat × Nat) : Prop :=
  match out with
  | .escape n => n + 1 ≤ needs.1
  | .repeatAt n => n + 1 ≤ needs.2
  | _ => True

theorem leftFits {flow out : Flow} {l r : Nat × Nat}
    (h : flow.fits l) (next : flow.fromLeft = some out) :
    out.fits (max (l.1 - 1) r.1, max l.2 (r.2 - 1)) := by
  cases flow with
  | normal => simp [Flow.fromLeft] at next
  | halt => cases next; trivial
  | repeatAt k =>
    cases next
    exact Nat.le_trans h (Nat.le_max_left _ _)
  | escape k =>
    cases k with
    | zero => cases next; trivial
    | succ k =>
      simp only [Flow.fromLeft, Option.some.injEq] at next
      subst out
      simp only [Flow.fits] at h ⊢
      omega

theorem rightFits {flow out : Flow} {l r : Nat × Nat}
    (h : flow.fits r) (next : flow.fromRight = some out) :
    out.fits (max (l.1 - 1) r.1, max l.2 (r.2 - 1)) := by
  cases flow with
  | normal => cases next; trivial
  | halt => cases next; trivial
  | escape k =>
    cases next
    exact Nat.le_trans h (Nat.le_max_right _ _)
  | repeatAt k =>
    cases k with
    | zero => simp [Flow.fromRight] at next
    | succ k =>
      simp only [Flow.fromRight, Option.some.injEq] at next
      subst out
      simp only [Flow.fits] at h ⊢
      omega

theorem Executes.bounded {p : Program} {s t : Store} {control : Flow} (h : Executes p s control t) :
    control.fits p.needs := by
  induction h with
  | instruction op s =>
    cases op with
    | inc => trivial
    | decNZ r =>
      by_cases hz : s r = 0 <;> simp [Op.effect, Program.needs, Flow.fits, hz]
    | break_ n => cases n <;> simp [Op.effect, Program.needs, Flow.fits]
    | continue_ n => simp [Op.effect, Program.needs, Flow.fits]
    | halt => trivial
  | leftExit _ next ih => exact leftFits ih next
  | rightExit _ _ next _ ih => exact rightFits ih next
  | reenter _ _ _ _ _ ih => exact ih

def Program.closed (p : Program) : Prop := p.needs = (0, 0)

theorem Program.closed_seq {p q : Program} (hp : p.closed) (hq : q.closed) :
    (Program.seq p q).closed := by
  simp only [Program.closed] at hp hq ⊢
  simp [Program.needs, hp, hq]

theorem Executes.closed_flow {p : Program} {s t : Store} {out : Flow}
    (hp : p.closed) (h : Executes p s out t) :
    out = .normal ∨ out = .halt := by
  have fits := h.bounded
  rw [Program.closed] at hp
  rw [hp] at fits
  cases out <;> simp [Flow.fits] at fits ⊢

end PalomarI3380.Compiler
