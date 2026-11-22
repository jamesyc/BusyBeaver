module
public import ZF192.Machine.Literal
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Bits

@[expose] public section

namespace M192.Startup
open BinaryTape

/-- State, left tape, and tape from the head onward, with the nearest bit first. -/
abbrev Packed := Nat × Nat × Nat

/-- Indexed access to the literal rows, with the same default as the list machine. -/
def replayRows : Array (M192.Row × M192.Row) := literalRows.toArray

def packedLiteral (q : Nat) (b : Bool) : M192.Row :=
  let row := replayRows[q]?.getD (none, none)
  if b then row.2 else row.1

theorem packedLiteral_eq (q : Nat) (b : Bool) : packedLiteral q b = literal q b := by
  simp [packedLiteral, replayRows, literal, tmOf, List.getD_eq_getElem?_getD]

def packedStep : Packed → Option Packed
  | (q,l,r) =>
    match packedLiteral q (Nat.bodd r) with
    | none => none
    | some (w, true, next) => some (next, Nat.bit w l, Nat.div2 r)
    | some (w, false, next) =>
      some (next, Nat.div2 l, Nat.bit (Nat.bodd l) (Nat.bit w (Nat.div2 r)))

def packedRun : Nat → Packed → Option Packed
  | 0, c => some c
  | n+1, c => (packedStep c).bind (packedRun n)

theorem packedRun_add (a b : Nat) (c : Packed) :
    packedRun (a+b) c = (packedRun a c).bind (packedRun b) := by
  induction a generalizing c with
  | zero => simp [packedRun]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [packedRun]
    cases packedStep c with
    | none => rfl
    | some d => exact ih d

def tapeCode : List Bool → Nat
  | [] => 0
  | b :: bs => Nat.bit b (tapeCode bs)

private theorem code_trim (bs : List Bool) : tapeCode (trim bs) = tapeCode bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [trim_cons]
    split
    · rename_i h
      have hzero : tapeCode bs = 0 := by rw [← ih, h.2]; rfl
      simp [tapeCode, h.1, hzero]
    · simp only [tapeCode, ih]

private theorem bits_code (bs : List Bool) : (tapeCode bs).bits = trim bs := by
  induction bs with
  | nil => simp [tapeCode]
  | cons b bs ih =>
    rw [tapeCode, trim_cons]
    split
    · rename_i h
      rw [h.1, ← code_trim bs, h.2]
      rfl
    · rename_i h
      rw [Nat.bits_append_bit, ih]
      intro hz
      have hbs : trim bs = [] := by rw [← ih, hz, Nat.zero_bits]
      cases b
      · exact False.elim (h ⟨rfl,hbs⟩)
      · rfl

private theorem code_head (bs : List Bool) : Nat.bodd (tapeCode bs) = bs.headD false := by
  cases bs <;> simp [tapeCode]

private theorem code_tail (bs : List Bool) : Nat.div2 (tapeCode bs) = tapeCode bs.tail := by
  cases bs <;> simp [tapeCode]

def pack (c : Conf) : Packed := (c.q, tapeCode c.l, tapeCode c.r)

def unpack : Packed → Conf
  | (q,l,r) => ⟨q, l.bits, r.bits⟩

private def normalize (c : Conf) : Conf := zc c.q c.l c.r

private theorem unpack_pack (c : Conf) : unpack (pack c) = normalize c := by
  cases c
  simp [unpack, pack, normalize, zc, bits_code]

theorem pack_step (c : Conf) : (step literal c).map pack = packedStep (pack c) := by
  obtain ⟨q,l,r⟩ := c
  simp only [step, packedStep, pack, code_head, packedLiteral_eq]
  cases h : literal q (r.headD false) with
  | none => rfl
  | some row =>
    obtain ⟨w,d,next⟩ := row
    cases d <;> simp [pack, zc, zl, code_trim, code_tail, tapeCode]

theorem pack_run (n : Nat) (c : Conf) : (run literal n c).map pack = packedRun n (pack c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [run, packedRun, ← pack_step]
    cases step literal c with
    | none => rfl
    | some d => exact ih d

private theorem step_normalize (c : Conf) : (step literal c).map normalize = step literal c := by
  unfold step
  split <;> simp [normalize, zc, zl, trim_trim]

private theorem run_normalize (n : Nat) (c : Conf) (hc : normalize c = c) :
    (run literal n c).map normalize = run literal n c := by
  induction n generalizing c with
  | zero => simp [run,hc]
  | succ n ih =>
    simp only [run]
    cases h : step literal c with
    | none => rfl
    | some d =>
      have hd := step_normalize c
      rw [h] at hd
      exact ih d (Option.some.inj hd)

theorem checkedBlankRun {n : Nat} {final : Packed}
    (h : packedRun n (0,0,0) = some final) :
    run literal n (zc 0 [] []) = some (unpack final) := by
  have replay := congrArg (Option.map unpack) (pack_run n (zc 0 [] []))
  change ((run literal n (zc 0 [] [])).map pack).map unpack =
    (packedRun n (0,0,0)).map unpack at replay
  rw [h, Option.map_map] at replay
  simpa only [Function.comp_def, unpack_pack, run_normalize n (zc 0 [] []) rfl, Option.map_some] using replay

end M192.Startup
