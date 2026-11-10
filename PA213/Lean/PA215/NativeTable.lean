import PA215.Machine
import PA215.Native

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PA215.NativeTable
open PA215.Zip PA215.Native PA215.Runtime

/-- Original sparse labels of the fixed dense machine, in dense state order. -/
def sparseLabels : List Nat := [74, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 75, 76, 77, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 118, 119, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 141, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 157, 158, 159, 160, 161, 162, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 176, 178, 179, 180, 182, 184, 185, 186, 187, 188, 189, 190, 193, 194, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 209, 210, 211, 213, 214, 215, 216, 217, 218, 220, 221, 222, 223, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 1000]

/-- Exchange the protected native engine label with its physical replacement. -/
def swap120302 (q : Nat) : Nat :=
  if q = 120 then 302 else if q = 302 then 120 else q

def label (q : WorkingState) : Nat := swap120302 (sparseLabels.getD q.val 254)
def labelControl : Control → Nat
  | none => 254
  | some q => label q

def inverse (q : Nat) : Option WorkingState :=
  workingStates.find? (fun d => label d == q)

/-- The actual dense table presented in the native proof's numeric labels. -/
def machine : TMN := fun q b =>
  (inverse q).map fun d =>
    let a := row d b
    (a.write, a.right, labelControl a.next)

theorem inverse_label : ∀ q : WorkingState, inverse (label q) = some q := by decide

theorem halt_not_working : ∀ q : WorkingState, label q ≠ 254 := by decide

theorem literal_row_correspondence : ∀ (q : WorkingState) (b : Bool),
    machine (label q) b = some ((row q b).write, (row q b).right, labelControl (row q b).next) := by
  intro q b
  simp [machine, inverse_label]

/-- All44 engine premises are equations of the exact dense215 table. -/
theorem engine_rows : AgreeRows machine Reference230.tm230 boxRows := by decide

theorem append_zero_tail : IncTail0 machine := by unfold IncTail0; decide

theorem native_boxes : BoxLemmas machine := boxLemmas engine_rows append_zero_tail

/-- Actual215 native increment, uniformly over full files and arbitrary left contexts.
    A spare zero is appended and the execution has strictly positive length. -/
theorem increment_positive (r : Nat) (l : List Bool) (vs : List Nat)
    (hr : r < 9) (hl : 10 ≤ vs.length) :
    Reach1 machine (zc 64 l (sepsM r vs))
      (zl 40 l (sepsR (incr r vs ++ [0]))) :=
  box_inc_positive engine_rows append_zero_tail r l vs hr hl

end PA215.NativeTable
