import PA215.NativeTable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-! Original contract4942, bound to data/contract4942.json by the input audit.
    Kernel acceptance below proves this one uniform symbolic contract, not the
    entire5134-obligation census or the final nonhalting theorem. -/
namespace PA215.Contract4942
open PA215.Zip PA215.Runtime PA215.NativeTable

def initial : SConf := (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 1, .run false 0 2, .run true 0 2, .run false 1 57, .run true 0 1, .box (.plain .none)])
def target : SConf := (84, false, [.run true 0 1], [.run true 0 1, .run false 0 1, .run true 0 2, .run false 1 60, .run true 0 1, .box (.plain .none)])

def result := exec machine none (fun s => sMatches s target) 500 initial false
/-- This closed computation is checked by Lean's kernel, not native_decide. -/
theorem accepted : result.isSome = true := by decide

/-- The original full-frame Break1 contract, for every padding and full file. -/
theorem uniform (n : Nat) (vs : List Nat) (hl : 10 ≤ vs.length) :
    Reach1 machine (conc n vs initial) (conc n vs target) := by
  have hv : Valid none vs := ⟨hl, trivial⟩
  have ha : (exec machine none (fun s => sMatches s target) 500 initial false).isSome = true :=
    accepted
  cases he : exec machine none (fun s => sMatches s target) 500 initial false with
  | none => simp [he] at ha
  | some last =>
      have h := exec_sound native_boxes n hv 500 initial false last he
      have hm := sMatches_conc n vs h.1
      simpa only [hm] using h.2.2 rfl
end PA215.Contract4942
