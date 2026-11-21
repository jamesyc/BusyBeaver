module
public import I3_380.Search.Arithmetic.ProgramFrames
public import I3_380.Search.Arithmetic.StoreCode
@[expose] public section

namespace PalomarI3380.Compiler

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ArithmeticMachine (packWord packWord_append repeatBit repeatBit_cast repeatBit_add)
open ArithmeticMachine.Reference (Frame Outcome execute executeDecoded frame)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The rightmost physical register represents logical register zero. -/
def Store.file {V : Type} (s : Store V) : List V := (List.ofFn s).reverse

@[simp] theorem Store.length_file {V : Type} (s : Store V) : s.file.length = 12 := by
  simp [Store.file,Register]

theorem file_storeOf {V : Type} [OfNat V 0] (file : List V) (length : 12 ≤ file.length) :
    (storeOf file).file = file.drop (file.length-12) := by
  apply List.ext_getElem
  · simp only [Store.length_file,List.length_drop]; omega
  · intro i h₁ h₂
    have small : i < 12 := by simpa only [Store.length_file] using h₁
    unfold Store.file at h₁ ⊢
    rw [List.getElem_reverse,List.getElem_ofFn,List.getElem_drop]
    simp only [storeOf,List.length_ofFn,Fin.val_mk]
    have index : file.length-(12-1-i+1) = file.length-12+i := by omega
    rw [index,List.getElem?_eq_getElem (by rw [List.length_drop] at h₂; omega),Option.getD_some]

theorem storeOf_file {V : Type} [OfNat V 0] (stem : List V) (s : Store V) :
    storeOf (stem ++ s.file) = s := by
  funext r
  have index : (stem ++ s.file).length-(r.val+1) = stem.length+(12-1-r.val) := by
    simp only [List.length_append,Store.length_file]
    have small := r.isLt
    omega
  rw [storeOf,index,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
  rw [List.getElem?_eq_getElem (by rw [Store.length_file]; have small := r.isLt; omega)]
  simp only [Option.getD_some,Store.file,List.getElem_reverse,List.getElem_ofFn,List.length_ofFn]
  congr 1
  apply Fin.ext
  change 12-1-(12-1-r.val) = r.val
  have small := r.isLt
  omega

theorem frame_file_unchanged {s t : Frame M} (outcome : execute s = .next t) :
    t.values.length = s.values.length ∧
    t.values.take (s.values.length-12) = s.values.take (s.values.length-12) := by
  unfold execute at outcome
  cases found : Engine.follow 59 Engine.Port.root [] (s.path ++ Engine.zeros (74-s.path.length)) with
  | none => simp [found] at outcome
  | some d =>
    cases command : d.command with
    | halt => simp [found,executeDecoded,command] at outcome
    | «break» skip =>
      simp only [found,executeDecoded,command,Outcome.next.injEq] at outcome
      subst t
      exact ⟨rfl,rfl⟩
    | «continue» skip =>
      cases skip <;>
        simp only [found,executeDecoded,command,Outcome.next.injEq] at outcome <;>
        subst t <;> exact ⟨rfl,rfl⟩
    | register dec r =>
      simp only [found,executeDecoded,command,Outcome.next.injEq] at outcome
      subst t
      exact ⟨List.length_set, List.take_set_of_le (Nat.sub_le_sub_left r.isLt s.values.length)⟩

theorem trimPC_zeros (path : List Bool) (n : Nat) : trimPC (path ++ Engine.zeros n) = trimPC path := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show Engine.zeros (n+1) = Engine.zeros n ++ [false] from List.replicate_succ' ..,
      ← List.append_assoc,trimPC_append_zero,ih]

theorem trimPC_clean {path : List Bool} (clean : Engine.Clean path) : Engine.Clean (trimPC path) := by
  obtain ⟨stem,n,rfl,valid⟩ := clean
  rw [trimPC_zeros]
  obtain ⟨k,padded⟩ := trimPC_padding stem
  have prefixValid : Engine.ValidPrefix Engine.Port.root (trimPC stem) :=
    Engine.ValidPrefix.initial _ _ _ (padded ▸ valid)
  exact ⟨trimPC stem,0,by simp,prefixValid⟩

/-- Trailing zero bits can be treated as tape padding. This gives each
logical path a canonical frame with the same encoded configuration. -/
theorem frame_trim (s : Frame M) :
    ∃ gap : M, s.code = frame (trimPC s.path) gap s.values ∧
      (s.path.length : M)+s.gap = ((trimPC s.path).length : M)+gap := by
  obtain ⟨n,padded⟩ := trimPC_padding s.path
  let stem := trimPC s.path
  have pathEq : s.path = stem ++ Engine.zeros n := padded
  refine ⟨s.gap+(n : M),?_,?_⟩
  · unfold Frame.code frame
    have run := congrArg (fun p => packWord p (repeatBit false s.gap
      (ArithmeticMachine.Reference.registers s.values 0))) pathEq
    rw [packWord_append, ← repeatBit_cast, ← repeatBit_add] at run
    exact congrArg (ArithmeticMachine.Reference.cell Engine.Port.root 1) run
  · have sizes := congrArg List.length pathEq
    rw [List.length_append,List.length_replicate] at sizes
    rw [sizes,Nat.cast_add]
    change (stem.length : M)+(n : M)+s.gap = (stem.length : M)+(s.gap+(n : M))
    ac_rfl

end PalomarI3380.Compiler
