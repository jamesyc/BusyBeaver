module
public import I0451.Logic.SetFormulaPrograms
public import I0451.Logic.AssignmentTuples
public import Mathlib.Data.Fin.Rev

/-! Connect the ordinary finite Lean parameter vectors to set-coded
tuples. Reversal matches a prepended de Bruijn binder with the coded
language's appended binder. -/
@[expose] public section
namespace I0451.Logic.SetFormulaPrograms

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.AssignmentCode I0451.Logic.SetAssignments I0451.Logic.ZFModel

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "E" => (fun (x y : V) => x ∈ y)

structure MatchesArguments {d : V} {n : Nat} (args : V) (v : Fin n → Domain E d) : Prop where
  tuple : Tuple d args (n : V)
  reads : ∀ i : Fin n, znth args (i.rev.val : V) = (v i).val

theorem matching_arguments_exist {d : V} {n : Nat} (v : Fin n → Domain E d) :
    ∃ args, MatchesArguments args v := by
  let contents (i : Fin n) := (v i.rev).val
  let args := vecToSeq contents
  have seq : Seq args := vecToSeq_seq contents
  have length : lh args = (n : V) := lh_vecToSeq contents
  have read (i : Fin n) : znth args (i.val : V) = (v i.rev).val :=
    seq.znth_eq_of_mem (mem_vectoSeq contents i)
  refine ⟨args, ⟨seq, length, ?_⟩, fun i => by simpa only [Fin.rev_rev] using read i.rev⟩
  intro x member
  obtain ⟨i, entry⟩ := mem_range_iff.mp member
  have pos : i ∈ (n : V) := length ▸ seq.lt_lh_of_mem entry
  obtain ⟨slot, rfl⟩ := mem_ofNat_iff.mp pos
  have eq := (seq.znth_eq_of_mem entry).symm.trans (read slot)
  exact eq.symm ▸ (v slot.rev).property

theorem MatchesArguments.append {d args : V} {n : Nat} {v : Fin n → Domain E d}
    (previous : MatchesArguments args v) (value : Domain E d) :
    MatchesArguments (args ⁀' value.val) (Fin.cases value v) := by
  have tuple := previous.tuple.append value.property
  have length : succ (n : V) = ((n + 1 : Nat) : V) := (num_succ_def n).symm
  rw [length] at tuple
  refine ⟨tuple, ?_⟩
  have sequence := previous.tuple.1
  have new := sequence.seqCons value.val
  intro i
  cases i using Fin.cases with
  | zero =>
    have eq : ((Fin.rev (0 : Fin (n + 1))).val : V) = lh args := by
      rw [Fin.rev_zero, Fin.val_last, previous.tuple.2.1]
    rw [eq]
    exact new.znth_eq_of_mem (Seq.mem_seqCons args value.val)
  | succ i =>
    have eq : ((Fin.rev i.succ).val : V) = (i.rev.val : V) := by rw [Fin.rev_succ]; rfl
    have earlier : (i.rev.val : V) ∈ lh args :=
      previous.tuple.2.1.symm ▸ ofNat_mem_of_lt i.rev.isLt
    rw [eq]
    exact (new.znth_eq_of_mem ((Seq.mem_seqCons_iff_of_lt earlier).mpr (sequence.znth earlier))).trans
      (previous.reads i)

theorem MatchesArguments.readsTuple {d j first second : V} {n : Nat}
    {f : Domain E d → Domain E d} (graph : Encodes E d j f) {v : Fin n → Domain E d}
    (args : MatchesArguments first v) (images : MatchesArguments second (f ∘ v)) :
    ReadsTuple j first second := by
  refine ⟨images.tuple.1, images.tuple.2.1.trans args.tuple.2.1.symm, ?_⟩
  intro i inside
  obtain ⟨slot, rfl⟩ := mem_ofNat_iff.mp (args.tuple.2.1 ▸ inside)
  have left : znth first (slot.val : V) = (v slot.rev).val := by
    simpa only [Fin.rev_rev] using args.reads slot.rev
  have right : znth second (slot.val : V) = (f (v slot.rev)).val := by
    simpa only [Fin.rev_rev, Function.comp_apply] using images.reads slot.rev
  rw [left, right]
  exact (graph.at_iff (v slot.rev) _).mpr rfl

end I0451.Logic.SetFormulaPrograms
