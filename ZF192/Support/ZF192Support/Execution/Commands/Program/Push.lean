module
public import ZF192Support.Execution.Commands.Semantics
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.ModelCommands
open ZF192Support.Internal (imp mem eqc all)
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma modelCommandsEval_append (xs ys:List (Command M)) (s:Store M) :
 modelCommandsEval (xs++ys) s=(modelCommandsEval xs s).bind (modelCommandsEval ys) := by
 induction xs generalizing s with
 | nil => rfl
 | cons c cs ih => simp only [List.cons_append,modelCommandsEval,Option.bind_assoc,ih]
private lemma multiple_add_ne_one {a b : M}
    (ha : ∃ q, a = 4 * q) (hb : ∃ q, b = 4 * q) : a + b ≠ 1 := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  rw [← mul_add]
  exact four_mul_ne_one _

/-- Each shift up to and including the selection tests only the old top and
the implication prefix. The following stack entry can be arbitrary. -/
private lemma shift_to_head (before : List M) (top current selected next bottom d : M)
    (rest : List M) (ht : ∃ q, top = 4 * q) (hc : ∃ q, current = 4 * q)
    (hs : ∃ q, selected = 4 * q) (hb : ∀ z ∈ before, ∃ q, z = 4 * q) :
    modelCommandsEval (List.replicate (before.length + 2) (.shift : Command M))
      ⟨top, (before ++ selected :: next :: rest).foldr modelCantor bottom, d, current⟩ =
    some ⟨selected, rest.foldr modelCantor bottom, d, next⟩ := by
  induction before generalizing top current with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.zero_add, List.replicate_succ,
      List.replicate_zero, List.foldr_cons, modelCommandsEval, modelCommandEval,
      modelUnpairLeft_pair, modelUnpairRight_pair, multiple_add_ne_one ht hc,
      multiple_add_ne_one hc hs, ite_false, Option.bind_some]
  | cons x xs ih =>
    have hx := hb x (List.mem_cons_self)
    have hxs : ∀ z ∈ xs, ∃ q, z = 4 * q := fun z hz => hb z (List.mem_cons_of_mem _ hz)
    have hlen : (x :: xs).length + 2 = (xs.length + 2) + 1 := by simp
    rw [hlen, List.replicate_succ]
    simp only [List.cons_append, List.foldr_cons, modelCommandsEval, modelCommandEval,
      modelUnpairLeft_pair, modelUnpairRight_pair, multiple_add_ne_one ht hc,
      ite_false, Option.bind_some]
    simpa only [List.foldr_cons] using ih current x hc hx hxs

private lemma gate_multiple (a d h : M) : ∃ q, gate a d h = 4 * q := by
  unfold gate
  split
  · exact ⟨_, modelImp_value _ _⟩
  · exact ⟨0, by simp⟩

private lemma implicationHeads_multiple (a d h u z : M)
    (hz : z ∈ implicationHeads a d h u) : ∃ q, z = 4 * q := by
  simp only [implicationHeads, CKernel.Generic.Codes.axImplicationHeads, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, modelImp_value _ _⟩

lemma modelAX_select (a x y t w d h : M) (before : List M) (selected next : M)
    (rest : List M)
    (splitHeads : heads a (d + x) (h + y) d h = before ++ selected :: next :: rest)
    (prefixMem : ∀ z ∈ before ++ [selected], z ∈ implicationHeads a (d + x) (h + y) d) :
    modelCommandsEval ([.ax a x y] ++ List.replicate (before.length + 2) .shift)
      ⟨t,w,d,h⟩ = some ⟨selected, (rest ++ [t]).foldr modelCantor w, 0, next⟩ := by
  rw [modelCommandsEval_append]
  change modelCommandsEval (List.replicate (before.length + 2) .shift)
    ⟨gate a (d + x) (h + y), (heads a (d + x) (h + y) d h ++ [t]).foldr modelCantor w, 0, 0⟩ = _
  rw [splitHeads, List.append_assoc]
  exact shift_to_head before _ 0 selected next w 0 (rest ++ [t]) (gate_multiple _ _ _)
    ⟨0, by simp⟩ (implicationHeads_multiple _ _ _ _ _ (prefixMem _ (List.mem_append_right _ (by simp))))
    (fun z hz => implicationHeads_multiple _ _ _ _ z (prefixMem _ (List.mem_append_left _ hz)))

lemma modelAX_shift8 (a x y t w d h : M) :
    modelCommandsEval ([.ax a x y] ++ List.replicate 8 .shift) ⟨t,w,d,h⟩ =
    some ⟨axRho8 a (d+x) (h+y) d,modelCantor t w,0,all d h⟩ := by
  let before := (implicationHeads a (d + x) (h + y) d).take 6
  exact modelAX_select a x y t w d h before _ _ [] rfl (by
    intro z hz
    have same : before ++ [axRho8 a (d + x) (h + y) d] =
        implicationHeads a (d + x) (h + y) d := rfl
    rwa [same] at hz)

/-- Fixed ten-command macro, symbolic arbitrary PA-model stores. Not yet coded arbitrary-length traces. -/
lemma modelPUSH_total (t w d h:M) :
 modelCommandsEval (([.ax 0 0 0]++List.replicate 8 .shift)++[.mp 0]) ⟨t,w,d,h⟩ =
 some ⟨0,modelCantor t w,0,0⟩ := by
 rw [modelCommandsEval_append,modelAX_shift8]
 have he:imp (axRho8 0 (d+0) (h+0) d) (0+0) ≠ all d h := by
  rw [modelImp_value,modelAll_value]
  exact four_mul_ne_four_add_two _ _
 simp only [add_zero] at he
 simp only [Option.bind_some,modelCommandsEval,modelCommandEval,he,ite_false,add_zero]
end ZF192Support.ModelCommands
