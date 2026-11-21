module
public import I0451.ArithmeticReach
public import I0451.Decoder

/-! The verified decoder paths apply uniformly to a model-valued
register file. The instruction address and its local path are finite. -/

@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelExit (leaf : Decoder.Exit) (left right : V) : V :=
  match leaf with
  | .issue q => modelConfig q left right
  | .erase q => modelFromLeft q (modelDiv left 2) (modelPush false right)
  | .fused => modelFromLeft continueOne (modelDiv (modelDiv left 2) 2)
      (modelPush false (modelPush false right))

theorem model_decoder_path {q : Nat} {leaf : Decoder.Exit} {a b : Bool} {word : List Bool}
    (path : Decoder.Path q a b word leaf) (l r : V) :
    ModelReaches literal
      (modelConfig q (modelPush a (modelPush b l)) (modelPack word r))
      (modelExit leaf (modelPack word.reverse (modelPush a (modelPush b l))) r) := by
  induction path generalizing l r with
  | issue q a b read t ticks short moves valid =>
    exact ModelReaches.window moves l r
  | erase q a b t ticks short moves valid =>
    simpa only [modelExit, modelPack_cons, modelPack_nil, List.reverse_singleton,
      modelDiv_push, modelFromLeft_push, modelWindow, Window.seed, List.foldr_cons, List.foldr_nil] using
      ModelReaches.window moves l r
  | fused q b ticks short moves =>
    simpa only [modelExit, modelPack_cons, modelPack_nil, List.reverse_singleton,
      modelDiv_push, modelFromLeft_push, modelWindow, Window.seed, List.foldr_cons, List.foldr_nil] using
      ModelReaches.window moves l r
  | @next q a b read t ticks rest exit short moves inner ih =>
    have before :
        ModelReaches literal
          (modelConfig q (modelPush a (modelPush b l)) (modelPack (read :: rest) r))
          (modelConfig t (modelPush read (modelPush a (modelPush b l))) (modelPack rest r)) :=
      ModelReaches.window moves l (modelPack rest r)
    simpa only [List.reverse_cons, modelPack_append, modelPack_cons, modelPack_nil] using
      before.trans (ih (modelPush b l) r)

theorem model_decoder_root {leaf : Decoder.Exit} {word : List Bool}
    (path : Decoder.Path root true false word leaf) (r : V) :
    ModelReaches literal (modelConfig root 1 (modelPack word r))
      (modelExit leaf (modelPack word.reverse 1) r) := by
  have marker : modelPush true (modelPush false (0 : V)) = 1 := by simp [modelPush]
  simpa only [marker] using model_decoder_path path (0 : V) r

theorem terminal_halt_label (l r : V) :
    Terminal literal (modelConfig 451 l r) := by
  obtain ⟨read, _, digit⟩ := modelDigit_has_literal_read literal 451 r
  have closed (b : Bool) : row literal 451 b = 0 := by cases b <;> decide +kernel
  simp only [Terminal, modelConfig, pi₁_pair, pi₂_pair]
  simpa only [closed, Nat.cast_zero, Nat.cast_ofNat] using digit

end I0451.Arithmetization
