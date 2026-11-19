module
public import ModelNativeAXPlan
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeAXSymbolic
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
theorem op_0 : Realizes (M:=M) .push 50 69 := by
 apply push_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_1 : Realizes (M:=M) .copyH 69 76 := by
 apply copyH_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_2 : Realizes (M:=M) .push 76 95 := by
 apply push_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_3 : Realizes (M:=M) .copyD 95 102 := by
 apply copyD_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_4 : Realizes (M:=M) .cons 102 129 := by
 apply cons_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_5 : Realizes (M:=M) .incT 129 130 := by
 apply incT_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_6 : Realizes (M:=M) .incT 130 131 := by
 apply incT_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_7 : Realizes (M:=M) .readH 131 145 := by
 exact readH_realizes
theorem op_8 : Realizes (M:=M) .push 145 164 := by
 apply push_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_9 : Realizes (M:=M) .copyH 164 171 := by
 apply copyH_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_10 : Realizes (M:=M) .push 171 190 := by
 apply push_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_11 : Realizes (M:=M) .copyD 190 197 := by
 apply copyD_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_12 : Realizes (M:=M) .cons 197 224 := by
 apply cons_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_13 : Realizes (M:=M) .readD 224 238 := by
 exact readD_realizes
theorem op_14 : Realizes (M:=M) .push 238 257 := by
 apply push_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_15 : Realizes (M:=M) .copyD 257 264 := by
 apply copyD_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_16 : Realizes (M:=M) .cons 264 291 := by
 apply cons_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_17 : Realizes (M:=M) .push 291 310 := by
 apply push_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_18 : Realizes (M:=M) .copyD 310 317 := by
 apply copyD_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_19 : Realizes (M:=M) .push 317 336 := by
 apply push_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_20 : Realizes (M:=M) .copyH 336 343 := by
 apply copyH_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_21 : Realizes (M:=M) .cons 343 370 := by
 apply cons_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_22 : Realizes (M:=M) .push 370 389 := by
 apply push_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_23 : Realizes (M:=M) .copyA 389 396 := by
 apply copyA_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_24 : Realizes (M:=M) .push 396 415 := by
 apply push_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_25 : Realizes (M:=M) .copyH 415 422 := by
 apply copyH_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_26 : Realizes (M:=M) .cons 422 449 := by
 apply cons_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_27 : Realizes (M:=M) .cons 449 476 := by
 apply cons_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_28 : Realizes (M:=M) .cons 476 503 := by
 apply cons_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_29 : Realizes (M:=M) .push 503 522 := by
 apply push_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_30 : Realizes (M:=M) .copyH 522 529 := by
 apply copyH_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_31 : Realizes (M:=M) .push 529 548 := by
 apply push_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_32 : Realizes (M:=M) .copyD 548 555 := by
 apply copyD_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_33 : Realizes (M:=M) .cons 555 582 := by
 apply cons_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_34 : Realizes (M:=M) .incT 582 583 := by
 apply incT_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_35 : Realizes (M:=M) .incT 583 584 := by
 apply incT_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_36 : Realizes (M:=M) .push 584 603 := by
 apply push_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_37 : Realizes (M:=M) .incT 603 604 := by
 apply incT_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_38 : Realizes (M:=M) .cons 604 631 := by
 apply cons_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_39 : Realizes (M:=M) .push 631 650 := by
 apply push_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_40 : Realizes (M:=M) .copyD 650 657 := by
 apply copyD_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_41 : Realizes (M:=M) .cons 657 684 := by
 apply cons_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_42 : Realizes (M:=M) .incT 684 685 := by
 apply incT_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_43 : Realizes (M:=M) .incT 685 686 := by
 apply incT_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_44 : Realizes (M:=M) .push 686 705 := by
 apply push_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_45 : Realizes (M:=M) .incT 705 706 := by
 apply incT_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_46 : Realizes (M:=M) .cons 706 733 := by
 apply cons_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_47 : Realizes (M:=M) .push 733 752 := by
 apply push_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_48 : Realizes (M:=M) .copyH 752 759 := by
 apply copyH_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_49 : Realizes (M:=M) .cons 759 786 := by
 apply cons_realizes
 all_goals repeat' first | (solve | decide) | constructor
end ZF207.NativeAXSymbolic
