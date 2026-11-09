module

public import PA215.Source.AXBindings.B022
public import PA215.Source.AXTypedPlan
public import PA215.Source.ExistingPrivateBound
import all PA215.Source.AXBindings.B022

@[expose] public section
namespace PA215.Source.AXModelBounds
theorem bound3565_u : UnpairPartial.Bound exactSites 3565 :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.bound3565_u"
theorem bound3565_q : AXPair.Bound exactSites 3545 :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.bound3565_q"
theorem bound3565_m : AXTimes4.Bound exactSites 3586 :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.bound3565_m"
theorem bound3592_p : AXPushParam.Bound exactSites 3567 :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.bound3592_p"
theorem row3611_i0 : resolveAt exactSites 3611 = some (Instruction.inc 1 (some 3612)) :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.row3611_i0"
theorem bound3612_u : UnpairPartial.Bound exactSites 3612 :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.bound3612_u"
theorem bound3612_q : AXPair.Bound exactSites 3592 :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.bound3612_q"
theorem bound3612_m : AXTimes4.Bound exactSites 3633 :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.bound3612_m"
theorem bound3639_u : UnpairPartial.Bound exactSites 3639 :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.bound3639_u"
theorem bound3639_q : AXPair.Bound exactSites 3619 :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.bound3639_q"
theorem bound3639_m : AXTimes4.Bound exactSites 3660 :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.bound3639_m"
theorem bound3666_u : UnpairPartial.Bound exactSites 3666 :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.bound3666_u"
theorem bound3666_q : AXPair.Bound exactSites 3646 :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.bound3666_q"
theorem bound3666_m : AXTimes4.Bound exactSites 3687 :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.bound3666_m"
theorem row3693_i0 : resolveAt exactSites 3693 = some (Instruction.inc 1 (some 3694)) :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.row3693_i0"
theorem row3694_i0 : resolveAt exactSites 3694 = some (Instruction.inc 1 (some 3695)) :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.row3694_i0"
theorem bound3695_u : UnpairPartial.Bound exactSites 3695 :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.bound3695_u"
theorem bound3695_q : AXPair.Bound exactSites 3675 :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.bound3695_q"
theorem bound3695_m : AXTimes4.Bound exactSites 3716 :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.bound3695_m"
theorem bound3722_p : AXPushParam.Bound exactSites 3697 :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.bound3722_p"
theorem row3741_i0 : resolveAt exactSites 3741 = some (Instruction.inc 1 (some 3742)) :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.row3741_i0"
theorem bound3742_u : UnpairPartial.Bound exactSites 3742 :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.bound3742_u"
theorem bound3742_q : AXPair.Bound exactSites 3722 :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.bound3742_q"
theorem bound3742_m : AXTimes4.Bound exactSites 3763 :=
  existingPrivateBound% "PA215.Source.AXBindings.B022" "PA215.Source.AXAll.bound3742_m"
theorem block3565 : AXTyped.Bound .cons 3565 3592 :=
  AXTyped.Bound.cons 3545 (by decide) bound3565_u bound3565_q bound3565_m
theorem block3592 : AXTyped.Bound .push 3592 3611 :=
  AXTyped.Bound.push 3567 (by decide) bound3592_p
theorem block3611 : AXTyped.Bound .incT 3611 3612 :=
  AXTyped.Bound.incT 3611 (by decide) row3611_i0
theorem block3612 : AXTyped.Bound .cons 3612 3639 :=
  AXTyped.Bound.cons 3592 (by decide) bound3612_u bound3612_q bound3612_m
theorem block3639 : AXTyped.Bound .cons 3639 3666 :=
  AXTyped.Bound.cons 3619 (by decide) bound3639_u bound3639_q bound3639_m
theorem block3666 : AXTyped.Bound .cons 3666 3693 :=
  AXTyped.Bound.cons 3646 (by decide) bound3666_u bound3666_q bound3666_m
theorem block3693 : AXTyped.Bound .incT 3693 3694 :=
  AXTyped.Bound.incT 3693 (by decide) row3693_i0
theorem block3694 : AXTyped.Bound .incT 3694 3695 :=
  AXTyped.Bound.incT 3694 (by decide) row3694_i0
theorem block3695 : AXTyped.Bound .cons 3695 3722 :=
  AXTyped.Bound.cons 3675 (by decide) bound3695_u bound3695_q bound3695_m
theorem block3722 : AXTyped.Bound .push 3722 3741 :=
  AXTyped.Bound.push 3697 (by decide) bound3722_p
theorem block3741 : AXTyped.Bound .incT 3741 3742 :=
  AXTyped.Bound.incT 3741 (by decide) row3741_i0
theorem block3742 : AXTyped.Bound .cons 3742 3769 :=
  AXTyped.Bound.cons 3722 (by decide) bound3742_u bound3742_q bound3742_m
end PA215.Source.AXModelBounds
