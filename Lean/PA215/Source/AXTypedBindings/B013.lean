module

public import PA215.Source.AXBindings.B013
public import PA215.Source.AXTypedPlan
public import PA215.Source.ExistingPrivateBound
import all PA215.Source.AXBindings.B013

@[expose] public section
namespace PA215.Source.AXModelBounds
theorem bound2087_p : AXPushParam.Bound exactSites 2062 :=
  existingPrivateBound% "PA215.Source.AXBindings.B013" "PA215.Source.AXAll.bound2087_p"
theorem bound2106_c : CopyToT.Bound exactSites 5 2106 :=
  existingPrivateBound% "PA215.Source.AXBindings.B013" "PA215.Source.AXAll.bound2106_c"
theorem bound2113_p : AXPushParam.Bound exactSites 2088 :=
  existingPrivateBound% "PA215.Source.AXBindings.B013" "PA215.Source.AXAll.bound2113_p"
theorem bound2132_c : CopyToT.Bound exactSites 3 2132 :=
  existingPrivateBound% "PA215.Source.AXBindings.B013" "PA215.Source.AXAll.bound2132_c"
theorem bound2139_u : UnpairPartial.Bound exactSites 2139 :=
  existingPrivateBound% "PA215.Source.AXBindings.B013" "PA215.Source.AXAll.bound2139_u"
theorem bound2139_q : AXPair.Bound exactSites 2119 :=
  existingPrivateBound% "PA215.Source.AXBindings.B013" "PA215.Source.AXAll.bound2139_q"
theorem bound2139_m : AXTimes4.Bound exactSites 2160 :=
  existingPrivateBound% "PA215.Source.AXBindings.B013" "PA215.Source.AXAll.bound2139_m"
theorem bound2166_u : UnpairPartial.Bound exactSites 2166 :=
  existingPrivateBound% "PA215.Source.AXBindings.B013" "PA215.Source.AXAll.bound2166_u"
theorem bound2166_q : AXPair.Bound exactSites 2146 :=
  existingPrivateBound% "PA215.Source.AXBindings.B013" "PA215.Source.AXAll.bound2166_q"
theorem bound2166_m : AXTimes4.Bound exactSites 2187 :=
  existingPrivateBound% "PA215.Source.AXBindings.B013" "PA215.Source.AXAll.bound2166_m"
theorem row2193_i0 : resolveAt exactSites 2193 = some (Instruction.inc 1 (some 2194)) :=
  existingPrivateBound% "PA215.Source.AXBindings.B013" "PA215.Source.AXAll.row2193_i0"
theorem row2194_i0 : resolveAt exactSites 2194 = some (Instruction.inc 1 (some 2195)) :=
  existingPrivateBound% "PA215.Source.AXBindings.B013" "PA215.Source.AXAll.row2194_i0"
theorem bound2195_p : AXPushParam.Bound exactSites 2170 :=
  existingPrivateBound% "PA215.Source.AXBindings.B013" "PA215.Source.AXAll.bound2195_p"
theorem bound2214_c : CopyToT.Bound exactSites 4 2214 :=
  existingPrivateBound% "PA215.Source.AXBindings.B013" "PA215.Source.AXAll.bound2214_c"
theorem bound2221_p : AXPushParam.Bound exactSites 2196 :=
  existingPrivateBound% "PA215.Source.AXBindings.B013" "PA215.Source.AXAll.bound2221_p"
theorem bound2240_c : CopyToT.Bound exactSites 5 2240 :=
  existingPrivateBound% "PA215.Source.AXBindings.B013" "PA215.Source.AXAll.bound2240_c"
theorem block2087 : AXTyped.Bound .push 2087 2106 :=
  AXTyped.Bound.push 2062 (by decide) bound2087_p
theorem block2106 : AXTyped.Bound .copyH 2106 2113 :=
  AXTyped.Bound.copyH 2106 (by decide) bound2106_c
theorem block2113 : AXTyped.Bound .push 2113 2132 :=
  AXTyped.Bound.push 2088 (by decide) bound2113_p
theorem block2132 : AXTyped.Bound .copyA 2132 2139 :=
  AXTyped.Bound.copyA 2132 (by decide) bound2132_c
theorem block2139 : AXTyped.Bound .cons 2139 2166 :=
  AXTyped.Bound.cons 2119 (by decide) bound2139_u bound2139_q bound2139_m
theorem block2166 : AXTyped.Bound .cons 2166 2193 :=
  AXTyped.Bound.cons 2146 (by decide) bound2166_u bound2166_q bound2166_m
theorem block2193 : AXTyped.Bound .incT 2193 2194 :=
  AXTyped.Bound.incT 2193 (by decide) row2193_i0
theorem block2194 : AXTyped.Bound .incT 2194 2195 :=
  AXTyped.Bound.incT 2194 (by decide) row2194_i0
theorem block2195 : AXTyped.Bound .push 2195 2214 :=
  AXTyped.Bound.push 2170 (by decide) bound2195_p
theorem block2214 : AXTyped.Bound .copyD 2214 2221 :=
  AXTyped.Bound.copyD 2214 (by decide) bound2214_c
theorem block2221 : AXTyped.Bound .push 2221 2240 :=
  AXTyped.Bound.push 2196 (by decide) bound2221_p
theorem block2240 : AXTyped.Bound .copyH 2240 2247 :=
  AXTyped.Bound.copyH 2240 (by decide) bound2240_c
end PA215.Source.AXModelBounds
