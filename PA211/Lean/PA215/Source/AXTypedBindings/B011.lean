import PA215.Source.AXBindings.B011
import PA215.Source.AXTypedPlan
import PA215.Source.ExistingPrivateBound
namespace PA215.Source.AXModelBounds
theorem bound1765_p : AXPushParam.Bound exactSites 1740 :=
  existingPrivateBound% "PA215.Source.AXBindings.B011" "PA215.Source.AXAll.bound1765_p"
theorem block1765 : AXTyped.Bound .push 1765 1784 :=
  AXTyped.Bound.push 1740 (by decide) bound1765_p
end PA215.Source.AXModelBounds
