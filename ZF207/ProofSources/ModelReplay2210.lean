module
public import ModelReplay2150
public import ModelRestrictedGraphCertificate
public import ModelLiteralBitParameterCertificate
public import ModelNumericSetDefinitions
public import ModelLiteralSetCodeCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 2183 xabfini
theorem p2191 (a0 : M) (a1 : M)  : (t13 (M := M) (t131 (a0) (a1)) (t28 (M := M))) := by
  let e3  : Prop := (t13 (M := M) ((show M from (t131 (a0) (a1)))) ((show M from (t28 (M := M)))))
  have v0 := b734 (M := M) ((show M from (t63 (M := M) (a0) (a1))))
  have v1 : (e3) := (show (e3) from v0)
  exact v1
-- Actual MMB 2192 ltconsid1
theorem p2193 (a0 : M) (a1 : M)  : (t48 (M := M) (a1) (t131 (a0) (a1))) := by
  let e0  : M := (t63 (M := M) (a0) (a1))
  let e1  : Prop := (t47 (M := M) (a1) (e0))
  let e3  : Prop := (t48 (M := M) (a1) ((show M from (t131 (a0) (a1)))))
  let e4  : Prop := (t3 (e1) (e3))
  have v0 := p910 (M := M) (a1) (e0)
  have v1 : (e4) := (show (e4) from v0)
  have v2 := p1257 (M := M) (a0) (a1)
  have v3 := p117 (e1) (e3) (v1) (v2)
  exact v3
-- Actual MMB 2194 consfstsnd
theorem p2194 (a0 : M)  : (t0 (t13 (M := M) (a0) (t28 (M := M))) (t10 (M := M) (t131 (t64 (M := M) (t46 (M := M) (a0) (t30 (M := M)))) (t65 (M := M) (t46 (M := M) (a0) (t30 (M := M))))) (a0))) := by
  let e1  : M := (t46 (M := M) (a0) ((show M from (t30 (M := M)))))
  let e2  : M := (t64 (M := M) (e1))
  let e3  : M := (t65 (M := M) (e1))
  let e4  : M := (t63 (M := M) (e2) (e3))
  let e6  : M := (t131 (e2) (e3))
  let e7  : M := (t29 (M := M) (e1))
  let e9  : Prop := (t0 ((show Prop from (t10 (M := M) (e4) (e1)))) ((show Prop from (t10 (M := M) (e6) (e7)))))
  have v0 := p739 (M := M) (e4) (e1)
  have v1 : (e9) := (show (e9) from v0)
  have v2 := p1279 (M := M) (e1)
  have v3 := ((v1) (v2))
  have v4 := p880 (M := M) (a0)
  have v5 := p360 (M := M) ((show Prop from (t13 (M := M) (a0) ((show M from (t28 (M := M))))))) (e6) (e7) (a0) (v3) (v4)
  exact v5
-- Actual MMB 2195 excons
theorem p2199 (a0 : M) (a1 : M)  : (t10 (M := M) (t64 (M := M) (t46 (M := M) (t131 (a0) (a1)) (t30 (M := M)))) (a0)) := by
  let e2  : M := (t46 (M := M) ((show M from (t131 (a0) (a1)))) ((show M from (t30 (M := M)))))
  let e4  : M := (t63 (M := M) (a0) (a1))
  let e6  : Prop := (t10 (M := M) (e2) (e4))
  have v0 := p342 (M := M) ((show M from (t64 (M := M) (e2)))) ((show M from (t64 (M := M) (e4)))) (a0)
  have v1 := p1267 (M := M) (e2) (e4)
  have v2 := p849 (M := M) (e4)
  have v3 : (e6) := (show (e6) from v2)
  have v4 := ((v1) (v3))
  have v5 := ((v0) (v4))
  have v6 := p1277 (M := M) (a0) (a1)
  have v7 := ((v5) (v6))
  exact v7
-- Actual MMB 2200 conssnd
theorem p2200 (a0 : M) (a1 : M)  : (t10 (M := M) (t65 (M := M) (t46 (M := M) (t131 (a0) (a1)) (t30 (M := M)))) (a1)) := by
  let e2  : M := (t46 (M := M) ((show M from (t131 (a0) (a1)))) ((show M from (t30 (M := M)))))
  let e4  : M := (t63 (M := M) (a0) (a1))
  let e6  : Prop := (t10 (M := M) (e2) (e4))
  have v0 := p342 (M := M) ((show M from (t65 (M := M) (e2)))) ((show M from (t65 (M := M) (e4)))) (a1)
  have v1 := p1269 (M := M) (e2) (e4)
  have v2 := p849 (M := M) (e4)
  have v3 : (e6) := (show (e6) from v2)
  have v4 := ((v1) (v3))
  have v5 := ((v0) (v4))
  have v6 := p1278 (M := M) (a0) (a1)
  have v7 := ((v5) (v6))
  exact v7
-- Actual MMB 2201 lecons1

end ZF207.MM0ModelReplay
