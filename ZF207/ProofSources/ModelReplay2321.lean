module
public import ModelReplay2315
public import ModelRestrictedGraphCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 2316 sreceqd
theorem p2316 (a0 : Prop) (a1 : (M → Prop)) (a2 : (M → Prop)) (a3 : M) (a4 : M) (h0 : (t0 (a0) (t17 (M := M) (a1) (a2)))) (h1 : (t0 (a0) (t10 (M := M) (a3) (a4)))) : (t0 (a0) (t10 (M := M) (t138 (a1) (a3)) (t138 (a2) (a4)))) := by
  let e0  : M := (t29 (M := M) (a3))
  let e1  : M := (t29 (M := M) (a4))
  let e2  : M := (t137 (a1) (e0))
  let e3  : M := (t137 (a2) (e1))
  let e9  : Prop := (t0 (a0) ((show Prop from (t10 (M := M) ((show M from (t138 (a1) (a3)))) ((show M from (t138 (a2) (a4))))))))
  have v0 := p740 (M := M) (a0) (a3) (a4) (h1)
  have v1 := p2306 (M := M) (a0) (a1) (a2) (e0) (e1) (h0) (v0)
  have v2 := p2015 (M := M) (a0) (e2) (e3) (v1)
  have v3 := p1475 (M := M) (a0) ((show (M → Prop) from (t120 (e2)))) ((show (M → Prop) from (t120 (e3)))) (a3) (a4) (v2) (h1)
  have v4 : (e9) := (show (e9) from v3)
  exact v4
-- Actual MMB 2317 sreceq
end ZF207.MM0ModelReplay
