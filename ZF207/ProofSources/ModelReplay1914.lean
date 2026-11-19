module
public import ModelReplay1905
public import ModelRestrictedGraphCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 1906 recnauxeqd
theorem p1906 (a0 : Prop) (a1 : M) (a2 : M) (a3 : (M → Prop)) (a4 : (M → Prop)) (a5 : M) (a6 : M) (h0 : (t0 (a0) (t10 (M := M) (a1) (a2)))) (h1 : (t0 (a0) (t17 (M := M) (a3) (a4)))) (h2 : (t0 (a0) (t10 (M := M) (a5) (a6)))) : (t0 (a0) (t10 (M := M) (t111 (M := M) (a1) (a3) (a5)) (t111 (M := M) (a2) (a4) (a6)))) := by
  let e0  : M := (t28 (M := M))
  let e1 (u0 : M) : M := (t64 (M := M) u0)
  let e2 (u0 : M) : M := (t29 (M := M) (e1 u0))
  let e3 (u0 : M) : M := (t84 (M := M) (a3) u0)
  let e4 (u0 : M) : M := (t84 (M := M) (a4) u0)
  let e5 (u0 : M) : M := (t63 (M := M) (e2 u0) (e3 u0))
  let e6 (u0 : M) : M := (t63 (M := M) (e2 u0) (e4 u0))
  let e14  : Prop := (t0 (a0) ((show Prop from (t10 (M := M) ((show M from (t111 (M := M) (a1) (a3) (a5)))) ((show M from (t111 (M := M) (a2) (a4) (a6))))))))
  have v0 := p1247 (M := M) (a0) (e0) (a1) (a2) (h0)
  have v1 := fun z0 : M => p1477 (M := M) (a0) (a3) (a4) z0 (h1)
  have v2 := fun z0 : M => p1247 (M := M) (a0) (e2 z0) (e3 z0) (e4 z0) (v1 z0)
  have v3 := p1436 (M := M) (a0) (fun w1 : M => (e5 w1)) (fun w1 : M => (e6 w1)) ((fun w1 : M => v2 w1))
  have v4 := p1895 (M := M) (a0) ((show M from (t63 (M := M) (e0) (a1)))) ((show M from (t63 (M := M) (e0) (a2)))) ((show (M → Prop) from (t82 (M := M) (fun x0_0 : M => (e5 x0_0))))) ((show (M → Prop) from (t82 (M := M) (fun x0_0 : M => (e6 x0_0))))) (a5) (a6) (v0) (v3) (h2)
  have v5 : (e14) := (show (e14) from v4)
  exact v5
-- Actual MMB 1907 recnauxeq
theorem p1912 (a0 : Prop) (a1 : M) (a2 : (M → Prop)) (a3 : M) (a4 : M) (h0 : (t0 (a0) (t10 (M := M) (a3) (a4)))) : (t0 (a0) (t10 (M := M) (t111 (M := M) (a1) (a2) (a3)) (t111 (M := M) (a1) (a2) (a4)))) := by
  have v0 := p354 (M := M) (a0) (a1)
  have v1 := p562 (M := M) (a0) (a2)
  have v2 := p1906 (M := M) (a0) (a1) (a1) (a2) (a2) (a3) (a4) (v0) (v1) (h0)
  exact v2
-- Actual MMB 1913 recnauxeq3
theorem p1914 (a0 : (M → Prop)) (a1 : M)  : (t10 (M := M) (t111 (M := M) (a1) (a0) (t28 (M := M))) (t63 (M := M) (t28 (M := M)) (a1))) := by
  let e0  : M := (t28 (M := M))
  let e1  : M := (t63 (M := M) (e0) (a1))
  let e2 (u0 : M) : M := (t64 (M := M) u0)
  let e3 (u0 : M) : M := (t29 (M := M) (e2 u0))
  let e4 (u0 : M) : M := (t84 (M := M) (a0) u0)
  let e5 (u0 : M) : M := (t63 (M := M) (e3 u0) (e4 u0))
  let e8  : Prop := (t10 (M := M) ((show M from (t111 (M := M) (a1) (a0) (e0)))) (e1))
  have v0 := p1904 (M := M) (e1) ((show (M → Prop) from (t82 (M := M) (fun x0_0 : M => (e5 x0_0)))))
  have v1 : (e8) := (show (e8) from v0)
  exact v1

end ZF207.MM0ModelReplay
