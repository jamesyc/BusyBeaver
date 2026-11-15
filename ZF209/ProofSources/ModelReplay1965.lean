module
public import ModelReplay1926
public import ModelRestrictedGraphCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 1927 ocaseeqd
theorem p1959 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (a4 : M) (h0 : (t0 (a0) (t10 (M := M) (a1) (a2)))) (h1 : (t0 (a0) (t10 (M := M) (a3) (a4)))) : (t0 (a0) (t10 (M := M) (t117 (M := M) (a1) (a3)) (t117 (M := M) (a2) (a4)))) := by
  let e0  : M := (t30 (M := M))
  let e1 (u0 : M) : M := (t45 (M := M) (a1) u0)
  let e2 (u0 : M) : M := (t45 (M := M) (a2) u0)
  let e8  : Prop := (t0 (a0) ((show Prop from (t10 (M := M) ((show M from (t117 (M := M) (a1) (a3)))) ((show M from (t117 (M := M) (a2) (a4))))))))
  have v0 := p354 (M := M) (a0) (e0)
  have v1 := fun z0 : M => p802 (M := M) (a0) (a1) (a2) z0 (h0)
  have v2 := p1436 (M := M) (a0) (fun w1 : M => (e1 w1)) (fun w1 : M => (e2 w1)) ((fun w1 : M => v1 w1))
  have v3 := p1895 (M := M) (a0) (e0) (e0) ((show (M → Prop) from (t82 (M := M) (fun x0_0 : M => (e1 x0_0))))) ((show (M → Prop) from (t82 (M := M) (fun x0_0 : M => (e2 x0_0))))) (a3) (a4) (v0) (v2) (h1)
  have v4 : (e8) := (show (e8) from v3)
  exact v4
-- Actual MMB 1960 poweq
theorem p1963 (a0 : Prop) (a1 : M) (a2 : M) (a3 : M) (h0 : (t0 (a0) (t10 (M := M) (a2) (a3)))) : (t0 (a0) (t10 (M := M) (t117 (M := M) (a1) (a2)) (t117 (M := M) (a1) (a3)))) := by
  have v0 := p354 (M := M) (a0) (a1)
  have v1 := p1959 (M := M) (a0) (a1) (a1) (a2) (a3) (v0) (h0)
  exact v1
-- Actual MMB 1964 poweq2
theorem p1964 (a0 : M) (a1 : M) (a2 : M)  : (t0 (t10 (M := M) (a1) (a2)) (t10 (M := M) (t117 (M := M) (a0) (a1)) (t117 (M := M) (a0) (a2)))) := by
  let e0  : Prop := (t10 (M := M) (a1) (a2))
  have v0 := p8 (e0)
  have v1 := p1963 (M := M) (e0) (a0) (a1) (a2) (v0)
  exact v1
-- Actual MMB 1965 pow0
theorem p1965 (a0 : M)  : (t10 (M := M) (t117 (M := M) (a0) (t28 (M := M))) (t30 (M := M))) := by
  let e0  : M := (t30 (M := M))
  let e1 (u0 : M) : M := (t45 (M := M) (a0) u0)
  let e5  : Prop := (t10 (M := M) ((show M from (t117 (M := M) (a0) ((show M from (t28 (M := M))))))) (e0))
  have v0 := p1904 (M := M) (e0) ((show (M → Prop) from (t82 (M := M) (fun x0_0 : M => (e1 x0_0)))))
  have v1 : (e5) := (show (e5) from v0)
  exact v1

end ZF209.MM0ModelReplay
