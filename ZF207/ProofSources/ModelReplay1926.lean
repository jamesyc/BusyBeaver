module
public import ModelReplay1916
public import ModelLiteralRecnStepCertificate
public import ModelRestrictedGraphCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 1917 recneqd
theorem p1917 (a0 : Prop) (a1 : M) (a2 : M) (a3 : (M → Prop)) (a4 : (M → Prop)) (a5 : M) (a6 : M) (h0 : (t0 (a0) (t10 (M := M) (a1) (a2)))) (h1 : (t0 (a0) (t17 (M := M) (a3) (a4)))) (h2 : (t0 (a0) (t10 (M := M) (a5) (a6)))) : (t0 (a0) (t10 (M := M) (t112 (M := M) (a1) (a3) (a5)) (t112 (M := M) (a2) (a4) (a6)))) := by
  let e5  : Prop := (t0 (a0) ((show Prop from (t10 (M := M) ((show M from (t112 (M := M) (a1) (a3) (a5)))) ((show M from (t112 (M := M) (a2) (a4) (a6))))))))
  have v0 := p1906 (M := M) (a0) (a1) (a2) (a3) (a4) (a5) (a6) (h0) (h1) (h2)
  have v1 := p1268 (M := M) (a0) ((show M from (t111 (M := M) (a1) (a3) (a5)))) ((show M from (t111 (M := M) (a2) (a4) (a6)))) (v0)
  have v2 : (e5) := (show (e5) from v1)
  exact v2
-- Actual MMB 1918 recneq
theorem p1925 (a0 : (M → Prop)) (a1 : M)  : (t10 (M := M) (t112 (M := M) (a1) (a0) (t28 (M := M))) (a1)) := by
  let e0  : M := (t28 (M := M))
  let e1  : M := (t112 (M := M) (a1) (a0) (e0))
  let e2  : M := (t63 (M := M) (e0) (a1))
  let e3  : M := (t65 (M := M) (e2))
  let e4  : M := (t111 (M := M) (a1) (a0) (e0))
  let e5  : Prop := (t10 (M := M) (e4) (e2))
  let e7  : Prop := (t0 (e5) ((show Prop from (t10 (M := M) (e1) (e3)))))
  let e8 (u0 : M) : M := (t64 (M := M) u0)
  let e9 (u0 : M) : M := (t29 (M := M) (e8 u0))
  let e10 (u0 : M) : M := (t84 (M := M) (a0) u0)
  let e11 (u0 : M) : M := (t63 (M := M) (e9 u0) (e10 u0))
  have v0 := p342 (M := M) (e1) (e3) (a1)
  have v1 := p1269 (M := M) (e4) (e2)
  have v2 : (e7) := (show (e7) from v1)
  have v3 := p1904 (M := M) (e2) ((show (M → Prop) from (t82 (M := M) (fun x0_0 : M => (e11 x0_0)))))
  have v4 : (e5) := (show (e5) from v3)
  have v5 := ((v2) (v4))
  have v6 := ((v0) (v5))
  have v7 := p1278 (M := M) (e0) (a1)
  have v8 := ((v6) (v7))
  exact v8
-- Actual MMB 1926 recnS
theorem p1926 (e : Nat → M) (a0 : (M → Prop)) (a1 : M) (a2 : M) (predicate : ZF207.MM0ModelPeano.FormulaCertificate e 1 (fun v => a0 (v 0))) : (t10 (M := M) (t112 (M := M) (a2) (a0) (t29 (M := M) (a1))) (t84 (M := M) (a0) (t63 (M := M) (a1) (t112 (M := M) (a2) (a0) (a1))))) := by
  let e0  : M := (t29 (M := M) (a1))
  let e1  : M := (t112 (M := M) (a2) (a0) (e0))
  let e2  : M := (t111 (M := M) (a2) (a0) (a1))
  let e3  : M := (t64 (M := M) (e2))
  let e4  : M := (t29 (M := M) (e3))
  let e5  : M := (t84 (M := M) (a0) (e2))
  let e6  : M := (t63 (M := M) (e4) (e5))
  let e7  : M := (t65 (M := M) (e6))
  let e9  : M := (t63 (M := M) (a1) ((show M from (t112 (M := M) (a2) (a0) (a1)))))
  let e10  : M := (t84 (M := M) (a0) (e9))
  let e11  : M := (t111 (M := M) (a2) (a0) (e0))
  let e14  : Prop := (t0 ((show Prop from (t10 (M := M) (e11) (e6)))) ((show Prop from (t10 (M := M) (e1) (e7)))))
  let e21  : M := (t65 (M := M) (e2))
  let e22  : M := (t63 (M := M) (e3) (e21))
  let e28  : Prop := (t0 ((show Prop from (t10 (M := M) (e3) (a1)))) ((show Prop from (t10 (M := M) (e22) (e9)))))
  have v0 := p342 (M := M) (e1) (e7) (e10)
  have v1 := p1269 (M := M) (e11) (e6)
  have v2 : (e14) := (show (e14) from v1)
  have v3 := p1915 (M := M) e (a0) (a1) (a2) predicate
  have v4 := ((v2) (v3))
  have v5 := ((v0) (v4))
  have v6 := p342 (M := M) (e7) (e5) (e10)
  have v7 := p1278 (M := M) (e4) (e5)
  have v8 := ((v6) (v7))
  have v9 := p1480 (M := M) (a0) (e2) (e9)
  have v10 := p332 (M := M) (e2) (e22) (e9)
  have v11 := p1279 (M := M) (e2)
  have v12 := ((v10) (v11))
  have v13 := p1246 (M := M) (e3) (a1) (e21)
  have v14 : (e28) := (show (e28) from v13)
  have v15 := p1916 (M := M) e (a0) (a1) (a2) predicate
  have v16 := ((v14) (v15))
  have v17 := ((v12) (v16))
  have v18 := ((v9) (v17))
  have v19 := ((v8) (v18))
  have v20 := ((v5) (v19))
  exact v20

end ZF207.MM0ModelReplay
