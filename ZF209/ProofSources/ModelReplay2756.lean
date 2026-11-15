module
public import ModelLiteralTraceCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 2726 traceStepeqd
theorem p2750 (a0 : (M → Prop)) (a1 : M) (a2 : M) (a3 : M)  : (t10 (M := M) (t84 (M := M) (t170 (M := M) (a0)) (t63 (M := M) (a1) (t63 (M := M) (a2) (a3)))) (t53 (M := M) (t2 (t51 (M := M) (a3)) (t16 (M := M) (t63 (M := M) (a1) (a2)) (a0))))) := by
  let e0  : M := (t63 (M := M) (a2) (a3))
  let e1  : M := (t63 (M := M) (a1) (e0))
  let e2 (u0 : M) : Prop := (t10 (M := M) u0 (e1))
  let e3 (u0 : M) : M := (t69 (M := M) u0)
  let e5 (u0 : M) : M := (t64 (M := M) u0)
  let e7 (u0 : M) : M := (t68 (M := M) u0)
  let e9 (u0 : M) : M := (t63 (M := M) (e5 u0) (e7 u0))
  let e10  : M := (t63 (M := M) (a1) (a2))
  let e11 (u0 : M) : Prop := (t51 (M := M) (e3 u0))
  let e12  : Prop := (t51 (M := M) (a3))
  let e13 (u0 : M) : Prop := (t16 (M := M) (e9 u0) (a0))
  let e14  : Prop := (t16 (M := M) (e10) (a0))
  let e15 (u0 : M) : Prop := (t2 (e11 u0) (e13 u0))
  let e16  : Prop := (t2 (e12) (e14))
  let e17  : M := (t53 (M := M) (e16))
  let e18 (u0 : M) : M := (t53 (M := M) (e15 u0))
  let e21  : Prop := (t10 (M := M) ((show M from (t84 (M := M) ((show (M → Prop) from (t170 (M := M) (a0)))) (e1)))) (e17))
  have v0 := p1305 (M := M) (a1) (a2) (a3)
  have v1 := fun z0 : M => p8 (e2 z0)
  have v2 := fun z0 : M => p1296 (M := M) (e2 z0) z0 (e1) (v1 z0)
  have v3 := fun z0 : M => p362 (M := M) (e2 z0) (e3 z0) ((show M from (t69 (M := M) (e1)))) (a3) (v0) (v2 z0)
  have v4 := fun z0 : M => p993 (M := M) (e2 z0) (e3 z0) (a3) (v3 z0)
  have v5 := p1277 (M := M) (a1) (e0)
  have v6 := fun z0 : M => p1266 (M := M) (e2 z0) z0 (e1) (v1 z0)
  have v7 := fun z0 : M => p362 (M := M) (e2 z0) (e5 z0) ((show M from (t64 (M := M) (e1)))) (a1) (v5) (v6 z0)
  have v8 := p1304 (M := M) (a1) (a2) (a3)
  have v9 := fun z0 : M => p1294 (M := M) (e2 z0) z0 (e1) (v1 z0)
  have v10 := fun z0 : M => p362 (M := M) (e2 z0) (e7 z0) ((show M from (t68 (M := M) (e1)))) (a2) (v8) (v9 z0)
  have v11 := fun z0 : M => p1243 (M := M) (e2 z0) (e5 z0) (a1) (e7 z0) (a2) (v7 z0) (v10 z0)
  have v12 := fun z0 : M => p574 (M := M) (e2 z0) (e9 z0) (e10) (a0) (v11 z0)
  have v13 := fun z0 : M => p196 (e2 z0) (e11 z0) (e12) (e13 z0) (e14) (v4 z0) (v12 z0)
  have v14 := fun z0 : M => p997 (M := M) (e2 z0) (e15 z0) (e16) (v13 z0)
  have v15 := p1494 (M := M) (e1) (e17) (fun w2 : M => (e18 w2)) ((fun w2 : M => v14 w2))
  have v16 : (e21) := (show (e21) from v15)
  exact v16
-- Actual MMB 2751 traceCheck_nil
theorem p2751 (env : Nat → M) (a0 : (M → Prop)) (c0 : ZF209.MM0ModelPeano.FormulaCertificate env 1 (fun v=>a0 (v 0)))  : (t10 (M := M) (t171 (M := M) (a0) (t28 (M := M))) (t30 (M := M))) := by
  let e0  : M := (t30 (M := M))
  let e4  : Prop := (t10 (M := M) ((show M from (t171 (M := M) (a0) ((show M from (t28 (M := M))))))) (e0))
  have v0 := p2360 (M := M) env (e0) ((show (M → Prop) from (t170 (M := M) (a0)))) (literalTraceStep_certificate c0)
  have v1 : (e4) := (show (e4) from v0)
  exact v1
-- Actual MMB 2752 traceCheck_cons
theorem p2752 (env : Nat → M) (a0 : (M → Prop)) (a1 : M) (a2 : M) (c0 : ZF209.MM0ModelPeano.FormulaCertificate env 1 (fun v=>a0 (v 0)))  : (t10 (M := M) (t171 (M := M) (a0) (t131 (a1) (a2))) (t53 (M := M) (t2 (t172 (M := M) (a0) (a2)) (t16 (M := M) (t63 (M := M) (a1) (a2)) (a0))))) := by
  let e1  : M := (t171 (M := M) (a0) ((show M from (t131 (a1) (a2)))))
  let e2  : (M → Prop) := (t170 (M := M) (a0))
  let e3  : M := (t30 (M := M))
  let e4  : M := (t142 (e3) (e2) (a2))
  let e7  : M := (t84 (M := M) (e2) ((show M from (t63 (M := M) (a1) ((show M from (t63 (M := M) (a2) (e4))))))))
  let e12  : M := (t53 (M := M) ((show Prop from (t2 ((show Prop from (t172 (M := M) (a0) (a2)))) ((show Prop from (t16 (M := M) ((show M from (t63 (M := M) (a1) (a2)))) (a0))))))))
  let e13  : Prop := (t10 (M := M) (e1) (e7))
  let e14  : Prop := (t10 (M := M) (e7) (e12))
  have v0 := p342 (M := M) (e1) (e7) (e12)
  have v1 := p2361 (M := M) env (e3) (e2) (a1) (a2) (literalTraceStep_certificate c0)
  have v2 : (e13) := (show (e13) from v1)
  have v3 := ((v0) (v2))
  have v4 := p2750 (M := M) (a0) (a1) (a2) (e4)
  have v5 : (e14) := (show (e14) from v4)
  have v6 := ((v3) (v5))
  exact v6
-- Actual MMB 2753 traceValid_nil
theorem p2753 (env : Nat → M) (a0 : (M → Prop)) (c0 : ZF209.MM0ModelPeano.FormulaCertificate env 1 (fun v=>a0 (v 0)))  : (t172 (M := M) (a0) (t28 (M := M))) := by
  let e0  : M := (t28 (M := M))
  let e1  : M := (t171 (M := M) (a0) (e0))
  let e2  : M := (t30 (M := M))
  let e3  : Prop := (t10 (M := M) (e1) (e2))
  let e4  : Prop := (t172 (M := M) (a0) (e0))
  let e5  : Prop := (t51 (M := M) (e2))
  let e6  : Prop := (t3 (e4) (e5))
  let e7  : Prop := (t0 (e3) (e6))
  have v0 := p994 (M := M) (e1) (e2)
  have v1 : (e7) := (show (e7) from v0)
  have v2 := p2751 (M := M) env (a0) c0
  have v3 := b3 (e3) (e6) (v1) (v2)
  have v4 := p999 (M := M)
  have v5 := p118 (e5) (e4) (v3) (v4)
  exact v5
-- Actual MMB 2754 traceValid_cons
theorem p2754 (env : Nat → M) (a0 : (M → Prop)) (a1 : M) (a2 : M) (c0 : ZF209.MM0ModelPeano.FormulaCertificate env 1 (fun v=>a0 (v 0)))  : (t3 (t172 (M := M) (a0) (t131 (a1) (a2))) (t2 (t172 (M := M) (a0) (a2)) (t16 (M := M) (t63 (M := M) (a1) (a2)) (a0)))) := by
  let e0  : M := (t131 (a1) (a2))
  let e1  : Prop := (t172 (M := M) (a0) (e0))
  let e5  : Prop := (t2 ((show Prop from (t172 (M := M) (a0) (a2)))) ((show Prop from (t16 (M := M) ((show M from (t63 (M := M) (a1) (a2)))) (a0)))))
  let e6  : M := (t53 (M := M) (e5))
  let e7  : Prop := (t51 (M := M) (e6))
  let e8  : M := (t171 (M := M) (a0) (e0))
  let e11  : Prop := (t0 ((show Prop from (t10 (M := M) (e8) (e6)))) ((show Prop from (t3 (e1) (e7)))))
  have v0 := p149 (e1) (e7) (e5)
  have v1 := p994 (M := M) (e8) (e6)
  have v2 : (e11) := (show (e11) from v1)
  have v3 := p2752 (M := M) env (a0) (a1) (a2) c0
  have v4 := ((v2) (v3))
  have v5 := ((v0) (v4))
  have v6 := p1011 (M := M) (e5)
  have v7 := ((v5) (v6))
  exact v7
-- Actual MMB 2755 traceDerives_head
end ZF209.MM0ModelReplay
