module
public import ModelReplay2359
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 2360 lrec0
theorem p2360 (e : Nat → M) (a0 : M) (a1 : (M → Prop)) (predicate : ZF207.MM0ModelPeano.FormulaCertificate e 1 (fun v => a1 (v 0))) : (t10 (M := M) (t142 (a0) (a1) (t28 (M := M))) (a0)) := by
  let e0  : M := (t28 (M := M))
  let e2  : Prop := (t10 (M := M) (e0) (e0))
  let e4  : M := (t46 (M := M) (e0) ((show M from (t30 (M := M)))))
  let e6  : M := (t65 (M := M) (e4))
  let e10  : M := (t84 (M := M) (a1) ((show M from (t63 (M := M) ((show M from (t64 (M := M) (e4)))) ((show M from (t63 (M := M) (e6) ((show M from (t142 (a0) (a1) (e6)))))))))))
  have v0 := p342 (M := M) ((show M from (t142 (a0) (a1) (e0)))) ((show M from (t50 (M := M) (e2) (a0) (e10)))) (a0)
  have v1 := p2359 (M := M) e (a1) (e0) (a0) predicate
  have v2 := ((v0) (v1))
  have v3 := p986 (M := M) (e2) (a0) (e10)
  have v4 := p340 (M := M) (e0)
  have v5 := ((v3) (v4))
  have v6 := ((v2) (v5))
  exact v6
-- Actual MMB 2361 lrecS
theorem p2361 (e : Nat → M) (a0 : M) (a1 : (M → Prop)) (a2 : M) (a3 : M) (predicate : ZF207.MM0ModelPeano.FormulaCertificate e 1 (fun v => a1 (v 0))) : (t10 (M := M) (t142 (a0) (a1) (t131 (a2) (a3))) (t84 (M := M) (a1) (t63 (M := M) (a2) (t63 (M := M) (a3) (t142 (a0) (a1) (a3)))))) := by
  let e0  : M := (t131 (a2) (a3))
  let e3  : Prop := (t10 (M := M) (e0) ((show M from (t28 (M := M)))))
  let e5  : M := (t46 (M := M) (e0) ((show M from (t30 (M := M)))))
  let e6  : M := (t64 (M := M) (e5))
  let e7  : M := (t65 (M := M) (e5))
  let e8  : M := (t142 (a0) (a1) (e7))
  let e9  : M := (t63 (M := M) (e7) (e8))
  let e10  : M := (t63 (M := M) (e6) (e9))
  let e11  : M := (t84 (M := M) (a1) (e10))
  let e12  : M := (t50 (M := M) (e3) (a0) (e11))
  let e13  : M := (t142 (a0) (a1) (a3))
  let e14  : M := (t63 (M := M) (a3) (e13))
  let e15  : M := (t63 (M := M) (a2) (e14))
  let e16  : M := (t84 (M := M) (a1) (e15))
  let e21  : Prop := (t1 (e3))
  have v0 := p342 (M := M) ((show M from (t142 (a0) (a1) (e0)))) (e12) (e16)
  have v1 := p2359 (M := M) e (a1) (e0) (a0) predicate
  have v2 := ((v0) (v1))
  have v3 := p342 (M := M) (e12) (e11) (e16)
  have v4 := p987 (M := M) (e3) (a0) (e11)
  have v5 := p2191 (M := M) (a2) (a3)
  have v6 : (e21) := (show (e21) from v5)
  have v7 := ((v4) (v6))
  have v8 := ((v3) (v7))
  have v9 := p1480 (M := M) (a1) (e10) (e15)
  have v10 := p1244 (M := M) (e6) (a2) (e9) (e14)
  have v11 := p2199 (M := M) (a2) (a3)
  have v12 := ((v10) (v11))
  have v13 := p1244 (M := M) (e7) (a3) (e8) (e13)
  have v14 := p2200 (M := M) (a2) (a3)
  have v15 := ((v13) (v14))
  have v16 := p2358 (M := M) (a0) (a1) (e7) (a3)
  have v17 := ((v16) (v14))
  have v18 := ((v15) (v17))
  have v19 := ((v12) (v18))
  have v20 := ((v9) (v19))
  have v21 := ((v8) (v20))
  have v22 := ((v2) (v21))
  exact v22

end ZF207.MM0ModelReplay
