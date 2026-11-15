module
public import ModelReplay2321
public import ModelHistoryLookupCertificate
public import ModelRestrictedGraphCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 2322 srecauxapp
theorem p2322 (e : Nat → M) (a0 : (M → Prop)) (a1 : M) (a2 : M) (predicate : ZF209.MM0ModelPeano.FormulaCertificate e 1 (fun v => a0 (v 0))) : (t0 (t48 (M := M) (a1) (a2)) (t10 (M := M) (t84 (M := M) (t120 (t137 (a0) (a2))) (a1)) (t138 (a0) (a1)))) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a2))
  let e1 (u0 : M) : M := (t137 (a0) u0)
  let e2  : M := (t137 (a0) (a2))
  let e3 (u0 : M) : (M → Prop) := (t120 (e1 u0))
  let e4  : (M → Prop) := (t120 (e2))
  let e5 (u0 : M) : M := (t84 (M := M) (e3 u0) (a1))
  let e6  : M := (t84 (M := M) (e4) (a1))
  let e7  : M := (t138 (a0) (a1))
  let e8 (u0 : M) : Prop := (t48 (M := M) (a1) u0)
  let e9  : Prop := (t48 (M := M) (a1) (a2))
  let e10 (u0 : M) : Prop := (t10 (M := M) (e5 u0) (e7))
  let e11  : Prop := (t10 (M := M) (e6) (e7))
  let e12  : M := (t28 (M := M))
  let e13 (u0 : M) : Prop := (t10 (M := M) u0 (e12))
  let e14  : M := (t137 (a0) (e12))
  let e15  : (M → Prop) := (t120 (e14))
  let e16  : M := (t84 (M := M) (e15) (a1))
  let e17  : Prop := (t48 (M := M) (a1) (e12))
  let e18  : Prop := (t10 (M := M) (e16) (e7))
  let e19 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e20 (u0 : M) : M := (t137 (a0) u0)
  let e21 (u0 : M) : (M → Prop) := (t120 (e20 u0))
  let e22 (u0 : M) : M := (t84 (M := M) (e21 u0) (a1))
  let e23 (u0 : M) : Prop := (t48 (M := M) (a1) u0)
  let e24 (u0 : M) : Prop := (t10 (M := M) (e22 u0) (e7))
  let e25 (u0 : M) : M := (t29 (M := M) u0)
  let e26 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (e25 u1))
  let e27 (u0 : M) : M := (t137 (a0) (e25 u0))
  let e28 (u0 : M) : (M → Prop) := (t120 (e27 u0))
  let e29 (u0 : M) : M := (t84 (M := M) (e28 u0) (a1))
  let e30 (u0 : M) : Prop := (t48 (M := M) (a1) (e25 u0))
  let e31 (u0 : M) : Prop := (t10 (M := M) (e29 u0) (e7))
  let e33  : Prop := (t0 (e17) (e18))
  let e34 (u0 : M) : M := (t84 (M := M) (a0) (e20 u0))
  let e35 (u0 : M) : (M → Prop) := (t136 (e21 u0) u0 (e34 u0))
  let e36 (u0 : M) : Prop := (t17 (M := M) (e28 u0) (e35 u0))
  let e37 (u0 : M) : M := (t84 (M := M) (e35 u0) (a1))
  let e38 (u0 : M) : Prop := (t10 (M := M) (e29 u0) (e37 u0))
  let e39 (u0 : M) : Prop := (t13 (M := M) (a1) u0)
  let e40 (u0 : M) : Prop := (t10 (M := M) (e37 u0) (e22 u0))
  let e41 (u0 : M) : Prop := (t10 (M := M) (a1) u0)
  let e42  : M := (t29 (M := M) (a1))
  let e43  : M := (t137 (a0) (e42))
  let e44 (u0 : M) : Prop := (t0 (e41 u0) (e31 u0))
  let e45 (u0 : M) : Prop := (t0 (e23 u0) (e24 u0))
  let e46 (u0 : M) : Prop := (t47 (M := M) (a1) u0)
  let e47 (u0 : M) : Prop := (t4 (e23 u0) (e41 u0))
  let e48 (u0 : M) : Prop := (t0 (e8 u0) (e10 u0))
  let e49  : Prop := (t0 (e9) (e11))
  let e50 (u0 : M) : Prop := (t0 (e30 u0) (e31 u0))
  let ee : Nat → M := fun i => Nat.casesOn i a1 (fun i => Nat.casesOn i e7 e)
  let inductionCertificate : ZF209.MM0ModelPeano.FormulaCertificate ee 1 (fun v => e48 (v 0)) := {
    formula := (historyLookup_certificate ((predicate.prependParameter e7).prependParameter a1)).formula
    correct := by
      intro v
      simpa [e48,e8,e10,e5,e3,e1,ee,t0,t10,literalLt_order] using
        (historyLookup_certificate ((predicate.prependParameter e7).prependParameter a1)).correct v
  }
  have v0 := fun z0 : M => p8 (e0 z0)
  have v1 := fun z0 : M => p890 (M := M) (e0 z0) (a1) z0 (a2) (v0 z0)
  have v2 := fun z0 : M => p2310 (M := M) (e0 z0) (a0) z0 (a2) (v0 z0)
  have v3 := fun z0 : M => p2015 (M := M) (e0 z0) (e1 z0) (e2) (v2 z0)
  have v4 := fun z0 : M => p1477 (M := M) (e0 z0) (e3 z0) (e4) (a1) (v3 z0)
  have v5 := fun z0 : M => p348 (M := M) (e0 z0) (e5 z0) (e6) (e7) (v4 z0)
  have v6 := fun z0 : M => p188 (e0 z0) (e8 z0) (e9) (e10 z0) (e11) (v1 z0) (v5 z0)
  have v7 := fun z0 : M => p8 (e13 z0)
  have v8 := fun z0 : M => p890 (M := M) (e13 z0) (a1) z0 (e12) (v7 z0)
  have v9 := fun z0 : M => p2310 (M := M) (e13 z0) (a0) z0 (e12) (v7 z0)
  have v10 := fun z0 : M => p2015 (M := M) (e13 z0) (e1 z0) (e14) (v9 z0)
  have v11 := fun z0 : M => p1477 (M := M) (e13 z0) (e3 z0) (e15) (a1) (v10 z0)
  have v12 := fun z0 : M => p348 (M := M) (e13 z0) (e5 z0) (e16) (e7) (v11 z0)
  have v13 := fun z0 : M => p188 (e13 z0) (e8 z0) (e17) (e10 z0) (e18) (v8 z0) (v12 z0)
  have v14 := fun z0 : M => fun z1 : M => p8 (e19 z0 z1)
  have v15 := fun z0 : M => fun z1 : M => p890 (M := M) (e19 z0 z1) (a1) z0 z1 (v14 z0 z1)
  have v16 := fun z0 : M => fun z1 : M => p2310 (M := M) (e19 z0 z1) (a0) z0 z1 (v14 z0 z1)
  have v17 := fun z0 : M => fun z1 : M => p2015 (M := M) (e19 z0 z1) (e1 z0) (e20 z1) (v16 z0 z1)
  have v18 := fun z0 : M => fun z1 : M => p1477 (M := M) (e19 z0 z1) (e3 z0) (e21 z1) (a1) (v17 z0 z1)
  have v19 := fun z0 : M => fun z1 : M => p348 (M := M) (e19 z0 z1) (e5 z0) (e22 z1) (e7) (v18 z0 z1)
  have v20 := fun z0 : M => fun z1 : M => p188 (e19 z0 z1) (e8 z0) (e23 z1) (e10 z0) (e24 z1) (v15 z0 z1) (v19 z0 z1)
  have v21 := fun z0 : M => fun z1 : M => p8 (e26 z0 z1)
  have v22 := fun z0 : M => fun z1 : M => p890 (M := M) (e26 z0 z1) (a1) z0 (e25 z1) (v21 z0 z1)
  have v23 := fun z0 : M => fun z1 : M => p2310 (M := M) (e26 z0 z1) (a0) z0 (e25 z1) (v21 z0 z1)
  have v24 := fun z0 : M => fun z1 : M => p2015 (M := M) (e26 z0 z1) (e1 z0) (e27 z1) (v23 z0 z1)
  have v25 := fun z0 : M => fun z1 : M => p1477 (M := M) (e26 z0 z1) (e3 z0) (e28 z1) (a1) (v24 z0 z1)
  have v26 := fun z0 : M => fun z1 : M => p348 (M := M) (e26 z0 z1) (e5 z0) (e29 z1) (e7) (v25 z0 z1)
  have v27 := fun z0 : M => fun z1 : M => p188 (e26 z0 z1) (e8 z0) (e30 z1) (e10 z0) (e31 z1) (v22 z0 z1) (v26 z0 z1)
  have v28 := p22 (e17) (e18)
  have v29 := p904 (M := M) (a1)
  have v30 := ((v28) (v29))
  have v31 := fun z0 : M => p910 (M := M) (a1) z0
  have v32 := fun z0 : M => p926 (M := M) (a1) z0
  have v33 := fun z0 : M => p1478 (M := M) (e28 z0) (e35 z0) (a1)
  have v34 := fun z0 : M => p2313 (M := M) e (a0) z0 predicate
  have v35 := fun z0 : M => ((v33 z0) (v34 z0))
  have v36 := fun z0 : M => p2298 (M := M) (e21 z0) z0 (e34 z0) (a1)
  have v37 := fun z0 : M => p914 (M := M) (a1) z0
  have v38 := fun z0 : M => p10 (e23 z0) (e39 z0) (e40 z0) (v36 z0) (v37 z0)
  have v39 := fun z0 : M => p360 (M := M) (e23 z0) (e29 z0) (e37 z0) (e22 z0) (v35 z0) (v38 z0)
  have v40 := fun z0 : M => p348 (M := M) (e23 z0) (e29 z0) (e22 z0) (e7) (v39 z0)
  have v41 := fun z0 : M => p110 (e23 z0) (e31 z0) (e24 z0) (v40 z0)
  have v42 := fun z0 : M => p5 (e23 z0) (e24 z0) (e31 z0) (v41 z0)
  have v43 := fun z0 : M => p341 (M := M) (a1) z0
  have v44 := fun z0 : M => p740 (M := M) (e41 z0) z0 (a1) (v43 z0)
  have v45 := fun z0 : M => p2310 (M := M) (e41 z0) (a0) (e25 z0) (e42) (v44 z0)
  have v46 := fun z0 : M => p2022 (M := M) (e41 z0) (e27 z0) (e43) (a1) (v45 z0)
  have v47 : (∀ z0 : M, (e44 z0)) := (show (∀ z0 : M, (e44 z0)) from v46)
  have v48 := fun z0 : M => p4 (e45 z0) (e44 z0) (v47 z0)
  have v49 := fun z0 : M => p252 (e45 z0) (e23 z0) (e41 z0) (e31 z0) (v42 z0) (v48 z0)
  have v50 := fun z0 : M => p161 (e45 z0) (e46 z0) (e47 z0) (e31 z0) (v32 z0) (v49 z0)
  have v51 := fun z0 : M => p162 (e45 z0) (e30 z0) (e46 z0) (e31 z0) (v31 z0) (v50 z0)
  have v52 := p741 (M := M) ee (fun w1 : M => (a2)) (fun w0 : M => (e48 w0)) (fun w1 : M => (e33)) (fun w1 : M => (e49)) (fun w1 : M => (e45 w1)) (fun w1 : M => (e50 w1)) inductionCertificate ((fun w0 : M => (fun w1 : M => v6 w0))) ((fun w0 : M => (fun w1 : M => v13 w0))) ((fun w0 : M => (fun w1 : M => v20 w0 w1))) ((fun w0 : M => (fun w1 : M => v27 w0 w1))) ((fun w1 : M => v30)) ((fun w1 : M => v51 w1)) 0
  exact v52

end ZF209.MM0ModelReplay
