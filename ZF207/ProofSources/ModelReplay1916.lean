module
public import ModelReplay1915
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
-- Actual MMB 1916 recnauxfst
theorem p1916 (e : Nat → M) (a0 : (M → Prop)) (a1 : M) (a2 : M) (predicate : ZF207.MM0ModelPeano.FormulaCertificate e 1 (fun v => a0 (v 0))) : (t10 (M := M) (t64 (M := M) (t111 (M := M) (a2) (a0) (a1))) (a1)) := by
  let e0 (u0 : M) : Prop := (t10 (M := M) u0 (a1))
  let e1 (u0 : M) : M := (t111 (M := M) (a2) (a0) u0)
  let e2  : M := (t111 (M := M) (a2) (a0) (a1))
  let e3 (u0 : M) : M := (t64 (M := M) (e1 u0))
  let e4  : M := (t64 (M := M) (e2))
  let e5  : M := (t28 (M := M))
  let e6 (u0 : M) : Prop := (t10 (M := M) u0 (e5))
  let e7  : M := (t111 (M := M) (a2) (a0) (e5))
  let e8  : M := (t64 (M := M) (e7))
  let e9 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 u1)
  let e10 (u0 : M) : M := (t111 (M := M) (a2) (a0) u0)
  let e11 (u0 : M) : M := (t64 (M := M) (e10 u0))
  let e12 (u0 : M) : M := (t29 (M := M) u0)
  let e13 (u0 : M) (u1 : M) : Prop := (t10 (M := M) u0 (e12 u1))
  let e14 (u0 : M) : M := (t111 (M := M) (a2) (a0) (e12 u0))
  let e15 (u0 : M) : M := (t64 (M := M) (e14 u0))
  let e16  : M := (t63 (M := M) (e5) (a2))
  let e23 (u0 : M) : M := (t29 (M := M) (e11 u0))
  let e24 (u0 : M) : M := (t84 (M := M) (a0) (e10 u0))
  let e25 (u0 : M) : M := (t63 (M := M) (e23 u0) (e24 u0))
  let e26 (u0 : M) : M := (t64 (M := M) (e25 u0))
  let e27 (u0 : M) : Prop := (t10 (M := M) (e14 u0) (e25 u0))
  let e28 (u0 : M) : Prop := (t10 (M := M) (e15 u0) (e26 u0))
  let e29 (u0 : M) : Prop := (t10 (M := M) (e26 u0) (e23 u0))
  let e30 (u0 : M) : Prop := (t10 (M := M) (e15 u0) (e23 u0))
  let e31 (u0 : M) : Prop := (t0 (e29 u0) (e30 u0))
  let e32 (u0 : M) : Prop := (t10 (M := M) (e11 u0) u0)
  let e33 (u0 : M) : Prop := (t10 (M := M) (e3 u0) u0)
  let e35 (u0 : M) : Prop := (t10 (M := M) (e15 u0) (e12 u0))
  let init : M := t63 (M := M) (t28 (M := M)) a2
  let ee : Nat → M := fun i => Nat.casesOn i init e
  let recGraph : ZF207.MM0ModelPeano.FunctionGraphCertificate ee 1 (fun v => t111 (M := M) a2 a0 (v 0)) :=
    literalRecursion_certificate (literalRecnStep_certificate (predicate.prependParameter init))
  let idGraph : ZF207.MM0ModelPeano.FunctionGraphCertificate ee 1 (fun v => v 0) := {
    formula := “y x. y=x”
    correct := by intro v y; rfl
  }
  let stepCertificate : ZF207.MM0ModelPeano.FormulaCertificate ee 1 (fun v => e33 (v 0)) :=
    ((literalFst_certificate ee).compose (G := fun x => t111 (M := M) a2 a0 x) recGraph).equal idGraph
  have v0 := fun z0 : M => p8 (e0 z0)
  have v1 := fun z0 : M => p1912 (M := M) (e0 z0) (a2) (a0) z0 (a1) (v0 z0)
  have v2 := fun z0 : M => p1266 (M := M) (e0 z0) (e1 z0) (e2) (v1 z0)
  have v3 := fun z0 : M => p350 (M := M) (e0 z0) (e3 z0) (e4) z0 (a1) (v2 z0) (v0 z0)
  have v4 := fun z0 : M => p8 (e6 z0)
  have v5 := fun z0 : M => p1912 (M := M) (e6 z0) (a2) (a0) z0 (e5) (v4 z0)
  have v6 := fun z0 : M => p1266 (M := M) (e6 z0) (e1 z0) (e7) (v5 z0)
  have v7 := fun z0 : M => p350 (M := M) (e6 z0) (e3 z0) (e8) z0 (e5) (v6 z0) (v4 z0)
  have v8 := fun z0 : M => fun z1 : M => p8 (e9 z0 z1)
  have v9 := fun z0 : M => fun z1 : M => p1912 (M := M) (e9 z0 z1) (a2) (a0) z0 z1 (v8 z0 z1)
  have v10 := fun z0 : M => fun z1 : M => p1266 (M := M) (e9 z0 z1) (e1 z0) (e10 z1) (v9 z0 z1)
  have v11 := fun z0 : M => fun z1 : M => p350 (M := M) (e9 z0 z1) (e3 z0) (e11 z1) z0 z1 (v10 z0 z1) (v8 z0 z1)
  have v12 := fun z0 : M => fun z1 : M => p8 (e13 z0 z1)
  have v13 := fun z0 : M => fun z1 : M => p1912 (M := M) (e13 z0 z1) (a2) (a0) z0 (e12 z1) (v12 z0 z1)
  have v14 := fun z0 : M => fun z1 : M => p1266 (M := M) (e13 z0 z1) (e1 z0) (e14 z1) (v13 z0 z1)
  have v15 := fun z0 : M => fun z1 : M => p350 (M := M) (e13 z0 z1) (e3 z0) (e15 z1) z0 (e12 z1) (v14 z0 z1) (v12 z0 z1)
  have v16 := p342 (M := M) (e8) ((show M from (t64 (M := M) (e16)))) (e5)
  have v17 := p1267 (M := M) (e7) (e16)
  have v18 := p1914 (M := M) (a0) (a2)
  have v19 := ((v17) (v18))
  have v20 := ((v16) (v19))
  have v21 := p1277 (M := M) (e5) (a2)
  have v22 := ((v20) (v21))
  have v23 := fun z0 : M => p342 (M := M) (e15 z0) (e26 z0) (e23 z0)
  have v24 := fun z0 : M => p1267 (M := M) (e14 z0) (e25 z0)
  have v25 := fun z0 : M => p1915 (M := M) e (a0) z0 (a2) predicate
  have v26 := fun z0 : M => ((v24 z0) (v25 z0))
  have v27 := fun z0 : M => ((v23 z0) (v26 z0))
  have v28 := fun z0 : M => p1277 (M := M) (e23 z0) (e24 z0)
  have v29 := fun z0 : M => ((v27 z0) (v28 z0))
  have v30 := fun z0 : M => p739 (M := M) (e11 z0) z0
  have v31 := fun z0 : M => p360 (M := M) (e32 z0) (e15 z0) (e23 z0) (e12 z0) (v29 z0) (v30 z0)
  have v32 := p741 (M := M) ee (fun w1 : M => (a1)) (fun w0 : M => (e33 w0)) (fun w1 : M => ((show Prop from (t10 (M := M) (e8) (e5))))) (fun w1 : M => ((show Prop from (t10 (M := M) (e4) (a1))))) (fun w1 : M => (e32 w1)) (fun w1 : M => (e35 w1)) stepCertificate ((fun w0 : M => (fun w1 : M => v3 w0))) ((fun w0 : M => (fun w1 : M => v7 w0))) ((fun w0 : M => (fun w1 : M => v11 w0 w1))) ((fun w0 : M => (fun w1 : M => v15 w0 w1))) ((fun w1 : M => v22)) ((fun w1 : M => v31 w1)) 0
  exact v32

end ZF207.MM0ModelReplay
