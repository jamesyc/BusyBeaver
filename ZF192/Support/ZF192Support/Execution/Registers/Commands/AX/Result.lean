module
public import ZF192Support.Execution.Registers.Commands.AX.SymbolicEval
@[expose] public section
set_option maxRecDepth 3000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeAXSymbolic
open ZF192Support.Internal (imp mem eqc all codes)
open ZFR.ArithmeticRepresentation ZF192Support.ModelCommands
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
private lemma mem_code (x y : M) : mem x y = imp x y + 1 := rfl
private lemma eq_code (x y : M) : eqc x y = imp x y + 3 := rfl
private lemma all_code (x y : M) : all x y = imp y x + 2 := rfl

noncomputable def valuation (t a d h y x:M) : Fin 6→M := ![t,a,d,h,y,x]
lemma actual_spec (t a d h y x tail bottom:M) :
 materialize (valuation t a d h y x) tail bottom actualResult =
 ⟨axGate a (d+x) (h+y),a,d+x,h+y,tail,
 (heads a (d+x) (h+y) d h ++ [t]).foldr modelCantor bottom⟩ := by
 simp only [materialize,actualResult,listCode,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,
 eval,valuation,Matrix.cons_val_zero,heads,implicationHeads,List.cons_append,List.nil_append,
 symbolicCodes, CKernel.Generic.Codes.axHeads, CKernel.Generic.Codes.axImplicationHeads,
 axGate,mem_code,eq_code,all_code,
 codes, CKernel.Generic.Codes.head6, CKernel.Generic.Codes.head5, CKernel.Generic.Codes.head4,
 CKernel.Generic.Codes.head3, CKernel.Generic.Codes.head2, CKernel.Generic.Codes.head1,
 CKernel.Generic.Codes.rho8, CKernel.Generic.Codes.bundle, CKernel.Generic.Codes.gateBody,
 CKernel.Generic.Codes.qGate, CKernel.Generic.Codes.eqVac, CKernel.Generic.Codes.memVac,
 CKernel.Generic.Codes.ex, CKernel.Generic.Codes.neg]
 norm_num [Matrix.cons_val,add_assoc]
end ZF192Support.NativeAXSymbolic
