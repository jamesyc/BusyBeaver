module
public import ZF192Support.Execution.Registers.Commands.AX.PrefixPlan
public import ZF192Support.Execution.Registers.Commands.AX.Result
public import ZF192Support.Execution.Registers.Commands.Boundary
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeAXSymbolic
open ZF192Support.Internal (imp mem eqc all)
open ZFR.ArithmeticRepresentation ZF192Support.ModelCommands ZF192Support.NativeSource ZF192Support.NativeCommands
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma initial_spec (t a d h y x tail bottom:M) :
 materialize (valuation t a d h y x) tail bottom initial =
 ⟨t,a,d,h,modelCantor y (modelCantor x tail),bottom⟩ := by rfl
/-- The fixed AX prefix implements the symbolic operations over model-sized values. -/
theorem native_ax_prefix (n tail t w d h a x y:M) :
 nativeReaches (bodyEntry (.ax a x y) n tail ⟨t,w,d,h⟩)
 (NativeAX.config 4187 n ⟨axGate a (d+x) (h+y),a,d+x,h+y,tail,
 (heads a (d+x) (h+y) d h ++ [t]).foldr modelCantor w⟩) := by
 have hh:=prefix_realizes (M:=M) initial actualResult program_actual n (valuation t a d h y x) tail w
 rw [initial_spec,actual_spec] at hh
 exact hh
end ZF192Support.NativeAXSymbolic
