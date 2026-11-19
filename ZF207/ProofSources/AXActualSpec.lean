module
public import AXSymbolicResult
@[expose] public section
namespace C207Search.AXSymbolic
open C207Soundness

def valuation (t a d h y x : Nat) : Fin 6 → Nat := fun i => [t,a,d,h,y,x][i.val]!

theorem actual_spec (t a d h y x tail : Nat) :
 materialize (valuation t a d h y x) tail actualResult =
 ⟨pointedGateCode a (d+x) (h+y),a,d+x,h+y,tail,
   [head1Code a (d+x) (h+y),head2Code a (d+x) (h+y),
    head3Code a (d+x) (h+y),head4Code a (d+x) (h+y),
    head5Code a (d+x) (h+y),head6Code a (d+x) (h+y),
    rho8Code a (d+x) (h+y) d,allCode d h,t]⟩ := by rfl

theorem macro_actual (t a d h y x tail : Nat) :
 AXMacro.run AXMacro.program ⟨t,a,d,h,M6.Source.Cantor.pair y (M6.Source.Cantor.pair x tail),[]⟩ =
 some ⟨pointedGateCode a (d+x) (h+y),a,d+x,h+y,tail,
   [head1Code a (d+x) (h+y),head2Code a (d+x) (h+y),
    head3Code a (d+x) (h+y),head4Code a (d+x) (h+y),
    head5Code a (d+x) (h+y),head6Code a (d+x) (h+y),
    rho8Code a (d+x) (h+y) d,allCode d h,t]⟩ := by
 have hh := run_sound AXMacro.program initial actualResult program_actual (valuation t a d h y x) tail
 rw [actual_spec] at hh
 exact hh
end C207Search.AXSymbolic
