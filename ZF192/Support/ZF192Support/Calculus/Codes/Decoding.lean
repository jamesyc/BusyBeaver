module
public import ZF192Support.Calculus.Codes.Encoding
@[expose] public section
namespace CCodeSoundness

def decodeNat (n : Nat) : Formula :=
  if h : n=0 then .truth else
    let p := unpair (n/4)
    if n%4=0 then .imp (decodeNat p.1) (decodeNat p.2)
    else if n%4=1 then .mem p.1 p.2
    else if n%4=2 then .all p.2 (decodeNat p.1)
    else .eq p.1 p.2
termination_by n
decreasing_by
  all_goals
    have hq : n/4 < n := Nat.div_lt_self (by omega) (by omega)
    have ha := unpair_left_le (n/4)
    have hb := unpair_right_le (n/4)
    omega

theorem decodeNat_code (n : Nat) : (decodeNat n).code = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      rw [decodeNat]
      split
      · rename_i hz
        simp only [Formula.code]
        omega
      · rename_i hn
        have hq : n/4 < n := Nat.div_lt_self (by omega) (by omega)
        have ha : (unpair (n/4)).1 < n := Nat.lt_of_le_of_lt (unpair_left_le _) hq
        have hb : (unpair (n/4)).2 < n := Nat.lt_of_le_of_lt (unpair_right_le _) hq
        have he := Nat.mod_add_div n 4
        have ht := Nat.mod_lt n (by decide : 0<4)
        dsimp only
        split
        · rename_i h0
          simp only [Formula.code, ih _ ha, ih _ hb, unpair_spec]
          omega
        · rename_i h0
          split
          · rename_i h1
            simp only [Formula.code, unpair_spec]
            omega
          · rename_i h1
            split
            · rename_i h2
              simp only [Formula.code, ih _ ha, unpair_spec]
              omega
            · rename_i h2
              simp only [Formula.code, unpair_spec]
              omega

end CCodeSoundness
