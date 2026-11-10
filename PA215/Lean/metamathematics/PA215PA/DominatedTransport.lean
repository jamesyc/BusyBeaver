import PA215PA.DominatedRho8

/-! A concrete finite-proof compiler replaces every unrestricted rho8 leaf
with the checked dominated template. This is external syntactic correctness;
its natural-code primitive-recursive arithmetization in PA is still separate. -/
namespace PA215.PA.NativeCalculus

attribute [local irreducible] rho1 rho2 rho3 rho4 rho5 rho6 rho7 rho8 bundle

set_option maxHeartbeats 1000000 in
inductive UnrestrictedDerivation : Nat → Type where
  | truth : UnrestrictedDerivation 0
  | mp {a b} : UnrestrictedDerivation a → UnrestrictedDerivation (wim a b) → UnrestrictedDerivation b
  | all (a) {b} : UnrestrictedDerivation b → UnrestrictedDerivation (wal a b)
  | r1 (a b) : UnrestrictedDerivation (rho1 a b)
  | r2 (a b c) : UnrestrictedDerivation (rho2 a b c)
  | r3 (a b c) : UnrestrictedDerivation (rho3 a b c)
  | r4 (a b c) : UnrestrictedDerivation (rho4 a b c)
  | r5 (a b c) : UnrestrictedDerivation (rho5 a b c)
  | r6 (a b) : UnrestrictedDerivation (rho6 a b)
  | r7 (a b c) : UnrestrictedDerivation (rho7 a b c)
  | r8 (a b c u) : UnrestrictedDerivation (rho8 a b c u)
  | guardedBundle (a b c) : c ≠ a → c ≠ b → UnrestrictedDerivation (bundle a b c)

def UnrestrictedDerivation.toDominated {n : Nat} : UnrestrictedDerivation n → Derivation n
  | .truth => .truth
  | .mp p q => .mp p.toDominated q.toDominated
  | .all a p => .all a p.toDominated
  | .r1 a b => .r1 a b
  | .r2 a b c => .r2 a b c
  | .r3 a b c => .r3 a b c
  | .r4 a b c => .r4 a b c
  | .r5 a b c => .r5 a b c
  | .r6 a b => .r6 a b
  | .r7 a b c => .r7 a b c
  | .r8 a b c u => Dominated.rho8_all a b c u
  | .guardedBundle a b c ha hb => .guardedBundle a b c ha hb

def Derivation.toUnrestricted {n : Nat} : Derivation n → UnrestrictedDerivation n
  | .truth => .truth
  | .mp p q => .mp p.toUnrestricted q.toUnrestricted
  | .all a p => .all a p.toUnrestricted
  | .r1 a b => .r1 a b
  | .r2 a b c => .r2 a b c
  | .r3 a b c => .r3 a b c
  | .r4 a b c => .r4 a b c
  | .r5 a b c => .r5 a b c
  | .r6 a b => .r6 a b
  | .r7 a b c => .r7 a b c
  | .r8 a b c u _ => .r8 a b c u
  | .guardedBundle a b c ha hb => .guardedBundle a b c ha hb

theorem proved_iff_unrestricted (n : Nat) : Proved n ↔ Nonempty (UnrestrictedDerivation n) :=
  ⟨fun ⟨p⟩ => ⟨p.toUnrestricted⟩,fun ⟨p⟩ => ⟨p.toDominated⟩⟩

#print axioms UnrestrictedDerivation.toDominated
#print axioms proved_iff_unrestricted
end PA215.PA.NativeCalculus
