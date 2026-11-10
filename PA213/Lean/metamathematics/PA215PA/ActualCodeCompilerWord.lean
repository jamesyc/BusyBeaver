import PA215PA.ActualCodeCompilerSound
import PA215.Source.CommandAtomEncoding
import PA215.Source.UniversalCommandWitness
namespace PA215.PA.NativeCalculus.ActualBasis.Code
open PA215.Source PA215.Source.Enumeration PA215.Source.Cantor
open PA215.Source.CommandAtomEncoding
attribute [local irreducible] word encodeWord encodeAtoms atoms compileCertificate commandsEval commandEval

def haltCertificate (code : Nat) : List Command :=
  [.ax 0 0 0] ++ compileCertificate code ++ [.shift]

def candidateCode (code : Nat) : Nat := encodeAtoms (atoms (haltCertificate code))-1

theorem candidateCode_word (code : Nat) : word (candidateCode code)=haltCertificate code := by
  unfold candidateCode haltCertificate
  exact candidate_atoms (.ax 0 0 0) (compileCertificate code ++ [.shift])

theorem haltCertificate_universal (code : Nat) (h : verify code=some 1) (s : CommandStore) :
    commandsEval (haltCertificate code) s=none := by
  obtain ⟨p,hp⟩ := compileCertificate_matches code 1 h
  unfold haltCertificate
  rw [←hp]
  exact haltWord_universal p s

theorem candidateCode_universal (code : Nat) (h : verify code=some 1) (s : CommandStore) :
    commandsEval (word (candidateCode code)) s=none := by
  rw [candidateCode_word]
  exact haltCertificate_universal code h s

#print axioms candidateCode_word
#print axioms candidateCode_universal
end PA215.PA.NativeCalculus.ActualBasis.Code
