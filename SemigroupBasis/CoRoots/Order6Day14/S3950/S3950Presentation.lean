import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Opposite

/-! Exact ordered S6_3950 B3 from msg0491/msg0492/msg0509. Every primitive
has an arbitrary nonempty-word instance; no empty substitution is used. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day14.S3950

open SemigroupBasis

def law00 : Identity Nat := ⟨(Word.mk 0 [0]), (Word.mk 0 [0, 0])⟩
def law01 : Identity Nat := ⟨(Word.mk 0 [0, 1]), (Word.mk 0 [1, 0])⟩
def law02 : Identity Nat := ⟨(Word.mk 0 [1, 1, 2]), (Word.mk 0 [2, 1, 1])⟩

def basis : List (Identity Nat) := [law00, law01, law02]
abbrev dualBasis : List (Identity Nat) := reversedBasis basis
abbrev displayedBasisSHA256 : String := "42d038a0f2a11bde98614c71114cb9621bb3b59bae04372e047fb81479bccf17"

theorem basis_length : basis.length = 3 := by decide

theorem displayedBasis_exact :
    basis.map (fun identity => (identity.lhs.toList, identity.rhs.toList)) =
      [([0, 0], [0, 0, 0]), ([0, 0, 1], [0, 1, 0]),
       ([0, 1, 1, 2], [0, 2, 1, 1])] := by decide

theorem rawLaw00 (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have primitive : Derives basis law00.lhs law00.rhs :=
    Derives.fromBasis (e := law00) (by decide)
  have mapped := primitive.subst (fun _ => u)
  simpa [law00, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw01 (u v : Word Nat) :
    Derives basis ((u ++ u) ++ v) ((u ++ v) ++ u) := by
  have primitive : Derives basis law01.lhs law01.rhs :=
    Derives.fromBasis (e := law01) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law01, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw02 (u v w : Word Nat) :
    Derives basis (((u ++ v) ++ v) ++ w) (((u ++ w) ++ v) ++ v) := by
  have primitive : Derives basis law02.lhs law02.rhs :=
    Derives.fromBasis (e := law02) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law02, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

end SemigroupBasis.CoRoots.Order6Day14.S3950
