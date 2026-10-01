import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Opposite

/-! The exact ordered S6_1193 B4 of msg0491/msg0492. Each displayed law has
an explicit arbitrary nonempty-word instance. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day13.S1193

open SemigroupBasis

def law00 : Identity Nat := ⟨(Word.mk 0 [0]), (Word.mk 0 [0, 0])⟩
def law01 : Identity Nat := ⟨(Word.mk 0 [0, 1]), (Word.mk 0 [1, 0])⟩
def law02 : Identity Nat := ⟨(Word.mk 0 [0, 1, 1]), (Word.mk 1 [0, 0, 1])⟩
def law03 : Identity Nat := ⟨(Word.mk 0 [1, 1, 2]), (Word.mk 0 [2, 1, 1])⟩

def basis : List (Identity Nat) := [law00, law01, law02, law03]
abbrev dualBasis : List (Identity Nat) := reversedBasis basis
abbrev displayedBasisSHA256 : String := "cf03ee4fe61ed020262aed32daa2bb4076aca068d9f6027f072b2117cc4313ae"

theorem basis_length : basis.length = 4 := by decide

theorem displayedBasis_exact :
    basis.map (fun identity => (identity.lhs.toList, identity.rhs.toList)) =
      [([0, 0], [0, 0, 0]), ([0, 0, 1], [0, 1, 0]),
       ([0, 0, 1, 1], [1, 0, 0, 1]), ([0, 1, 1, 2], [0, 2, 1, 1])] := by decide

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

theorem rawLaw02 (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ v) (((v ++ u) ++ u) ++ v) := by
  have primitive : Derives basis law02.lhs law02.rhs :=
    Derives.fromBasis (e := law02) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law02, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw03 (u v w : Word Nat) :
    Derives basis (((u ++ v) ++ v) ++ w) (((u ++ w) ++ v) ++ v) := by
  have primitive : Derives basis law03.lhs law03.rhs :=
    Derives.fromBasis (e := law03) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law03, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

end SemigroupBasis.CoRoots.Order6Day13.S1193
