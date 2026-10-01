import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Opposite

/-! The exact ordered B9 of msg0499/msg0500/msg0502. All nine typed nonempty-word instances, including both four-block crossing macros, are explicit. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day13.FordLord2

open SemigroupBasis

def law00 : Identity Nat := ⟨(Word.mk 0 [0]), (Word.mk 0 [0, 0])⟩
def law01 : Identity Nat := ⟨(Word.mk 0 [1, 0]), (Word.mk 0 [0, 1, 0])⟩
def law02 : Identity Nat := ⟨(Word.mk 0 [1, 0]), (Word.mk 0 [1, 0, 0])⟩
def law03 : Identity Nat := ⟨(Word.mk 0 [0, 1, 1]), (Word.mk 0 [1, 0, 1])⟩
def law04 : Identity Nat := ⟨(Word.mk 0 [0, 1, 1]), (Word.mk 1 [0, 0, 1])⟩
def law05 : Identity Nat := ⟨(Word.mk 0 [1, 2, 0]), (Word.mk 0 [2, 1, 0])⟩
def law06 : Identity Nat := ⟨(Word.mk 0 [0, 1, 1, 2]), (Word.mk 0 [1, 1, 0, 2])⟩
def law07 : Identity Nat := ⟨(Word.mk 0 [0, 1, 2, 3, 1]), (Word.mk 0 [2, 0, 1, 3, 1])⟩
def law08 : Identity Nat := ⟨(Word.mk 0 [0, 1, 3, 2, 1]), (Word.mk 0 [3, 0, 1, 2, 1])⟩

def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05, law06, law07, law08]
abbrev dualBasis : List (Identity Nat) := reversedBasis basis
abbrev displayedBasisSHA256 : String := "2d2c549a8d376055cd53dfbd120e0776e97c71ce77dd365106bb7e8476ea4acb"

theorem basis_length : basis.length = 9 := by decide

theorem rawLaw00 (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have primitive : Derives basis law00.lhs law00.rhs :=
    Derives.fromBasis (e := law00) (by decide)
  have mapped := primitive.subst (fun _ => u)
  simpa [law00, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw01 (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have primitive : Derives basis law01.lhs law01.rhs :=
    Derives.fromBasis (e := law01) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law01, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw02 (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have primitive : Derives basis law02.lhs law02.rhs :=
    Derives.fromBasis (e := law02) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law02, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw03 (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ v) (((u ++ v) ++ u) ++ v) := by
  have primitive : Derives basis law03.lhs law03.rhs :=
    Derives.fromBasis (e := law03) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law03, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw04 (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ v) (((v ++ u) ++ u) ++ v) := by
  have primitive : Derives basis law04.lhs law04.rhs :=
    Derives.fromBasis (e := law04) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law04, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw05 (u v w : Word Nat) :
    Derives basis (((u ++ v) ++ w) ++ u) (((u ++ w) ++ v) ++ u) := by
  have primitive : Derives basis law05.lhs law05.rhs :=
    Derives.fromBasis (e := law05) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law05, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw06 (u v w : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ v) ++ w) ((((u ++ v) ++ v) ++ u) ++ w) := by
  have primitive : Derives basis law06.lhs law06.rhs :=
    Derives.fromBasis (e := law06) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law06, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw07 (u v w s : Word Nat) :
    Derives basis (((((u ++ u) ++ v) ++ w) ++ s) ++ v) (((((u ++ w) ++ u) ++ v) ++ s) ++ v) := by
  have primitive : Derives basis law07.lhs law07.rhs :=
    Derives.fromBasis (e := law07) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | 3 => s | _ => Word.singleton 0)
  simpa [law07, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw08 (u v w s : Word Nat) :
    Derives basis (((((u ++ u) ++ v) ++ s) ++ w) ++ v) (((((u ++ s) ++ u) ++ v) ++ w) ++ v) := by
  have primitive : Derives basis law08.lhs law08.rhs :=
    Derives.fromBasis (e := law08) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | 3 => s | _ => Word.singleton 0)
  simpa [law08, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped


end SemigroupBasis.CoRoots.Order6Day13.FordLord2
