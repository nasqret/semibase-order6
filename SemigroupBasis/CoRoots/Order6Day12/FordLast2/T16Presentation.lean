import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Opposite

/-! The exact ordered B9 of msg0491/msg0492 and all nine typed nonempty-word instances. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day12.FordLast2

open SemigroupBasis

def law00 : Identity Nat := ⟨(Word.mk 0 [0]), (Word.mk 0 [0, 0])⟩
def law01 : Identity Nat := ⟨(Word.mk 0 [1, 0]), (Word.mk 0 [0, 1, 0])⟩
def law02 : Identity Nat := ⟨(Word.mk 0 [1, 0]), (Word.mk 0 [1, 0, 0])⟩
def law03 : Identity Nat := ⟨(Word.mk 0 [0, 1, 1]), (Word.mk 0 [1, 0, 1])⟩
def law04 : Identity Nat := ⟨(Word.mk 0 [0, 1, 1]), (Word.mk 1 [0, 0, 1])⟩
def law05 : Identity Nat := ⟨(Word.mk 0 [1, 2, 0]), (Word.mk 0 [1, 0, 2, 0])⟩
def law06 : Identity Nat := ⟨(Word.mk 0 [1, 2, 1]), (Word.mk 0 [2, 1, 1])⟩
def law07 : Identity Nat := ⟨(Word.mk 0 [0, 1, 1, 2]), (Word.mk 0 [1, 1, 0, 2])⟩
def law08 : Identity Nat := ⟨(Word.mk 0 [1, 0, 2, 2]), (Word.mk 2 [0, 1, 0, 2])⟩

def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05, law06, law07, law08]
abbrev dualBasis : List (Identity Nat) := reversedBasis basis
abbrev displayedBasisSHA256 : String := "18dd12cf39657be7b4d2e550a338772f10b7685c69aa0387bc1765db5373f5a5"

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
    Derives basis (((u ++ v) ++ w) ++ u) ((((u ++ v) ++ u) ++ w) ++ u) := by
  have primitive : Derives basis law05.lhs law05.rhs :=
    Derives.fromBasis (e := law05) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law05, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw06 (u v w : Word Nat) :
    Derives basis (((u ++ v) ++ w) ++ v) (((u ++ w) ++ v) ++ v) := by
  have primitive : Derives basis law06.lhs law06.rhs :=
    Derives.fromBasis (e := law06) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law06, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw07 (u v w : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ v) ++ w) ((((u ++ v) ++ v) ++ u) ++ w) := by
  have primitive : Derives basis law07.lhs law07.rhs :=
    Derives.fromBasis (e := law07) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law07, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw08 (u v w : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ w) ++ w) ((((w ++ u) ++ v) ++ u) ++ w) := by
  have primitive : Derives basis law08.lhs law08.rhs :=
    Derives.fromBasis (e := law08) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law08, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped


end SemigroupBasis.CoRoots.Order6Day12.FordLast2
