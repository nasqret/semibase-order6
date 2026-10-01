import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Opposite

/-! The exact approved B11 presentation. Unrestricted word instances start with decide membership. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordPeriodOne

open SemigroupBasis

def law00 : Identity Nat := ⟨(Word.mk 0 [0]), (Word.mk 0 [0, 0])⟩
def law01 : Identity Nat := ⟨(Word.mk 0 [1, 0]), (Word.mk 0 [0, 1, 0])⟩
def law02 : Identity Nat := ⟨(Word.mk 0 [1, 0]), (Word.mk 0 [1, 0, 0])⟩
def law03 : Identity Nat := ⟨(Word.mk 0 [0, 1, 1]), (Word.mk 0 [1, 0, 1])⟩
def law04 : Identity Nat := ⟨(Word.mk 0 [0, 1, 1]), (Word.mk 0 [1, 1, 0])⟩
def law05 : Identity Nat := ⟨(Word.mk 0 [1, 2, 0]), (Word.mk 0 [1, 0, 2, 0])⟩
def law06 : Identity Nat := ⟨(Word.mk 0 [1, 1, 2, 2]), (Word.mk 0 [2, 1, 1, 2])⟩
def law07 : Identity Nat := ⟨(Word.mk 0 [1, 2, 0, 1]), (Word.mk 0 [1, 2, 1, 0])⟩
def law08 : Identity Nat := ⟨(Word.mk 0 [1, 0, 2, 3, 2]), (Word.mk 0 [1, 2, 0, 3, 2])⟩
def law09 : Identity Nat := ⟨(Word.mk 2 [1, 0, 2, 3, 0]), (Word.mk 2 [1, 2, 0, 3, 0])⟩
def law10 : Identity Nat := ⟨(Word.mk 0 [1, 2, 3, 1, 2]), (Word.mk 0 [2, 1, 3, 1, 2])⟩

def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09, law10]
abbrev displayedBasisSHA256 : String := "59cacb87f165c55eb4fb6563d410ed5973533c19c68884ce36b7049499138d54"

theorem basis_length : basis.length = 11 := by decide

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
    Derives basis (((u ++ u) ++ v) ++ v) (((u ++ v) ++ v) ++ u) := by
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
    Derives basis ((((u ++ v) ++ v) ++ w) ++ w) ((((u ++ w) ++ v) ++ v) ++ w) := by
  have primitive : Derives basis law06.lhs law06.rhs :=
    Derives.fromBasis (e := law06) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law06, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw07 (u v w : Word Nat) :
    Derives basis ((((u ++ v) ++ w) ++ u) ++ v) ((((u ++ v) ++ w) ++ v) ++ u) := by
  have primitive : Derives basis law07.lhs law07.rhs :=
    Derives.fromBasis (e := law07) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law07, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw08 (u v w s : Word Nat) :
    Derives basis (((((u ++ v) ++ u) ++ w) ++ s) ++ w) (((((u ++ v) ++ w) ++ u) ++ s) ++ w) := by
  have primitive : Derives basis law08.lhs law08.rhs :=
    Derives.fromBasis (e := law08) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | 3 => s | _ => Word.singleton 0)
  simpa [law08, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw09 (u v w s : Word Nat) :
    Derives basis (((((w ++ v) ++ u) ++ w) ++ s) ++ u) (((((w ++ v) ++ w) ++ u) ++ s) ++ u) := by
  have primitive : Derives basis law09.lhs law09.rhs :=
    Derives.fromBasis (e := law09) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | 3 => s | _ => Word.singleton 0)
  simpa [law09, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw10 (u v w s : Word Nat) :
    Derives basis (((((u ++ v) ++ w) ++ s) ++ v) ++ w) (((((u ++ w) ++ v) ++ s) ++ v) ++ w) := by
  have primitive : Derives basis law10.lhs law10.rhs :=
    Derives.fromBasis (e := law10) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | 3 => s | _ => Word.singleton 0)
  simpa [law10, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped


end SemigroupBasis.CoRoots.Order6Day11.FordLordPeriodOne
