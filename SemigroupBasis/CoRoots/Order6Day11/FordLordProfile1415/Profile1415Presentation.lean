import SemigroupBasis.FiniteCertificate
import SemigroupBasis.CoRoots.S5_107ListDerives

/-! The exact approved B32 presentation. Every unrestricted displayed-law instance starts with decide membership. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415

open SemigroupBasis

def law00 : Identity Nat := ⟨(Word.mk 0 [0]), (Word.mk 0 [0, 0, 0])⟩
def law01 : Identity Nat := ⟨(Word.mk 0 [1, 0]), (Word.mk 0 [0, 0, 1, 0])⟩
def law02 : Identity Nat := ⟨(Word.mk 0 [1, 0]), (Word.mk 0 [0, 1, 0, 0])⟩
def law03 : Identity Nat := ⟨(Word.mk 0 [1, 0]), (Word.mk 0 [0, 1, 1, 1])⟩
def law04 : Identity Nat := ⟨(Word.mk 0 [1, 0]), (Word.mk 0 [1, 0, 0, 0])⟩
def law05 : Identity Nat := ⟨(Word.mk 0 [1, 0]), (Word.mk 0 [1, 0, 1, 1])⟩
def law06 : Identity Nat := ⟨(Word.mk 0 [1, 0]), (Word.mk 0 [1, 1, 0, 1])⟩
def law07 : Identity Nat := ⟨(Word.mk 0 [1, 0]), (Word.mk 0 [1, 1, 1, 0])⟩
def law08 : Identity Nat := ⟨(Word.mk 0 [0, 0, 1, 1]), (Word.mk 0 [0, 1, 0, 1])⟩
def law09 : Identity Nat := ⟨(Word.mk 0 [0, 0, 1, 1]), (Word.mk 0 [0, 1, 1, 0])⟩
def law10 : Identity Nat := ⟨(Word.mk 0 [0, 0, 1, 1]), (Word.mk 0 [1, 0, 0, 1])⟩
def law11 : Identity Nat := ⟨(Word.mk 0 [0, 0, 1, 1]), (Word.mk 0 [1, 0, 1, 0])⟩
def law12 : Identity Nat := ⟨(Word.mk 0 [0, 0, 1, 1]), (Word.mk 0 [1, 1, 0, 0])⟩
def law13 : Identity Nat := ⟨(Word.mk 0 [0, 1, 0, 2]), (Word.mk 0 [1, 0, 0, 2])⟩
def law14 : Identity Nat := ⟨(Word.mk 0 [0, 1, 1, 2]), (Word.mk 0 [1, 0, 1, 2])⟩
def law15 : Identity Nat := ⟨(Word.mk 0 [0, 1, 1, 2]), (Word.mk 0 [1, 1, 0, 2])⟩
def law16 : Identity Nat := ⟨(Word.mk 0 [0, 1, 2, 0]), (Word.mk 0 [1, 0, 2, 0])⟩
def law17 : Identity Nat := ⟨(Word.mk 0 [0, 1, 2, 0]), (Word.mk 0 [1, 2, 0, 0])⟩
def law18 : Identity Nat := ⟨(Word.mk 0 [0, 1, 2, 1]), (Word.mk 0 [1, 0, 2, 1])⟩
def law19 : Identity Nat := ⟨(Word.mk 0 [0, 1, 2, 1]), (Word.mk 0 [1, 1, 2, 0])⟩
def law20 : Identity Nat := ⟨(Word.mk 0 [0, 1, 2, 1]), (Word.mk 0 [1, 2, 0, 1])⟩
def law21 : Identity Nat := ⟨(Word.mk 0 [0, 1, 2, 1]), (Word.mk 0 [1, 2, 1, 0])⟩
def law22 : Identity Nat := ⟨(Word.mk 0 [1, 0, 2, 2]), (Word.mk 0 [1, 2, 0, 2])⟩
def law23 : Identity Nat := ⟨(Word.mk 0 [1, 0, 2, 2]), (Word.mk 0 [1, 2, 2, 0])⟩
def law24 : Identity Nat := ⟨(Word.mk 0 [1, 1, 2, 1]), (Word.mk 0 [1, 2, 1, 1])⟩
def law25 : Identity Nat := ⟨(Word.mk 0 [1, 1, 2, 2]), (Word.mk 0 [1, 2, 1, 2])⟩
def law26 : Identity Nat := ⟨(Word.mk 0 [1, 1, 2, 2]), (Word.mk 0 [1, 2, 2, 1])⟩
def law27 : Identity Nat := ⟨(Word.mk 0 [0, 1, 0]), (Word.mk 0 [1, 0, 0])⟩
def law28 : Identity Nat := ⟨(Word.mk 0 [0, 1, 1]), (Word.mk 0 [1, 0, 1])⟩
def law29 : Identity Nat := ⟨(Word.mk 0 [0, 1, 1]), (Word.mk 0 [1, 1, 0])⟩
def law30 : Identity Nat := ⟨(Word.mk 0 [1, 0, 2, 3, 2]), (Word.mk 0 [1, 2, 0, 3, 2])⟩
def law31 : Identity Nat := ⟨(Word.mk 2 [1, 0, 2, 3, 0]), (Word.mk 2 [1, 2, 0, 3, 0])⟩

def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09, law10, law11, law12, law13, law14, law15, law16, law17, law18, law19, law20, law21, law22, law23, law24, law25, law26, law27, law28, law29, law30, law31]
abbrev displayedBasisSHA256 : String := "813c39eb60d6b5d7cf668315e5b2f08cc4d71c712f185a1753a7cf71f6e5a452"

theorem basis_length : basis.length = 32 := by decide

theorem rawLaw00 (u : Word Nat) :
    Derives basis (u ++ u) (((u ++ u) ++ u) ++ u) := by
  have primitive : Derives basis law00.lhs law00.rhs :=
    Derives.fromBasis (e := law00) (by decide)
  have mapped := primitive.subst (fun _ => u)
  simpa [law00, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw01 (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((((u ++ u) ++ u) ++ v) ++ u) := by
  have primitive : Derives basis law01.lhs law01.rhs :=
    Derives.fromBasis (e := law01) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law01, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw02 (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((((u ++ u) ++ v) ++ u) ++ u) := by
  have primitive : Derives basis law02.lhs law02.rhs :=
    Derives.fromBasis (e := law02) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law02, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw03 (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((((u ++ u) ++ v) ++ v) ++ v) := by
  have primitive : Derives basis law03.lhs law03.rhs :=
    Derives.fromBasis (e := law03) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law03, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw04 (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((((u ++ v) ++ u) ++ u) ++ u) := by
  have primitive : Derives basis law04.lhs law04.rhs :=
    Derives.fromBasis (e := law04) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law04, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw05 (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((((u ++ v) ++ u) ++ v) ++ v) := by
  have primitive : Derives basis law05.lhs law05.rhs :=
    Derives.fromBasis (e := law05) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law05, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw06 (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((((u ++ v) ++ v) ++ u) ++ v) := by
  have primitive : Derives basis law06.lhs law06.rhs :=
    Derives.fromBasis (e := law06) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law06, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw07 (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((((u ++ v) ++ v) ++ v) ++ u) := by
  have primitive : Derives basis law07.lhs law07.rhs :=
    Derives.fromBasis (e := law07) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law07, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw08 (u v : Word Nat) :
    Derives basis ((((u ++ u) ++ u) ++ v) ++ v) ((((u ++ u) ++ v) ++ u) ++ v) := by
  have primitive : Derives basis law08.lhs law08.rhs :=
    Derives.fromBasis (e := law08) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law08, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw09 (u v : Word Nat) :
    Derives basis ((((u ++ u) ++ u) ++ v) ++ v) ((((u ++ u) ++ v) ++ v) ++ u) := by
  have primitive : Derives basis law09.lhs law09.rhs :=
    Derives.fromBasis (e := law09) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law09, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw10 (u v : Word Nat) :
    Derives basis ((((u ++ u) ++ u) ++ v) ++ v) ((((u ++ v) ++ u) ++ u) ++ v) := by
  have primitive : Derives basis law10.lhs law10.rhs :=
    Derives.fromBasis (e := law10) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law10, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw11 (u v : Word Nat) :
    Derives basis ((((u ++ u) ++ u) ++ v) ++ v) ((((u ++ v) ++ u) ++ v) ++ u) := by
  have primitive : Derives basis law11.lhs law11.rhs :=
    Derives.fromBasis (e := law11) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law11, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw12 (u v : Word Nat) :
    Derives basis ((((u ++ u) ++ u) ++ v) ++ v) ((((u ++ v) ++ v) ++ u) ++ u) := by
  have primitive : Derives basis law12.lhs law12.rhs :=
    Derives.fromBasis (e := law12) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law12, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw13 (u v w : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ u) ++ w) ((((u ++ v) ++ u) ++ u) ++ w) := by
  have primitive : Derives basis law13.lhs law13.rhs :=
    Derives.fromBasis (e := law13) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law13, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw14 (u v w : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ v) ++ w) ((((u ++ v) ++ u) ++ v) ++ w) := by
  have primitive : Derives basis law14.lhs law14.rhs :=
    Derives.fromBasis (e := law14) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law14, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw15 (u v w : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ v) ++ w) ((((u ++ v) ++ v) ++ u) ++ w) := by
  have primitive : Derives basis law15.lhs law15.rhs :=
    Derives.fromBasis (e := law15) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law15, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw16 (u v w : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ w) ++ u) ((((u ++ v) ++ u) ++ w) ++ u) := by
  have primitive : Derives basis law16.lhs law16.rhs :=
    Derives.fromBasis (e := law16) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law16, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw17 (u v w : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ w) ++ u) ((((u ++ v) ++ w) ++ u) ++ u) := by
  have primitive : Derives basis law17.lhs law17.rhs :=
    Derives.fromBasis (e := law17) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law17, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw18 (u v w : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ w) ++ v) ((((u ++ v) ++ u) ++ w) ++ v) := by
  have primitive : Derives basis law18.lhs law18.rhs :=
    Derives.fromBasis (e := law18) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law18, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw19 (u v w : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ w) ++ v) ((((u ++ v) ++ v) ++ w) ++ u) := by
  have primitive : Derives basis law19.lhs law19.rhs :=
    Derives.fromBasis (e := law19) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law19, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw20 (u v w : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ w) ++ v) ((((u ++ v) ++ w) ++ u) ++ v) := by
  have primitive : Derives basis law20.lhs law20.rhs :=
    Derives.fromBasis (e := law20) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law20, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw21 (u v w : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ w) ++ v) ((((u ++ v) ++ w) ++ v) ++ u) := by
  have primitive : Derives basis law21.lhs law21.rhs :=
    Derives.fromBasis (e := law21) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law21, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw22 (u v w : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ w) ++ w) ((((u ++ v) ++ w) ++ u) ++ w) := by
  have primitive : Derives basis law22.lhs law22.rhs :=
    Derives.fromBasis (e := law22) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law22, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw23 (u v w : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ w) ++ w) ((((u ++ v) ++ w) ++ w) ++ u) := by
  have primitive : Derives basis law23.lhs law23.rhs :=
    Derives.fromBasis (e := law23) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law23, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw24 (u v w : Word Nat) :
    Derives basis ((((u ++ v) ++ v) ++ w) ++ v) ((((u ++ v) ++ w) ++ v) ++ v) := by
  have primitive : Derives basis law24.lhs law24.rhs :=
    Derives.fromBasis (e := law24) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law24, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw25 (u v w : Word Nat) :
    Derives basis ((((u ++ v) ++ v) ++ w) ++ w) ((((u ++ v) ++ w) ++ v) ++ w) := by
  have primitive : Derives basis law25.lhs law25.rhs :=
    Derives.fromBasis (e := law25) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law25, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw26 (u v w : Word Nat) :
    Derives basis ((((u ++ v) ++ v) ++ w) ++ w) ((((u ++ v) ++ w) ++ w) ++ v) := by
  have primitive : Derives basis law26.lhs law26.rhs :=
    Derives.fromBasis (e := law26) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law26, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw27 (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have primitive : Derives basis law27.lhs law27.rhs :=
    Derives.fromBasis (e := law27) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law27, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw28 (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ v) (((u ++ v) ++ u) ++ v) := by
  have primitive : Derives basis law28.lhs law28.rhs :=
    Derives.fromBasis (e := law28) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law28, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw29 (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ v) (((u ++ v) ++ v) ++ u) := by
  have primitive : Derives basis law29.lhs law29.rhs :=
    Derives.fromBasis (e := law29) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law29, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw30 (u v w s : Word Nat) :
    Derives basis (((((u ++ v) ++ u) ++ w) ++ s) ++ w) (((((u ++ v) ++ w) ++ u) ++ s) ++ w) := by
  have primitive : Derives basis law30.lhs law30.rhs :=
    Derives.fromBasis (e := law30) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | 3 => s | _ => Word.singleton 0)
  simpa [law30, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw31 (u v w s : Word Nat) :
    Derives basis (((((w ++ v) ++ u) ++ w) ++ s) ++ u) (((((w ++ v) ++ w) ++ u) ++ s) ++ u) := by
  have primitive : Derives basis law31.lhs law31.rhs :=
    Derives.fromBasis (e := law31) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | 3 => s | _ => Word.singleton 0)
  simpa [law31, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped


end SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415
