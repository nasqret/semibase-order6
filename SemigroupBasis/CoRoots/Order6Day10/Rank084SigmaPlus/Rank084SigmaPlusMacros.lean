import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S4_11
import SemigroupBasis.Generated.S4_77

/-! Exact reviewed B7, with all six raw laws retained. The added duplication
law is used in six explicitly typed nonerasing edges. Tail swap is a derived
consequence, never an extra assumption. Statement approval: fable0413. -/

namespace SemigroupBasis.CoRoots.Order6Day10.Rank084SigmaPlus.Rank084SigmaPlusMacros

open SemigroupBasis

def law00 : Identity Nat := ⟨Word.mk 0 [0, 0, 0], Word.mk 0 [0, 0, 1]⟩
def law01 : Identity Nat := ⟨Word.mk 0 [0, 0, 0], Word.mk 0 [0, 1, 0]⟩
def law02 : Identity Nat := ⟨Word.mk 0 [0, 0, 0], Word.mk 0 [0, 1, 2]⟩
def law03 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 1]⟩
def law04 : Identity Nat := ⟨Word.mk 0 [1, 0, 0], Word.mk 0 [1, 0, 2]⟩
def law05 : Identity Nat := ⟨Word.mk 0 [1, 0, 0], Word.mk 0 [1, 2, 0]⟩
def law06 : Identity Nat := ⟨Word.mk 0 [1, 2, 3], Word.mk 0 [1, 1, 2, 3]⟩

def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05, law06]
abbrev B7 := basis
abbrev displayedBasisSHA256 : String := "22363bad5c30f3bcb21ec410e0c6fbd125a31128fc189e67efd0acea4d95839f"
abbrev leftTable : FiniteTable := Generated.S4_11.table
abbrev rightTable : FiniteTable := Generated.S4_77.table

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

theorem basis_length : basis.length = 7 := by decide
set_option maxRecDepth 100000 in
theorem modelsLeft : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinFour (by decide)
set_option maxRecDepth 100000 in
theorem modelsRight : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinFour (by decide)
theorem leftBasis_complete : BasisFor leftTable.semigroup Examples.cyclicFourOneBasis :=
  Generated.S4_11.representative_basis
theorem rightBasis_complete : BasisFor rightTable.semigroup Examples.twoLetterPrefixBasis :=
  Generated.S4_77.representative_basis

private def fourWords (u v w t : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | 3 => t
  | _ => Word.singleton 0

theorem rawLaw00 (u v : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ u) (((u ++ u) ++ u) ++ v) := by
  have primitive : Derives basis law00.lhs law00.rhs := Derives.fromBasis (e := law00) (by decide)
  have mapped := primitive.subst (fourWords u v u u)
  simpa [law00, fourWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw01 (u v : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ u) (((u ++ u) ++ v) ++ u) := by
  have primitive : Derives basis law01.lhs law01.rhs := Derives.fromBasis (e := law01) (by decide)
  have mapped := primitive.subst (fourWords u v u u)
  simpa [law01, fourWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw02 (u v w : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ u) (((u ++ u) ++ v) ++ w) := by
  have primitive : Derives basis law02.lhs law02.rhs := Derives.fromBasis (e := law02) (by decide)
  have mapped := primitive.subst (fourWords u v w u)
  simpa [law02, fourWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw03 (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((u ++ v) ++ v) := by
  have primitive : Derives basis law03.lhs law03.rhs := Derives.fromBasis (e := law03) (by decide)
  have mapped := primitive.subst (fourWords u v u u)
  simpa [law03, fourWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw04 (u v w : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ u) (((u ++ v) ++ u) ++ w) := by
  have primitive : Derives basis law04.lhs law04.rhs := Derives.fromBasis (e := law04) (by decide)
  have mapped := primitive.subst (fourWords u v w u)
  simpa [law04, fourWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw05 (u v w : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ u) (((u ++ v) ++ w) ++ u) := by
  have primitive : Derives basis law05.lhs law05.rhs := Derives.fromBasis (e := law05) (by decide)
  have mapped := primitive.subst (fourWords u v w u)
  simpa [law05, fourWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw06 (u v w t : Word Nat) :
    Derives basis (((u ++ v) ++ w) ++ t) ((((u ++ v) ++ v) ++ w) ++ t) := by
  have primitive : Derives basis law06.lhs law06.rhs := Derives.fromBasis (e := law06) (by decide)
  have mapped := primitive.subst (fourWords u v w t)
  simpa [law06, fourWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem collapseEdge0 (p q r s : Word Nat) :
    Derives basis (((p ++ q) ++ r) ++ s) ((((p ++ q) ++ q) ++ r) ++ s) := rawLaw06 p q r s

theorem collapseEdge1 (p q r s : Word Nat) :
    Derives basis ((((p ++ q) ++ q) ++ r) ++ s) ((((p ++ q) ++ p) ++ r) ++ s) := by
  simpa only [Word.append_assoc] using Derives.appendRight (rawLaw03 p q).symm (r ++ s)

theorem collapseEdge2 (p q r s : Word Nat) :
    Derives basis ((((p ++ q) ++ p) ++ r) ++ s) ((((p ++ q) ++ p) ++ p) ++ s) :=
  Derives.appendRight (rawLaw04 p q r).symm s

theorem collapseEdge3 (p q s : Word Nat) :
    Derives basis ((((p ++ q) ++ p) ++ p) ++ s) ((((p ++ q) ++ q) ++ p) ++ s) := by
  simpa only [Word.append_assoc] using Derives.appendRight (rawLaw03 p q) (p ++ s)

theorem collapseEdge4 (p q s : Word Nat) :
    Derives basis ((((p ++ q) ++ q) ++ p) ++ s) (((p ++ q) ++ p) ++ s) := (rawLaw06 p q p s).symm

theorem collapseEdge5 (p q s : Word Nat) :
    Derives basis (((p ++ q) ++ p) ++ s) (((p ++ q) ++ p) ++ p) := (rawLaw04 p q s).symm

theorem longCollapse (p q r s : Word Nat) :
    Derives basis (((p ++ q) ++ r) ++ s) (((p ++ q) ++ p) ++ p) :=
  (collapseEdge0 p q r s).trans ((collapseEdge1 p q r s).trans
    ((collapseEdge2 p q r s).trans ((collapseEdge3 p q s).trans
      ((collapseEdge4 p q s).trans (collapseEdge5 p q s)))))

theorem tailSwap (p q r s : Word Nat) :
    Derives basis (((p ++ q) ++ r) ++ s) (((p ++ q) ++ s) ++ r) :=
  (longCollapse p q r s).trans (longCollapse p q s r).symm

theorem derivesLongWord (a b c d : Nat) (rest : List Nat) :
    Derives basis (Word.mk a (b :: c :: d :: rest)) (Word.mk a [b, a, a]) := by
  simpa [Word.singleton, Word.append, List.append_assoc] using
    longCollapse (Word.singleton a) (Word.singleton b) (Word.singleton c) (Word.mk d rest)

end SemigroupBasis.CoRoots.Order6Day10.Rank084SigmaPlus.Rank084SigmaPlusMacros
