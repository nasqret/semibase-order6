import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S2_2
import SemigroupBasis.Generated.S3_11
import SemigroupBasis.CoRoots.S5_240Completeness
import SemigroupBasis.CoRoots.S5_107ListDerives

/-! Exact ordered B23 for the first shared level-3 section. The complete
positive-parity calculus is lifted only before TWO nonempty suffix blocks.
Every displayed-law edge below has explicit typed endpoints and decide
membership. No completeness claim is made by this module alone. -/

namespace SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section01.Section01Macros

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107

def law00 : Identity Nat := ⟨Word.mk 0 [0], Word.mk 0 [0, 0, 0]⟩
def law01 : Identity Nat := ⟨Word.mk 0 [0, 0, 1, 0], Word.mk 0 [1, 0]⟩
def law02 : Identity Nat := ⟨Word.mk 0 [0, 0, 1, 1], Word.mk 0 [1, 1]⟩
def law03 : Identity Nat := ⟨Word.mk 0 [0, 0, 1, 2], Word.mk 0 [1, 2]⟩
def law04 : Identity Nat := ⟨Word.mk 0 [0, 1, 0, 1], Word.mk 0 [1, 1]⟩
def law05 : Identity Nat := ⟨Word.mk 0 [0, 1, 1], Word.mk 0 [1, 0, 1]⟩
def law06 : Identity Nat := ⟨Word.mk 0 [0, 1, 1], Word.mk 0 [1, 1, 0]⟩
def law07 : Identity Nat := ⟨Word.mk 0 [0, 1, 1], Word.mk 1 [0, 0, 1]⟩
def law08 : Identity Nat := ⟨Word.mk 0 [0, 1, 1, 0], Word.mk 0 [1, 1]⟩
def law09 : Identity Nat := ⟨Word.mk 0 [1, 0, 0], Word.mk 0 [1, 1, 1]⟩
def law10 : Identity Nat := ⟨Word.mk 0 [1, 0, 0], Word.mk 1 [0, 0, 0]⟩
def law11 : Identity Nat := ⟨Word.mk 0 [1, 0, 0, 1], Word.mk 0 [1, 1]⟩
def law12 : Identity Nat := ⟨Word.mk 0 [1, 0, 1, 0], Word.mk 0 [1, 1]⟩
def law13 : Identity Nat := ⟨Word.mk 0 [1, 0, 2], Word.mk 1 [0, 0, 2]⟩
def law14 : Identity Nat := ⟨Word.mk 0 [1, 1], Word.mk 0 [1, 1, 0, 0]⟩
def law15 : Identity Nat := ⟨Word.mk 0 [1, 1], Word.mk 1 [0, 0, 0, 1]⟩
def law16 : Identity Nat := ⟨Word.mk 0 [1, 1], Word.mk 1 [0, 0, 1, 0]⟩
def law17 : Identity Nat := ⟨Word.mk 0 [1, 1], Word.mk 1 [0, 1, 0, 0]⟩
def law18 : Identity Nat := ⟨Word.mk 0 [1, 1], Word.mk 1 [0, 1, 1, 1]⟩
def law19 : Identity Nat := ⟨Word.mk 0 [1, 1], Word.mk 1 [1, 0, 0, 0]⟩
def law20 : Identity Nat := ⟨Word.mk 0 [1, 1], Word.mk 1 [1, 0, 1, 1]⟩
def law21 : Identity Nat := ⟨Word.mk 0 [1, 2, 0], Word.mk 1 [0, 2, 0]⟩
def law22 : Identity Nat := ⟨Word.mk 0 [1, 2, 2], Word.mk 1 [0, 2, 2]⟩

def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09,
   law10, law11, law12, law13, law14, law15, law16, law17, law18, law19,
   law20, law21, law22]

abbrev displayedBasisSHA256 : String := "383b08f45c1cc8c2a6919cb992641ac5b88c0b6879944a2d8a47196f96895a5e"
abbrev leftTable : FiniteTable := Generated.S2_2.table
abbrev alternateTable : FiniteTable := Generated.S3_11.table
abbrev rightTable : FiniteTable := Generated.Catalogue.S5_240.table
abbrev D := ListDerives basis

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem basis_length : basis.length = 23 := by decide
theorem modelsLeft : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)
theorem modelsAlternate : Models alternateTable.semigroup basis :=
  FiniteCertificate.checkModels_sound alternateTable basis toFinThree (by decide)
theorem modelsRight : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)

theorem leftBasis_complete : BasisFor leftTable.semigroup cyclicTwoBasis :=
  Generated.S2_2.representative_basis
theorem alternateBasis_complete :
    BasisFor alternateTable.semigroup commutativeParityBasis :=
  Generated.S3_11.representative_basis
theorem rightBasis_complete : BasisFor rightTable.semigroup CoRoots.S5_240.basis :=
  CoRoots.S5_240.representative_basis

theorem guardedTriple (x a b : Word Nat) :
    Derives basis ((((x ++ x) ++ x) ++ a) ++ b) ((x ++ a) ++ b) := by
  have primitive : Derives basis law03.lhs law03.rhs :=
    Derives.fromBasis (e := law03) (by decide)
  have mapped := primitive.subst (fun
    | 0 => x
    | 1 => a
    | 2 => b
    | _ => Word.singleton 0)
  simpa [law03, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem guardedCommutativity (x y a b : Word Nat) :
    Derives basis (((x ++ y) ++ a) ++ b) (((y ++ x) ++ a) ++ b) := by
  have first : Derives basis (((x ++ y) ++ a) ++ b)
      (((x ++ ((y ++ y) ++ y)) ++ a) ++ b) := by
    simpa [Word.append_assoc] using Derives.prepend x (guardedTriple y a b).symm
  have second : Derives basis (((x ++ ((y ++ y) ++ y)) ++ a) ++ b)
      (((((x ++ y) ++ x) ++ x) ++ a) ++ b) := by
    have primitive : Derives basis law09.lhs law09.rhs :=
      Derives.fromBasis (e := law09) (by decide)
    have mapped := primitive.subst (fun | 0 => x | 1 => y | _ => Word.singleton 0)
    simpa [law09, Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.appendRight mapped.symm (a ++ b)
  have third : Derives basis (((((x ++ y) ++ x) ++ x) ++ a) ++ b)
      (((y ++ ((x ++ x) ++ x)) ++ a) ++ b) := by
    have primitive : Derives basis law10.lhs law10.rhs :=
      Derives.fromBasis (e := law10) (by decide)
    have mapped := primitive.subst (fun | 0 => x | 1 => y | _ => Word.singleton 0)
    simpa [law10, Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.appendRight mapped (a ++ b)
  have fourth : Derives basis (((y ++ ((x ++ x) ++ x)) ++ a) ++ b)
      (((y ++ x) ++ a) ++ b) := by
    simpa [Word.append_assoc] using Derives.prepend y (guardedTriple x a b)
  exact first.trans (second.trans (third.trans fourth))

theorem parityBasis_literal : commutativeParityBasis =
    [⟨Word.mk 0 [], Word.mk 0 [0, 0]⟩, ⟨Word.mk 0 [1], Word.mk 1 [0]⟩] := by decide

theorem guardedParityAxiom (identity : Identity Nat)
    (member : identity ∈ commutativeParityBasis) (substitution : Nat → Word Nat)
    (a b : Word Nat) :
    Derives basis ((identity.lhs.bind substitution ++ a) ++ b)
      ((identity.rhs.bind substitution ++ a) ++ b) := by
  rw [parityBasis_literal] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      (guardedTriple (substitution 0) a b).symm
  · simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      guardedCommutativity (substitution 0) (substitution 1) a b

private theorem bind_append (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution = left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second = word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) : word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Full derivation induction, including arbitrary substitutions and contexts. -/
theorem liftParity {left right : Word Nat}
    (derivation : Derives commutativeParityBasis left right)
    (a b : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis ((left.bind substitution ++ a) ++ b)
      ((right.bind substitution ++ a) ++ b) := by
  induction derivation generalizing a b substitution with
  | fromBasis member => exact guardedParityAxiom _ member substitution a b
  | refl => exact Derives.refl _
  | symm _ ih => exact (ih a b substitution).symm
  | trans _ _ first second => exact (first a b substitution).trans (second a b substitution)
  | prepend stem _ ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (stem.bind substitution) (ih a b substitution)
  | appendRight _ final ih =>
      simpa [bind_append, Word.append_assoc] using ih (final.bind substitution ++ a) b substitution
  | subst _ next ih =>
      simpa [bind_bind] using ih a b (fun letter => (next letter).bind substitution)

theorem parityDerivesOfSupportParity (left right : Word Nat)
    (support : ∀ z, z ∈ left.toList ↔ z ∈ right.toList)
    (parity : ∀ z, left.toList.count z % 2 = right.toList.count z % 2) :
    Derives commutativeParityBasis left right := by
  have permutation := positiveParityReduce_perm support parity
  have leftNormal := positiveParityDerivesNormal left
  have rightNormal := positiveParityDerivesNormal right
  cases hl : positiveParityReduce left.toList with
  | nil =>
      have present := (mem_positiveParityReduce_iff left.head left.toList).mpr
        (by simp [Word.toList])
      simp [hl] at present
  | cons x xs =>
      cases hr : positiveParityReduce right.toList with
      | nil =>
          rw [hl, hr] at permutation
          exact False.elim (List.not_perm_cons_nil permutation)
      | cons y ys =>
          rw [hl] at leftNormal
          rw [hr] at rightNormal
          rw [hl, hr] at permutation
          exact leftNormal.trans ((parityDerivesPermutation
            (Word.mk x xs) (Word.mk y ys) permutation).trans rightNormal.symm)

/-- Empty prefixes are legitimate list contexts, not empty word substitutions. -/
theorem prefixOfSupportParity (left right : List Nat) (p t : Nat)
    (support : ∀ z, z ∈ left ↔ z ∈ right)
    (parity : ∀ z, left.count z % 2 = right.count z % 2) :
    D (left ++ [p, t]) (right ++ [p, t]) := by
  cases left with
  | nil =>
      cases right with
      | nil => exact ListDerives.refl _
      | cons y ys =>
          have bad := (support y).mpr (by simp)
          simp at bad
  | cons x xs =>
      cases right with
      | nil =>
          have bad := (support x).mp (by simp)
          simp at bad
      | cons y ys =>
          have lower := parityDerivesOfSupportParity (Word.mk x xs) (Word.mk y ys) support parity
          have lifted := liftParity lower (Word.singleton p) (Word.singleton t) Word.singleton
          simpa [bind_singleton, Word.toList, Word.append, Word.singleton,
            List.append_assoc] using ListDerives.ofWord lifted

theorem prefixPermutation {left right : List Nat} (permutation : left.Perm right) (p t : Nat) :
    D (left ++ [p, t]) (right ++ [p, t]) :=
  prefixOfSupportParity left right p t (fun _ => permutation.mem_iff)
    (fun z => congrArg (fun count => count % 2) (permutation.count_eq z))

theorem squarePadding (x : Nat) : D [x, x] [x, x, x, x] := by
  have primitive : Derives basis law00.lhs law00.rhs :=
    Derives.fromBasis (e := law00) (by decide)
  have mapped := primitive.subst (fun _ => Word.singleton x)
  simpa [law00, Word.bind, Word.append, Word.singleton, Word.toList] using ListDerives.ofWord mapped

theorem squareCommutation (x y : Nat) : D [x, x, y, y] [y, y, x, x] := by
  have first : D [x, x, y, y] [y, x, x, y] := by
    have primitive : Derives basis law07.lhs law07.rhs :=
      Derives.fromBasis (e := law07) (by decide)
    have mapped := primitive.subst (fun | 0 => Word.singleton x | 1 => Word.singleton y | _ => Word.singleton x)
    simpa [law07, Word.bind, Word.append, Word.singleton, Word.toList] using ListDerives.ofWord mapped
  have second : D [y, y, x, x] [y, x, x, y] := by
    have primitive : Derives basis law06.lhs law06.rhs :=
      Derives.fromBasis (e := law06) (by decide)
    have mapped := primitive.subst (fun | 0 => Word.singleton y | 1 => Word.singleton x | _ => Word.singleton x)
    simpa [law06, Word.bind, Word.append, Word.singleton, Word.toList] using ListDerives.ofWord mapped
  exact first.trans second.symm

theorem alternatingSquares (x y : Nat) : D [x, y, x, y] [x, x, y, y] := by
  have primitive : Derives basis law05.lhs law05.rhs :=
    Derives.fromBasis (e := law05) (by decide)
  have mapped := primitive.subst (fun | 0 => Word.singleton x | 1 => Word.singleton y | _ => Word.singleton x)
  simpa [law05, Word.bind, Word.append, Word.singleton, Word.toList] using ListDerives.ofWord mapped.symm

theorem derivesParity {left right : List Nat} (derivation : D left right) :
    ∀ z, left.count z % 2 = right.count z % 2 := by
  cases derivation with
  | empty => intro z; rfl
  | @words leftHead rightHead leftTail rightTail wordDerivation =>
      have valid : (Identity.mk (listWordOfCons leftHead leftTail)
          (listWordOfCons rightHead rightTail)).SatisfiedBy cyclicTwo.semigroup :=
        fun valuation => wordDerivation.sound modelsLeft valuation
      exact cyclicValid_parity_eq _ valid

end SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section01.Section01Macros
