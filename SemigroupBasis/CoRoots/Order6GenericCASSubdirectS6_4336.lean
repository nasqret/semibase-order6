import SemigroupBasis.Examples.CyclicThreeThree
import SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336
import SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_4336
import SemigroupBasis.Generated.S3_18
import SemigroupBasis.Generated.S4_3

namespace SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_4336

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev rootBasis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.basis
private abbrev rootSemigroup : Semigroup (Fin 6) :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.oppositeTable.semigroup
private abbrev factorPair :=
  SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_4336.subdirectPair

private def instantiateOneWord (word : Word Nat) : Nat → Word Nat
  | 0 => word
  | n + 1 => Word.singleton (n + 1)

private def instantiateTwoWords
    (first second : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | n + 2 => Word.singleton (n + 2)

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

private theorem rootLaw0 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law0.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law0.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.basis]

private theorem rootLaw2 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law2.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law2.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.basis]

private theorem rootLaw3 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law3.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law3.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.basis]

private theorem rootLaw5 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law5.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law5.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.basis]

private theorem derivesCommutativity (left right : Word Nat) :
    Derives rootBasis (left ++ right) (right ++ left) := by
  have substituted :=
    Derives.subst rootLaw2 (instantiateTwoWords left right)
  simpa [SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law2,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton] using
      substituted

/-- The root laws derive the long cancellation law for `C(3,3)`: first add
a triple to a supported coordinate, transfer it to the requested coordinate,
and commute it to the front. -/
private theorem derivesCyclicThreeThreeLongCancellation :
    Derives rootBasis
      cyclicThreeThreeLongCancellationLaw.lhs
      cyclicThreeThreeLongCancellationLaw.rhs := by
  let x := Word.singleton 0
  let y := Word.singleton 1
  let z := Word.singleton 2
  let t := Word.singleton 3
  let yzt := (y ++ z) ++ t
  let xxx := (x ++ x) ++ x
  have addTriple :=
    Derives.subst rootLaw3 (instantiateThreeWords y z t)
  have transferTriple :=
    Derives.subst rootLaw5 (instantiateThreeWords y (z ++ t) x)
  have moveTriple := derivesCommutativity yzt xxx
  apply Derives.symm
  exact Derives.trans
    (by
      simpa [yzt, x, y, z, t,
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law3,
        instantiateThreeWords, Word.bind, Word.append, Word.singleton,
        Word.append_assoc] using addTriple)
    (Derives.trans
      (by
        simpa [yzt, xxx, x, y, z, t,
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law5,
          instantiateThreeWords, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using transferTriple)
      (by
        simpa [cyclicThreeThreeLongCancellationLaw,
          cyclicThreeThreeXXXYZT, cyclicThreeThreeYZT,
          yzt, xxx, x, y, z, t, Word.append, Word.singleton,
          Word.append_assoc] using moveTriple))

private theorem cyclicThreeThreeBasisLawDerives
    (identity : Identity Nat)
    (member : identity ∈ cyclicThreeThreeBasis) :
    Derives rootBasis identity.lhs identity.rhs := by
  simp only [cyclicThreeThreeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact derivesCommutativity (Word.singleton 0) (Word.singleton 1)
  · exact derivesCyclicThreeThreeLongCancellation

private theorem derivesCyclicThreeThree
    {left right : Word Nat}
    (derivation : Derives cyclicThreeThreeBasis left right) :
    Derives rootBasis left right :=
  derivation.transport cyclicThreeThreeBasisLawDerives

private theorem derivesPermutation (left right : Word Nat)
    (permutation : left.toList.Perm right.toList) :
    Derives rootBasis left right :=
  derivesCyclicThreeThree <|
    cyclicThreeThreeDerivesPermutation left right permutation

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-- Expand a diagonal quadratic word by one triple. All other words are
unchanged. Thus exactly the common `S4_3` class becomes long. -/
private def commonize : Word Nat → Word Nat
  | ⟨head, next :: []⟩ =>
      if head = next then wordOfCons head [head, head, head, head]
      else wordOfCons head [next]
  | word => word

private theorem derivesCommonize (word : Word Nat) :
    Derives rootBasis word (commonize word) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => exact Derives.refl _
      | cons next rest =>
          cases rest with
          | nil =>
              by_cases diagonal : head = next
              · subst next
                have expanded :=
                  Derives.subst rootLaw0
                    (instantiateOneWord (Word.singleton head))
                simpa [commonize, wordOfCons,
                  SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.law0,
                  instantiateOneWord, Word.bind, Word.append,
                  Word.singleton] using expanded
              · simpa [commonize, diagonal, wordOfCons] using
                  (Derives.refl (wordOfCons head [next]) :
                    Derives rootBasis (wordOfCons head [next])
                      (wordOfCons head [next]))
          | cons third rest =>
              exact Derives.refl _

private theorem commonize_long_of_shape_common
    (word : Word Nat)
    (common : commutativeCommonSquareShape word =
      CommutativeCommonSquareShape.common) :
    3 ≤ (commonize word).toList.length := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [commutativeCommonSquareShape] at common
      | cons next rest =>
          cases rest with
          | nil =>
              by_cases diagonal : head = next
              · subst next
                simp [commonize, wordOfCons, Word.toList]
              · simp [commutativeCommonSquareShape, diagonal] at common
          | cons third rest =>
              simp [commonize, Word.toList]

private theorem length_lt_three_of_shape_ne_common
    (word : Word Nat)
    (notCommon : commutativeCommonSquareShape word ≠
      CommutativeCommonSquareShape.common) :
    word.toList.length < 3 := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => simp [Word.toList]
      | cons next rest =>
          cases rest with
          | nil => simp [Word.toList]
          | cons third rest =>
              simp [commutativeCommonSquareShape] at notCommon

private theorem commonize_count_mod
    (word : Word Nat) (tested : Nat) :
    (commonize word).toList.count tested % 3 =
      word.toList.count tested % 3 := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => rfl
      | cons next rest =>
          cases rest with
          | nil =>
              by_cases diagonal : head = next
              · subst next
                by_cases same : tested = head
                · subst tested
                  simp [commonize, wordOfCons, Word.toList]
                · simp [commonize, wordOfCons, same,
                    Ne.symm same, Word.toList]
              · simp [commonize, diagonal, wordOfCons, Word.toList]
          | cons third rest => rfl

private theorem catalogueS3_18_table_eq_cyclicThree :
    SemigroupBasis.Generated.Catalogue.S3_18.table = cyclicThree := by
  calc
    SemigroupBasis.Generated.Catalogue.S3_18.table =
        SemigroupBasis.Generated.S3_18.table :=
      SemigroupBasis.Generated.S3_18.table_eq_canonical_catalogue.symm
    _ = cyclicThree :=
      SemigroupBasis.Generated.S3_18.table_eq_catalogue_model

private theorem catalogueS4_3_table_eq_commonSquare :
    SemigroupBasis.Generated.Catalogue.S4_3.table =
      commutativeCommonSquareThreeNilpotentFour := by
  calc
    SemigroupBasis.Generated.Catalogue.S4_3.table =
        SemigroupBasis.Generated.S4_3.table :=
      SemigroupBasis.Generated.S4_3.table_eq_canonical_catalogue.symm
    _ = commutativeCommonSquareThreeNilpotentFour :=
      SemigroupBasis.Generated.S4_3.table_eq_catalogue_model

private theorem satisfiedBy_of_table_eq
    {source target : FiniteTable} (tableEq : source = target)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy source.semigroup) :
    identity.SatisfiedBy target.semigroup := by
  cases tableEq
  exact valid

private theorem factorIntersectionComplete
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S3_18.table.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S4_3.table.semigroup) :
    Derives rootBasis identity.lhs identity.rhs := by
  have leftValid' : identity.SatisfiedBy cyclicThree.semigroup :=
    satisfiedBy_of_table_eq catalogueS3_18_table_eq_cyclicThree
      identity leftValid
  have rightValid' :
      identity.SatisfiedBy
        commutativeCommonSquareThreeNilpotentFour.semigroup :=
    satisfiedBy_of_table_eq catalogueS4_3_table_eq_commonSquare
      identity rightValid
  have modEq :
      ∀ tested,
        identity.lhs.toList.count tested % 3 =
          identity.rhs.toList.count tested % 3 :=
    cyclicThreeValid_mod_eq identity leftValid'
  have shapeEq :=
    commutativeCommonSquareShape_eq_of_valid identity rightValid'
  by_cases lhsCommon :
      commutativeCommonSquareShape identity.lhs =
        CommutativeCommonSquareShape.common
  · have rhsCommon :
        commutativeCommonSquareShape identity.rhs =
          CommutativeCommonSquareShape.common := by
      rw [← shapeEq]
      exact lhsCommon
    have lhsLong :=
      commonize_long_of_shape_common identity.lhs lhsCommon
    have rhsLong :=
      commonize_long_of_shape_common identity.rhs rhsCommon
    have commonizedMod :
        ∀ tested,
          (commonize identity.lhs).toList.count tested % 3 =
            (commonize identity.rhs).toList.count tested % 3 := by
      intro tested
      exact (commonize_count_mod identity.lhs tested).trans <|
        (modEq tested).trans
          (commonize_count_mod identity.rhs tested).symm
    exact Derives.trans (derivesCommonize identity.lhs) <|
      Derives.trans
        (derivesCyclicThreeThree <|
          cyclicThreeThreeDerivesLongModThree
            (commonize identity.lhs) (commonize identity.rhs)
            lhsLong rhsLong commonizedMod)
        (Derives.symm (derivesCommonize identity.rhs))
  · have rhsNotCommon :
        commutativeCommonSquareShape identity.rhs ≠
          CommutativeCommonSquareShape.common := by
      intro rhsCommon
      apply lhsCommon
      rw [shapeEq]
      exact rhsCommon
    have lhsShort :=
      length_lt_three_of_shape_ne_common identity.lhs lhsCommon
    have rhsShort :=
      length_lt_three_of_shape_ne_common identity.rhs rhsNotCommon
    have countEq :
        ∀ tested,
          identity.lhs.toList.count tested =
            identity.rhs.toList.count tested := by
      intro tested
      have lhsBound :=
        List.count_le_length (a := tested) (l := identity.lhs.toList)
      have rhsBound :=
        List.count_le_length (a := tested) (l := identity.rhs.toList)
      have residue := modEq tested
      omega
    exact derivesPermutation identity.lhs identity.rhs <|
      List.perm_iff_count.mpr countEq

private theorem leftFactorModels :
    Models
      SemigroupBasis.Generated.Catalogue.S3_18.table.semigroup
      rootBasis := by
  intro identity member
  exact factorPair.left.pushforwardIdentity identity
    (SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.models
      identity member)

private theorem rightFactorModels :
    Models
      SemigroupBasis.Generated.Catalogue.S4_3.table.semigroup
      rootBasis := by
  intro identity member
  exact factorPair.right.pushforwardIdentity identity
    (SemigroupBasis.Generated.Order6GenericCASRootData.S6_4336.models
      identity member)

/-- Exact unconditional basis endpoint for the mixed generic-CAS root
`S6_4336`. -/
theorem basisFor : BasisFor rootSemigroup rootBasis :=
  (IntersectionBasis.mk leftFactorModels rightFactorModels
    factorIntersectionComplete).basisFor factorPair

end SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_4336
