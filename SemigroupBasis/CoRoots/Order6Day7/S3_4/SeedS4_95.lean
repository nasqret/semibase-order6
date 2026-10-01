import SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS4_95RelativeLift
import SemigroupBasis.CoRoots.Order6GenericCASShortTwo
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.Examples.LeftZeroTwo

/-!
# Independent unrestricted S3_4 × S4_95 rank-013 seed

The exact states 2 and 3 in the actual parity-initial factor form an
explicitly kernel-checked copy of the two-element left-zero semigroup.
Pulling back validity along this concrete embedding proves initial-letter
equality without assuming or fabricating unrestricted factor separation.

The S3_4 classifier reduces all valid identities to literal, quadratic, or
long.  Quadratic permutation plus equal heads is literal.  Long identities
are handled by the exact two-block guarded parity lift and frozen initial
double expansion.  Unrestricted completeness precedes quotient normalization
and discharges all three authenticated classes and six orientations.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS4_95

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev targetBasis : List (Identity Nat) := Rank013.basis

private abbrev leftFactor := Rank013.leftTable.semigroup

private abbrev rightFactor := Rank013.rightTable.semigroup

private def word (first : Nat) (rest : List Nat) : Word Nat :=
  Word.mk first rest

/-- The actual S4_95 states 2 and 3 form an embedded left-zero pair. -/
def leftZeroEmbedding :
    Embedding leftZeroTwo.semigroup
      SemigroupBasis.Generated.S4_95.table.semigroup where
  toFun := fun value : Fin 2 =>
    if value = 0 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by
    intro first second
    exact by decide +revert
  injective := by
    intro first second same
    exact by decide +revert

/-- Actual parity-factor validity forces equal unrestricted initial letters. -/
theorem sameInitialOfValid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy SemigroupBasis.Generated.S4_95.table.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  have leftZeroValid := leftZeroEmbedding.pullback_identity identity valid
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 :=
    fun letter => if letter = identity.lhs.head then 0 else 1
  have evaluated := leftZeroValid valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm different] at evaluated

/-- Reuse the ten exact frozen left-factor displayed-law witnesses. -/
theorem modelsLeft : Models leftFactor targetBasis :=
  Rank013.leftModels

/-- Reuse the ten exact frozen right-factor displayed-law witnesses. -/
theorem modelsRight : Models rightFactor targetBasis :=
  Rank013.rightModels

private theorem quadraticWordsEqual
    (first second third fourth : Nat)
    (permutation : [first, second].Perm [third, fourth])
    (sameInitial : first = third) :
    word first [second] = word third [fourth] := by
  subst third
  have tails : [second].Perm [fourth] := by
    simpa using permutation.erase first
  have singletonEqual : [second] = [fourth] :=
    List.perm_singleton.mp tails
  have finalEqual : second = fourth := by
    simpa using singletonEqual
  subst fourth
  rfl

private theorem quadraticIdentityLiteral
    (identity : Identity Nat)
    (leftTwo : identity.lhs.toList.length = 2)
    (rightTwo : identity.rhs.toList.length = 2)
    (permutation : identity.lhs.toList.Perm identity.rhs.toList)
    (sameInitial : identity.lhs.head = identity.rhs.head) :
    identity.lhs = identity.rhs := by
  cases identity with
  | mk left right =>
      cases left with
      | mk leftFirst leftTail =>
          cases leftTail with
          | nil => simp [Word.toList] at leftTwo
          | cons leftSecond leftRest =>
              have leftRestNil : leftRest = [] := by
                simp [Word.toList] at leftTwo
                omega
              subst leftRest
              cases right with
              | mk rightFirst rightTail =>
                  cases rightTail with
                  | nil => simp [Word.toList] at rightTwo
                  | cons rightSecond rightRest =>
                      have rightRestNil : rightRest = [] := by
                        simp [Word.toList] at rightTwo
                        omega
                      subst rightRest
                      exact quadraticWordsEqual
                        leftFirst leftSecond rightFirst rightSecond
                        (by simpa [word, Word.toList] using permutation)
                        (by simpa using sameInitial)

/-- Independent unrestricted completeness for the exact ten frozen laws. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives targetBasis identity.lhs identity.rhs := by
  have canonicalValid :
      identity.SatisfiedBy SemigroupBasis.Generated.S4_95.table.semigroup := by
    rw [SemigroupBasis.Generated.S4_95.table_eq_canonical_catalogue]
    exact rightValid
  have sameInitial := sameInitialOfValid identity canonicalValid
  have shortValid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.Order6GenericCASShortTwo.shortFactor :=
    leftValid
  rcases
      SemigroupBasis.CoRoots.Order6GenericCASShortTwo.classifyValidIdentity
        identity shortValid with
    literal | quadratic | long
  · rw [literal]
    exact Derives.refl _
  · rcases quadratic with ⟨leftTwo, rightTwo, permutation⟩
    have literal :=
      quadraticIdentityLiteral
        identity leftTwo rightTwo permutation sameInitial
    rw [literal]
    exact Derives.refl _
  · have lower :=
      SemigroupBasis.Generated.S4_95.representative_basis.2
        identity canonicalValid
    exact derivesLongOfLowerAndSameInitial
      lower long.1 long.2 sameInitial

/-- The exact unrestricted independently proved ten-law intersection. -/
def intersectionBasis :
    IntersectionBasis
      Rank013.leftTable.semigroup
      Rank013.rightTable.semigroup
      Rank013.basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := derivesOfFactorValid

/-- Quotient normalization only after independent unrestricted completeness. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      Rank013.leftTable.semigroup
      Rank013.rightTable.semigroup
      Rank013.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- First exact authenticated rank-013 representative endpoint. -/
theorem representative_basis_S6_5746 :
    BasisFor Rank013.S6_5746.table.semigroup Rank013.basis :=
  Rank013.S6_5746.representative_basis_of_normalizer intersectionNormalizer

/-- Literal reversed-basis opposite endpoint for S6_5746. -/
theorem opposite_basis_S6_5746 :
    BasisFor Rank013.S6_5746.table.semigroup.opposite
      (reversedBasis Rank013.basis) :=
  Rank013.S6_5746.opposite_basis_of_normalizer intersectionNormalizer

/-- Second exact authenticated rank-013 representative endpoint. -/
theorem representative_basis_S6_5760 :
    BasisFor Rank013.S6_5760.table.semigroup Rank013.basis :=
  Rank013.S6_5760.representative_basis_of_normalizer intersectionNormalizer

/-- Literal reversed-basis opposite endpoint for S6_5760. -/
theorem opposite_basis_S6_5760 :
    BasisFor Rank013.S6_5760.table.semigroup.opposite
      (reversedBasis Rank013.basis) :=
  Rank013.S6_5760.opposite_basis_of_normalizer intersectionNormalizer

/-- Third exact authenticated rank-013 representative endpoint. -/
theorem representative_basis_S6_9534 :
    BasisFor Rank013.S6_9534.table.semigroup Rank013.basis :=
  Rank013.S6_9534.representative_basis_of_normalizer intersectionNormalizer

/-- Literal reversed-basis opposite endpoint for S6_9534. -/
theorem opposite_basis_S6_9534 :
    BasisFor Rank013.S6_9534.table.semigroup.opposite
      (reversedBasis Rank013.basis) :=
  Rank013.S6_9534.opposite_basis_of_normalizer intersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS4_95
