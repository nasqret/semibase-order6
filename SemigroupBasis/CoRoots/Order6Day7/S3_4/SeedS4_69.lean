import SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS4_69RelativeLift
import SemigroupBasis.CoRoots.Order6GenericCASShortTwo
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal

/-!
# Independent unrestricted S3_4 × S4_69 rank-011 seed

The exact S3_4 classifier gives singleton, quadratic, and long regions.
The actual unique-separator S4_69 factor refutes the swapped quadratic
case using its noncommuting states 1 and 2.  On long endpoints, all seven
independently complete lower-factor axioms lift through the exact frozen
twelve-law basis with only bare unary squares protected.

The unrestricted intersection theorem precedes quotient normalization and
closes three authenticated classes and all six opposite orientations.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS4_69

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev targetBasis : List (Identity Nat) := Rank011.basis

private abbrev leftFactor := Rank011.leftTable.semigroup

private abbrev rightFactor := Rank011.rightTable.semigroup

private def word (first : Nat) (rest : List Nat) : Word Nat :=
  Word.mk first rest

/-- Reuse all twelve exact frozen left-factor validity witnesses. -/
theorem modelsLeft : Models leftFactor targetBasis :=
  Rank011.leftModels

/-- Reuse all twelve exact frozen right-factor validity witnesses. -/
theorem modelsRight : Models rightFactor targetBasis :=
  Rank011.rightModels

private def orderedPairSeparator
    (first second : Nat) : Nat → Fin 4 :=
  fun tested => if tested = first then 1 else if tested = second then 2 else 0

private theorem swappedQuadraticImpossible
    {first second : Nat} (different : first ≠ second)
    (valid :
      (Identity.mk (word first [second])
        (word second [first])).SatisfiedBy
        SemigroupBasis.Generated.S4_69.table.semigroup) :
    False := by
  have evaluated := valid (orderedPairSeparator first second)
  change
    uniqueSeparatorFourMul
        (orderedPairSeparator first second first)
        (orderedPairSeparator first second second) =
      uniqueSeparatorFourMul
        (orderedPairSeparator first second second)
        (orderedPairSeparator first second first) at evaluated
  have impossible : (0 : Fin 4) = 1 := by
    simp [orderedPairSeparator, different.symm,
      uniqueSeparatorFourMul] at evaluated
  exact (by decide : (0 : Fin 4) ≠ 1) impossible

private theorem quadraticWordsEqual
    (first second third fourth : Nat)
    (permutation : [first, second].Perm [third, fourth])
    (valid :
      (Identity.mk (word first [second])
        (word third [fourth])).SatisfiedBy
        SemigroupBasis.Generated.S4_69.table.semigroup) :
    word first [second] = word third [fourth] := by
  have support (tested : Nat) :
      (first = tested ∨ second = tested) ↔
        (third = tested ∨ fourth = tested) := by
    have membership :
        tested ∈ [first, second] ↔ tested ∈ [third, fourth] :=
      permutation.mem_iff
    simpa [eq_comm] using membership
  have thirdSource : third = first ∨ third = second := by
    have member := (support third).mpr (Or.inl rfl)
    exact member.imp Eq.symm Eq.symm
  have fourthSource : fourth = first ∨ fourth = second := by
    have member := (support fourth).mpr (Or.inr rfl)
    exact member.imp Eq.symm Eq.symm
  rcases thirdSource with thirdFirst | thirdSecond
  · rcases fourthSource with fourthFirst | fourthSecond
    · subst third
      subst fourth
      by_cases same : first = second
      · subst second
        rfl
      · have missing := (support second).mp (Or.inr rfl)
        have forced : first = second := missing.elim id id
        exact False.elim (same forced)
    · subst third
      subst fourth
      rfl
  · rcases fourthSource with fourthFirst | fourthSecond
    · subst third
      subst fourth
      by_cases same : first = second
      · subst second
        rfl
      · exact False.elim (swappedQuadraticImpossible same valid)
    · subst third
      subst fourth
      by_cases same : first = second
      · subst second
        rfl
      · have missing := (support first).mp (Or.inl rfl)
        have forced : second = first := missing.elim id id
        exact False.elim (same forced.symm)

private theorem quadraticIdentityLiteral
    (identity : Identity Nat)
    (leftTwo : identity.lhs.toList.length = 2)
    (rightTwo : identity.rhs.toList.length = 2)
    (permutation : identity.lhs.toList.Perm identity.rhs.toList)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_69.table.semigroup) :
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
                        (by simpa [word] using valid)

/-- Genuine unrestricted completeness of the frozen twelve-law intersection. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives targetBasis identity.lhs identity.rhs := by
  have canonicalValid :
      identity.SatisfiedBy SemigroupBasis.Generated.S4_69.table.semigroup := by
    rw [SemigroupBasis.Generated.S4_69.table_eq_canonical_catalogue]
    exact rightValid
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
        identity leftTwo rightTwo permutation canonicalValid
    rw [literal]
    exact Derives.refl _
  · have lower :=
      SemigroupBasis.Generated.S4_69.representative_basis.2
        identity canonicalValid
    exact liftLowerDerivationOfLong lower long.1 long.2

/-- The exact independently proved frozen twelve-law intersection. -/
def intersectionBasis :
    IntersectionBasis
      Rank011.leftTable.semigroup
      Rank011.rightTable.semigroup
      Rank011.basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := derivesOfFactorValid

/-- Quotient normalization only after unrestricted completeness. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      Rank011.leftTable.semigroup
      Rank011.rightTable.semigroup
      Rank011.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- First exact authenticated rank-011 representative endpoint. -/
theorem representative_basis_S6_5547 :
    BasisFor Rank011.S6_5547.table.semigroup Rank011.basis :=
  Rank011.S6_5547.representative_basis_of_normalizer intersectionNormalizer

/-- Literal reversed-basis opposite endpoint for S6_5547. -/
theorem opposite_basis_S6_5547 :
    BasisFor Rank011.S6_5547.table.semigroup.opposite
      (reversedBasis Rank011.basis) :=
  Rank011.S6_5547.opposite_basis_of_normalizer intersectionNormalizer

/-- Second exact authenticated rank-011 representative endpoint. -/
theorem representative_basis_S6_5557 :
    BasisFor Rank011.S6_5557.table.semigroup Rank011.basis :=
  Rank011.S6_5557.representative_basis_of_normalizer intersectionNormalizer

/-- Literal reversed-basis opposite endpoint for S6_5557. -/
theorem opposite_basis_S6_5557 :
    BasisFor Rank011.S6_5557.table.semigroup.opposite
      (reversedBasis Rank011.basis) :=
  Rank011.S6_5557.opposite_basis_of_normalizer intersectionNormalizer

/-- Third exact authenticated rank-011 representative endpoint. -/
theorem representative_basis_S6_9631 :
    BasisFor Rank011.S6_9631.table.semigroup Rank011.basis :=
  Rank011.S6_9631.representative_basis_of_normalizer intersectionNormalizer

/-- Literal reversed-basis opposite endpoint for S6_9631. -/
theorem opposite_basis_S6_9631 :
    BasisFor Rank011.S6_9631.table.semigroup.opposite
      (reversedBasis Rank011.basis) :=
  Rank011.S6_9631.opposite_basis_of_normalizer intersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS4_69
