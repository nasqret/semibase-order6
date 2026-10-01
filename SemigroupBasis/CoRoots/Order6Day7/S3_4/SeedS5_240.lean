import SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS5_240RelativeLift
import SemigroupBasis.CoRoots.Order6GenericCASShortTwo
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal

/-!
# Final independent unrestricted owner seed for the authenticated S3_4 family

The complete three-law S5_240 calculus lifts through the exact frozen
fifteen-law rank-085 basis while protecting only bare unary squares.  The
actual S5_240 catalogue states 3 and 2 separate swapped quadratic words;
the genuine S3_4 classifier and complete lower-factor semantics prove
unrestricted factor intersection BEFORE quotient normalization.

This closes both unconditional orientations of authenticated class S6_5854
and supplies the final independent owner proof for the eight-pair S3_4 family.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS5_240

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank085.basis

private abbrev leftFactor := Rank085.leftTable.semigroup

private abbrev rightFactor := Rank085.rightTable.semigroup

private def word (first : Nat) (rest : List Nat) : Word Nat :=
  Word.mk first rest

/-- Reuse every exact frozen left-factor displayed-law witness. -/
theorem modelsLeft : Models leftFactor targetBasis :=
  Rank085.leftModels

/-- Reuse every exact frozen right-factor displayed-law witness. -/
theorem modelsRight : Models rightFactor targetBasis :=
  Rank085.rightModels

private def orderedPairSeparator
    (first second : Nat) : Nat → Fin 5 :=
  fun tested => if tested = first then 3 else if tested = second then 2 else 0

private theorem swappedQuadraticImpossible
    {first second : Nat} (different : first ≠ second)
    (valid :
      (Identity.mk (word first [second])
        (word second [first])).SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup) :
    False := by
  have evaluated := valid (orderedPairSeparator first second)
  change
    SemigroupBasis.Generated.Catalogue.S5_240.mul
        (orderedPairSeparator first second first)
        (orderedPairSeparator first second second) =
      SemigroupBasis.Generated.Catalogue.S5_240.mul
        (orderedPairSeparator first second second)
        (orderedPairSeparator first second first) at evaluated
  simp [orderedPairSeparator, Ne.symm different,
    SemigroupBasis.Generated.Catalogue.S5_240.mul] at evaluated

private theorem quadraticWordsEqual
    (first second third fourth : Nat)
    (permutation : [first, second].Perm [third, fourth])
    (valid :
      (Identity.mk (word first [second])
        (word third [fourth])).SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup) :
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
        SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup) :
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

/-- Independent unrestricted completeness of the exact fifteen-law basis. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives targetBasis identity.lhs identity.rhs := by
  have canonicalValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup :=
    rightValid
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
      SemigroupBasis.CoRoots.S5_240.basis_complete.2
        identity canonicalValid
    exact liftLowerDerivationOfLong lower long.1 long.2

/-- Actual owner unrestricted intersection completeness before normalization. -/
def intersectionBasis :
    IntersectionBasis
      Rank085.leftTable.semigroup
      Rank085.rightTable.semigroup
      Rank085.basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := derivesOfFactorValid

/-- Quotient normalization strictly after unrestricted completeness. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      Rank085.leftTable.semigroup
      Rank085.rightTable.semigroup
      Rank085.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- Exact final authenticated rank-085 representative endpoint. -/
theorem representative_basis_S6_5854 :
    BasisFor Rank085.S6_5854.table.semigroup Rank085.basis :=
  Rank085.S6_5854.representative_basis_of_normalizer intersectionNormalizer

/-- Literal reversed-basis opposite endpoint for the authenticated class. -/
theorem opposite_basis_S6_5854 :
    BasisFor Rank085.S6_5854.table.semigroup.opposite
      (reversedBasis Rank085.basis) :=
  Rank085.S6_5854.opposite_basis_of_normalizer intersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS5_240
