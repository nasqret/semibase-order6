import SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS5_84RelativeLift
import SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004SiblingTransport
import SemigroupBasis.CoRoots.Order6GenericCASShortTwo
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal

/-!
# Independent rank-030 owner seed and explicitly recovered collision twin

The surviving `S3_4 × S5_84` envelope is proved independently using the
complete four-law S5_83/S5_84 basis, the genuine S3_4 short-word classifier,
and a concrete S5_84 noncommutation witness.  Its unrestricted intersection
basis precedes quotient normalization.

The codex-0-attested S5_83 collision successor is instantiated ONLY AFTER
that actual owner intersection exists.  Its reviewed bridge proves BOTH
unrestricted factor-theory directions from complete lower bases.  This
closes the two authenticated classes `S6_2639` and `S6_2638` and all four
orientation endpoints without overwriting the surviving frozen envelope.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS5_84

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank030.basis

private abbrev leftFactor := Rank030.leftTable.semigroup

private abbrev rightFactor := Rank030.rightTable.semigroup

private def word (first : Nat) (rest : List Nat) : Word Nat :=
  Word.mk first rest

/-- Reuse all six exact frozen left-factor displayed-law witnesses. -/
theorem modelsLeft : Models leftFactor targetBasis :=
  Rank030.leftModels

/-- Reuse all six exact frozen right-factor displayed-law witnesses. -/
theorem modelsRight : Models rightFactor targetBasis :=
  Rank030.rightModels

private def orderedPairSeparator
    (first second : Nat) : Nat → Fin 5 :=
  fun tested => if tested = first then 3 else if tested = second then 2 else 0

private theorem swappedQuadraticImpossible
    {first second : Nat} (different : first ≠ second)
    (valid :
      (Identity.mk (word first [second])
        (word second [first])).SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup) :
    False := by
  have evaluated := valid (orderedPairSeparator first second)
  change
    SemigroupBasis.Generated.Catalogue.S5_84.mul
        (orderedPairSeparator first second first)
        (orderedPairSeparator first second second) =
      SemigroupBasis.Generated.Catalogue.S5_84.mul
        (orderedPairSeparator first second second)
        (orderedPairSeparator first second first) at evaluated
  simp [orderedPairSeparator, Ne.symm different,
    SemigroupBasis.Generated.Catalogue.S5_84.mul] at evaluated

private theorem quadraticWordsEqual
    (first second third fourth : Nat)
    (permutation : [first, second].Perm [third, fourth])
    (valid :
      (Identity.mk (word first [second])
        (word third [fourth])).SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup) :
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
        SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup) :
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

/-- Independent unrestricted completeness of the exact six-law survivor. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives targetBasis identity.lhs identity.rhs := by
  have canonicalValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup :=
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
      SemigroupBasis.CoRoots.S5_83Family.S5_84.basis_complete.2
        identity canonicalValid
    exact liftLowerDerivationOfLong lower long.1 long.2

/-- The surviving independently proved unrestricted owner intersection. -/
def intersectionBasis :
    IntersectionBasis
      Rank030.leftTable.semigroup
      Rank030.rightTable.semigroup
      Rank030.basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := derivesOfFactorValid

/-- Survivor normalization strictly after unrestricted completeness. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      Rank030.leftTable.semigroup
      Rank030.rightTable.semigroup
      Rank030.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- Exact surviving rank-030 representative endpoint. -/
theorem representative_basis_S6_2639 :
    BasisFor Rank030.S6_2639.table.semigroup Rank030.basis :=
  Rank030.S6_2639.representative_basis_of_normalizer intersectionNormalizer

/-- Literal reversed-basis opposite endpoint for the surviving class. -/
theorem opposite_basis_S6_2639 :
    BasisFor Rank030.S6_2639.table.semigroup.opposite
      (reversedBasis Rank030.basis) :=
  Rank030.S6_2639.opposite_basis_of_normalizer intersectionNormalizer

/-- Instantiate the attested sibling bridge only with the actual owner proof. -/
def recoveredIntersectionBasis :
    IntersectionBasis
      Rank030Pair004Recovered.leftTable.semigroup
      Rank030Pair004Recovered.rightTable.semigroup
      Rank030Pair004Recovered.basis :=
  Rank030Pair004SiblingTransport.recoveredIntersectionBasis intersectionBasis

/-- Recovered normalization strictly after actual transported completeness. -/
noncomputable def recoveredIntersectionNormalizer :
    IntersectionNormalizer
      Rank030Pair004Recovered.leftTable.semigroup
      Rank030Pair004Recovered.rightTable.semigroup
      Rank030Pair004Recovered.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    recoveredIntersectionBasis

/-- Exact explicitly attested collision-recovered representative endpoint. -/
theorem representative_basis_S6_2638 :
    BasisFor Rank030Pair004Recovered.S6_2638.table.semigroup
      Rank030Pair004Recovered.basis :=
  Rank030Pair004Recovered.S6_2638.representative_basis_of_normalizer
    recoveredIntersectionNormalizer

/-- Literal reversed-basis opposite endpoint for the recovered class. -/
theorem opposite_basis_S6_2638 :
    BasisFor Rank030Pair004Recovered.S6_2638.table.semigroup.opposite
      (reversedBasis Rank030Pair004Recovered.basis) :=
  Rank030Pair004Recovered.S6_2638.opposite_basis_of_normalizer
    recoveredIntersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS5_84
