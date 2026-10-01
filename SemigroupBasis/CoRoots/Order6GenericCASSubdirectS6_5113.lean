import SemigroupBasis.CoRoots.Order6GenericCASShortTwo
import SemigroupBasis.CoRoots.S4_37
import SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113
import SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_5113

namespace SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_5113

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev rootBasis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.basis
private abbrev rootSemigroup : Semigroup (Fin 6) :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.oppositeTable.semigroup
private abbrev factorPair :=
  SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_5113.subdirectPair

private def instantiateTwoWords
    (first second : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | index + 2 => Word.singleton (index + 2)

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | index + 3 => Word.singleton (index + 3)

private theorem rootLaw0 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law0.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law0.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.basis]

private theorem rootLaw6 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law6.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law6.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.basis]

private theorem rootLaw7 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law7.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law7.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.basis]

private theorem derivesCommutativity (left right : Word Nat) :
    Derives rootBasis (left ++ right) (right ++ left) := by
  have substituted :=
    Derives.subst rootLaw0 (instantiateTwoWords left right)
  simpa [SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law0,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton] using
      substituted

private theorem derivesPermutation (left right : Word Nat)
    (permutation : left.toList.Perm right.toList) :
    Derives rootBasis left right :=
  SemigroupBasis.CoRoots.Order6GenericCASShortTwo.derivesPermutation
    derivesCommutativity left right permutation

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private def fourthPower (word : Word Nat) : Word Nat :=
  ((word ++ word) ++ word) ++ word

/-- Add a fourth-power block of the leading letter to any word of length at
least three. -/
private theorem derivesLeadingFourthExpansion
    (word : Word Nat) (long : 3 ≤ word.toList.length) :
    Derives rootBasis word
      (fourthPower (Word.singleton word.head) ++ word) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons second rest =>
          cases rest with
          | nil => simp [Word.toList] at long
          | cons third suffix =>
              have expanded :=
                Derives.subst rootLaw6 <|
                  instantiateThreeWords
                    (Word.singleton head)
                    (Word.singleton second)
                    (wordOfCons third suffix)
              simpa [SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law6,
                instantiateThreeWords, fourthPower, wordOfCons,
                Word.bind, Word.append, Word.singleton,
                Word.append_assoc] using expanded

/-- In the long region, an arbitrary fourth-power block may be inserted.
The common-fourth law changes the leading block supplied by `law6` to the
requested variable. -/
private theorem derivesFourthExpansion
    (letter : Word Nat) (word : Word Nat)
    (long : 3 ≤ word.toList.length) :
    Derives rootBasis word (fourthPower letter ++ word) := by
  have leading := derivesLeadingFourthExpansion word long
  have common :=
    Derives.subst rootLaw7
      (instantiateTwoWords (Word.singleton word.head) letter)
  have replaced := Derives.appendRight common word
  exact leading.trans <| by
    simpa [SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.law7,
      instantiateTwoWords, fourthPower, Word.bind, Word.append,
      Word.singleton, Word.append_assoc] using replaced

private theorem bind_append
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem prefix_long_append
    (contextWord suffix : Word Nat)
    (long : 3 ≤ contextWord.toList.length) :
    3 ≤ (contextWord ++ suffix).toList.length := by
  rw [Word.toList_append, List.length_append]
  omega

/-- Replay a cyclic-four derivation after a fixed long prefix. The prefix
supplies the three-letter context that prevents cancellation from entering
the literal short-word region. -/
private theorem liftCyclicFour
    {left right : Word Nat}
    (derivation : Derives cyclicFourBasis left right)
    (contextWord : Word Nat)
    (contextLong : 3 ≤ contextWord.toList.length)
    (substitution : Nat → Word Nat) :
    Derives rootBasis
      (contextWord ++ left.bind substitution)
      (contextWord ++ right.bind substitution) := by
  induction derivation generalizing contextWord substitution with
  | fromBasis member =>
      simp only [cyclicFourBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · have commute :=
          derivesCommutativity (substitution 0) (substitution 1)
        simpa [cyclicFourCommutativityLaw, cyclicFourXY,
          cyclicFourYX, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using Derives.prepend contextWord commute
      · let power := fourthPower (substitution 0)
        let body := contextWord ++ substitution 1
        have enter :=
          Derives.appendRight
            (derivesCommutativity contextWord power) (substitution 1)
        have bodyLong : 3 ≤ body.toList.length :=
          prefix_long_append contextWord (substitution 1) contextLong
        have remove :=
          Derives.symm <|
            derivesFourthExpansion (substitution 0) body bodyLong
        have remove' :
            Derives rootBasis
              ((power ++ contextWord) ++ substitution 1)
              (contextWord ++ substitution 1) := by
          simpa [power, body, Word.append_assoc] using remove
        have combined := enter.trans remove'
        simpa [cyclicFourCancellationLaw, cyclicFourXXXXY,
          cyclicFourY, power, fourthPower, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using combined
  | refl =>
      exact Derives.refl _
  | symm _ inductionHypothesis =>
      exact Derives.symm
        (inductionHypothesis contextWord contextLong substitution)
  | trans _ _ first second =>
      exact Derives.trans
        (first contextWord contextLong substitution)
        (second contextWord contextLong substitution)
  | prepend stem _ inductionHypothesis =>
      have extendedLong :
          3 ≤ (contextWord ++ stem.bind substitution).toList.length :=
        prefix_long_append contextWord (stem.bind substitution) contextLong
      simpa [bind_append, Word.append_assoc] using
        inductionHypothesis
          (contextWord ++ stem.bind substitution) extendedLong substitution
  | appendRight _ suffix inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (inductionHypothesis contextWord contextLong substitution)
          (suffix.bind substitution)
  | subst _ first inductionHypothesis =>
      simpa [bind_bind] using
        inductionHypothesis contextWord contextLong
          (fun letter => (first letter).bind substitution)

private def marker : Word Nat := Word.singleton 0
private def longPrefix : Word Nat := fourthPower marker

private theorem longPrefix_long : 3 ≤ longPrefix.toList.length := by
  decide

private theorem derivesLongFromRightFactor
    (identity : Identity Nat)
    (leftLong : 3 ≤ identity.lhs.toList.length)
    (rightLong : 3 ≤ identity.rhs.toList.length)
    (rightValid : identity.SatisfiedBy
      SemigroupBasis.CoRoots.S4_37.table.semigroup) :
    Derives rootBasis identity.lhs identity.rhs := by
  have cyclicDerivation :
      Derives cyclicFourBasis identity.lhs identity.rhs :=
    SemigroupBasis.CoRoots.S4_37.basis_complete.2 identity rightValid
  have leftExpanded :=
    derivesFourthExpansion marker identity.lhs leftLong
  have rightExpanded :=
    derivesFourthExpansion marker identity.rhs rightLong
  have lifted :=
    liftCyclicFour cyclicDerivation longPrefix longPrefix_long
      Word.singleton
  rw [bind_singleton, bind_singleton] at lifted
  exact leftExpanded.trans <|
    lifted.trans rightExpanded.symm

private theorem completeFromFactors
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_5113.leftFactor)
    (rightValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_5113.rightFactor) :
    Derives rootBasis identity.lhs identity.rhs := by
  rcases
      SemigroupBasis.CoRoots.Order6GenericCASShortTwo.classifyValidIdentity
        identity leftValid with
    equal | ⟨leftTwo, rightTwo, permutation⟩ |
      ⟨leftLong, rightLong⟩
  · rw [equal]
    exact Derives.refl _
  · exact derivesPermutation identity.lhs identity.rhs permutation
  · exact derivesLongFromRightFactor
      identity leftLong rightLong rightValid

/-- Unconditional complete basis theorem for the exact opposite table and
displayed generic-CAS basis of `S6_5113`. -/
theorem basisFor : BasisFor rootSemigroup rootBasis := by
  refine ⟨
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5113.models,
    ?_⟩
  intro identity valid
  have factorValid := (factorPair.satisfiedBy_iff identity).mp valid
  exact completeFromFactors identity factorValid.1 factorValid.2

end SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_5113
