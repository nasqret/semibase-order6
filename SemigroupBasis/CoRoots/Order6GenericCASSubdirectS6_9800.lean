import SemigroupBasis.CoRoots.Order6GenericCASShortTwo
import SemigroupBasis.Generated.Order6GenericCASRootData.S6_9800
import SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_9800
import SemigroupBasis.Generated.S4_124

namespace SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_9800

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev rootBasis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_9800.basis
private abbrev rootSemigroup : Semigroup (Fin 6) :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_9800.oppositeTable.semigroup
private abbrev factorPair :=
  SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_9800.subdirectPair

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
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_9800.law0.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_9800.law0.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_9800.basis]

private theorem rootLaw4 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_9800.law4.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_9800.law4.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_9800.basis]

private theorem derivesCommutativity (left right : Word Nat) :
    Derives rootBasis (left ++ right) (right ++ left) := by
  have substituted :=
    Derives.subst rootLaw0 (instantiateTwoWords left right)
  simpa [SemigroupBasis.Generated.Order6GenericCASRootData.S6_9800.law0,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton] using
      substituted

private theorem derivesPermutation (left right : Word Nat)
    (permutation : left.toList.Perm right.toList) :
    Derives rootBasis left right :=
  SemigroupBasis.CoRoots.Order6GenericCASShortTwo.derivesPermutation
    derivesCommutativity left right permutation

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private def triplePower (word : Word Nat) : Word Nat :=
  (word ++ word) ++ word

private def fourthPower (word : Word Nat) : Word Nat :=
  triplePower word ++ word

private def frontedWord (letter : Nat) (word : Word Nat) : Word Nat :=
  wordOfCons letter (word.toList.erase letter)

private theorem word_perm_frontedWord
    (letter : Nat) (word : Word Nat)
    (present : letter ∈ word.toList) :
    word.toList.Perm (frontedWord letter word).toList := by
  simpa [frontedWord, wordOfCons, Word.toList] using
    List.perm_cons_erase present

/-- Add three copies of the first nonempty block while retaining two further
nonempty blocks. -/
private theorem derivesThreeBlockExpansion
    (first second third : Word Nat) :
    Derives rootBasis ((first ++ second) ++ third)
      (triplePower first ++ ((first ++ second) ++ third)) := by
  have expanded :=
    Derives.subst rootLaw4
      (instantiateThreeWords first second third)
  simpa [SemigroupBasis.Generated.Order6GenericCASRootData.S6_9800.law4,
    instantiateThreeWords, triplePower, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using expanded

/-- Add a triple of a supported variable to a long word. -/
private theorem derivesSupportedTripleExpansion
    (letter : Nat) (word : Word Nat)
    (present : letter ∈ word.toList)
    (long : 3 ≤ word.toList.length) :
    Derives rootBasis word
      (triplePower (Word.singleton letter) ++ word) := by
  have enter :=
    derivesPermutation word (frontedWord letter word)
      (word_perm_frontedWord letter word present)
  have erasedLength := List.length_erase_of_mem present
  have erasedLong : 2 ≤ (word.toList.erase letter).length := by
    omega
  cases erased : word.toList.erase letter with
  | nil => simp [erased] at erasedLong
  | cons first rest =>
      cases rest with
      | nil => simp [erased] at erasedLong
      | cons second suffix =>
          have expanded :=
            derivesThreeBlockExpansion
              (Word.singleton letter)
              (Word.singleton first)
              (wordOfCons second suffix)
          have prefixedEnter :=
            Derives.prepend
              (triplePower (Word.singleton letter)) enter
          have expanded' :
              Derives rootBasis
                (frontedWord letter word)
                (triplePower (Word.singleton letter) ++
                  frontedWord letter word) := by
            simpa [frontedWord, erased, wordOfCons, triplePower,
              Word.append, Word.singleton, Word.append_assoc] using
                expanded
          have exit' :
              Derives rootBasis
                (triplePower (Word.singleton letter) ++
                  frontedWord letter word)
                (triplePower (Word.singleton letter) ++ word) := by
            simpa [frontedWord, erased, wordOfCons,
              Word.append_assoc] using prefixedEnter.symm
          exact enter.trans (expanded'.trans exit')

/-- Add three copies of an arbitrary nonempty block after a prefix of length
at least two. This is the contextual replay of `x = xxxx`. -/
private theorem derivesBlockTripleExpansion
    (block contextWord : Word Nat)
    (contextLong : 2 ≤ contextWord.toList.length) :
    Derives rootBasis (contextWord ++ block)
      (contextWord ++ fourthPower block) := by
  cases contextWord with
  | mk head tail =>
      cases tail with
      | nil => simp [Word.toList] at contextLong
      | cons second rest =>
          let firstPrefix := Word.singleton head
          let secondPrefix := wordOfCons second rest
          have enter := derivesCommutativity
            (firstPrefix ++ secondPrefix) block
          have expanded :=
            derivesThreeBlockExpansion block firstPrefix secondPrefix
          have exit :=
            derivesCommutativity (fourthPower block)
              (firstPrefix ++ secondPrefix)
          have expanded' :
              Derives rootBasis
                (block ++ (firstPrefix ++ secondPrefix))
                (fourthPower block ++
                  (firstPrefix ++ secondPrefix)) := by
            simpa [fourthPower, Word.append_assoc] using expanded
          have combined := enter.trans (expanded'.trans exit)
          simpa [firstPrefix, secondPrefix, fourthPower,
            triplePower, wordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using combined

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

/-- Replay a positive-modulo-three derivation behind a long prefix. -/
private theorem liftPositiveModThree
    {left right : Word Nat}
    (derivation : Derives commutativePositiveModThreeBasis left right)
    (contextWord : Word Nat)
    (contextLong : 3 ≤ contextWord.toList.length)
    (substitution : Nat → Word Nat) :
    Derives rootBasis
      (contextWord ++ left.bind substitution)
      (contextWord ++ right.bind substitution) := by
  induction derivation generalizing contextWord substitution with
  | fromBasis member =>
      simp only [commutativePositiveModThreeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · have contextTwo : 2 ≤ contextWord.toList.length := by omega
        simpa [positiveModThreePowerLaw, positiveModThreeX,
          positiveModThreeXXXX, fourthPower, triplePower, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
            derivesBlockTripleExpansion
              (substitution 0) contextWord contextTwo
      · have commute :=
          derivesCommutativity (substitution 0) (substitution 1)
        simpa [positiveModThreeCommutativityLaw, positiveModThreeXY,
          positiveModThreeYX, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using Derives.prepend contextWord commute
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

private theorem generatedRightValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_9800.rightFactor) :
    identity.SatisfiedBy
      SemigroupBasis.Generated.S4_124.table.semigroup := by
  rw [SemigroupBasis.Generated.S4_124.table_eq_canonical_catalogue]
  exact valid

private theorem concreteRightValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_9800.rightFactor) :
    identity.SatisfiedBy commutativePositiveModThreeFour.semigroup := by
  rw [← SemigroupBasis.Generated.S4_124.table_eq_catalogue_model]
  exact generatedRightValid identity valid

private theorem derivesLongFromRightFactor
    (identity : Identity Nat)
    (leftLong : 3 ≤ identity.lhs.toList.length)
    (rightLong : 3 ≤ identity.rhs.toList.length)
    (rightValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_9800.rightFactor) :
    Derives rootBasis identity.lhs identity.rhs := by
  have concreteValid := concreteRightValid identity rightValid
  have support := positiveModThreeValid_support identity concreteValid
  let selected := identity.lhs.head
  have selectedLeft : selected ∈ identity.lhs.toList := by
    simp [selected, Word.toList]
  have selectedRight : selected ∈ identity.rhs.toList :=
    (support selected).mp selectedLeft
  have leftExpanded :=
    derivesSupportedTripleExpansion
      selected identity.lhs selectedLeft leftLong
  have rightExpanded :=
    derivesSupportedTripleExpansion
      selected identity.rhs selectedRight rightLong
  have positiveDerivation :
      Derives commutativePositiveModThreeBasis
        identity.lhs identity.rhs :=
    SemigroupBasis.Generated.S4_124.representative_basis.2
      identity (generatedRightValid identity rightValid)
  let contextWord := triplePower (Word.singleton selected)
  have contextLong : 3 ≤ contextWord.toList.length := by
    change 3 ≤ 3
    omega
  have lifted :=
    liftPositiveModThree positiveDerivation contextWord contextLong
      Word.singleton
  rw [bind_singleton, bind_singleton] at lifted
  exact leftExpanded.trans <|
    lifted.trans rightExpanded.symm

private theorem completeFromFactors
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_9800.leftFactor)
    (rightValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_9800.rightFactor) :
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
displayed generic-CAS basis of `S6_9800`. -/
theorem basisFor : BasisFor rootSemigroup rootBasis := by
  refine ⟨
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_9800.models,
    ?_⟩
  intro identity valid
  have factorValid := (factorPair.satisfiedBy_iff identity).mp valid
  exact completeFromFactors identity factorValid.1 factorValid.2

end SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_9800
