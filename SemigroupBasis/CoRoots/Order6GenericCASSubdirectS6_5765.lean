import SemigroupBasis.Examples.CyclicThreeThree
import SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765
import SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_5765
import SemigroupBasis.Generated.S3_18
import SemigroupBasis.Generated.S4_11

namespace SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_5765

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev rootBasis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.basis
private abbrev rootSemigroup : Semigroup (Fin 6) :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.oppositeTable.semigroup
private abbrev factorPair :=
  SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_5765.subdirectPair

private def instantiateTwoWords
    (first second : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | n + 2 => Word.singleton (n + 2)

private def instantiateFourWords
    (first second third fourth : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | n + 4 => Word.singleton (n + 4)

private theorem rootLaw0 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.law0.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.law0.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.basis]

private theorem rootLaw1 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.law1.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.law1.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.basis]

private theorem rootLaw4 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.law4.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.law4.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.basis]

private theorem derivesCommutativity (left right : Word Nat) :
    Derives rootBasis (left ++ right) (right ++ left) := by
  have substituted :=
    Derives.subst rootLaw0 (instantiateTwoWords left right)
  simpa [SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.law0,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton] using
      substituted

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {leftHead rightHead : Nat} {leftTail rightTail : List Nat} :
      Derives rootBasis
          (wordOfCons leftHead leftTail)
          (wordOfCons rightHead rightTail) →
        ListDerives
          (leftHead :: leftTail) (rightHead :: rightTail)

private theorem listDerives_of_perm {source target : List Nat}
    (permutation : source.Perm target) : ListDerives source target := by
  induction permutation with
  | nil =>
      exact ListDerives.empty
  | cons head _ inductionHypothesis =>
      cases inductionHypothesis with
      | empty =>
          exact ListDerives.words (Derives.refl _)
      | words derivation =>
          exact ListDerives.words <| by
            simpa [wordOfCons, Word.singleton, Word.append] using
              Derives.prepend (Word.singleton head) derivation
  | swap first second suffix =>
      exact ListDerives.words <| by
        cases suffix with
        | nil =>
            simpa [wordOfCons, Word.singleton, Word.append] using
              derivesCommutativity
                (Word.singleton second) (Word.singleton first)
        | cons next rest =>
            have swapped :=
              Derives.appendRight
                (derivesCommutativity
                  (Word.singleton second) (Word.singleton first))
                (wordOfCons next rest)
            simpa [wordOfCons, Word.singleton, Word.append,
              Word.append_assoc] using swapped
  | trans _ _ firstProof secondProof =>
      cases firstProof with
      | empty =>
          cases secondProof
          exact ListDerives.empty
      | words firstDerivation =>
          cases secondProof with
          | words secondDerivation =>
              exact ListDerives.words
                (Derives.trans firstDerivation secondDerivation)

private theorem derivesPermutation (left right : Word Nat)
    (permutation : left.toList.Perm right.toList) :
    Derives rootBasis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          cases listDerives_of_perm permutation with
          | words derivation => exact derivation

/-- Laws 4 and 1 first append a cube of the fourth factor and then replace
that cube by a cube of an arbitrary word. -/
private theorem derivesFourFactorCubeExpansion
    (first second third fourth cube : Word Nat) :
    Derives rootBasis
      (((first ++ second) ++ third) ++ fourth)
      ((((((first ++ second) ++ third) ++ fourth) ++ cube) ++ cube) ++ cube) := by
  have appendFourthCube :=
    Derives.subst rootLaw4
      (instantiateFourWords first second third fourth)
  have replaceFourthCube :=
    Derives.subst rootLaw1 (instantiateTwoWords fourth cube)
  exact Derives.trans
    (by
      simpa [SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.law4,
        instantiateFourWords, Word.bind, Word.append, Word.singleton,
        Word.append_assoc] using appendFourthCube)
    (by
      simpa [SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.law1,
        instantiateTwoWords, Word.bind, Word.append, Word.singleton,
        Word.append_assoc] using
          Derives.prepend ((first ++ second) ++ third) replaceFourthCube)

private theorem word_eq_four_factors
    (word : Word Nat) (long : 4 ≤ word.toList.length) :
    ∃ first second third fourth,
      word = (((first ++ second) ++ third) ++ fourth) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at long
      | cons second rest =>
          cases rest with
          | nil =>
              simp [Word.toList] at long
          | cons third more =>
              cases more with
              | nil =>
                  simp [Word.toList] at long
              | cons fourth remaining =>
                  refine ⟨Word.singleton head, Word.singleton second,
                    Word.singleton third, wordOfCons fourth remaining, ?_⟩
                  apply Word.toList_injective
                  simp [wordOfCons, Word.singleton, Word.append,
                    Word.toList]

private theorem derivesLongCubeExpansion
    (word cube : Word Nat) (long : 4 ≤ word.toList.length) :
    Derives rootBasis word
      (word ++ ((cube ++ cube) ++ cube)) := by
  obtain ⟨first, second, third, fourth, rfl⟩ :=
    word_eq_four_factors word long
  simpa [Word.append_assoc] using
    derivesFourFactorCubeExpansion first second third fourth cube

/-- The `C(3,3)` cube cancellation law is available behind any nonempty
context word. Its reverse is obtained by law 4, law 1, and a commutation. -/
private theorem derivesContextualCubeCancellation
    (contextWord cube first second third : Word Nat) :
    Derives rootBasis
      (contextWord ++ (((((cube ++ cube) ++ cube) ++ first) ++ second) ++ third))
      (contextWord ++ ((first ++ second) ++ third)) := by
  have expand :=
    derivesFourFactorCubeExpansion contextWord first second third cube
  have moveCube :=
    derivesCommutativity ((first ++ second) ++ third)
      ((cube ++ cube) ++ cube)
  apply Derives.symm
  exact Derives.trans
    (by simpa [Word.append_assoc] using expand)
    (by
      simpa [Word.append_assoc] using
        Derives.prepend contextWord moveCube)

private theorem bind_append (left right : Word Nat)
    (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat)
    (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Replay a `C(3,3)` derivation behind one fixed nonempty context word. That
word supplies the fourth factor needed by laws 4 and 1 whenever the source proof
uses cube cancellation. -/
private theorem derivesCyclicThreeThreeBehind
    {left right : Word Nat}
    (derivation : Derives cyclicThreeThreeBasis left right)
    (contextWord : Word Nat) (substitution : Nat → Word Nat) :
    Derives rootBasis
      (contextWord ++ left.bind substitution)
      (contextWord ++ right.bind substitution) := by
  induction derivation generalizing contextWord substitution with
  | fromBasis member =>
      simp only [cyclicThreeThreeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · have commute :=
          derivesCommutativity (substitution 0) (substitution 1)
        simpa [cyclicThreeThreeCommutativityLaw,
          cyclicThreeThreeXY, cyclicThreeThreeYX, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
            Derives.prepend contextWord commute
      · simpa [cyclicThreeThreeLongCancellationLaw,
          cyclicThreeThreeXXXYZT, cyclicThreeThreeYZT, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
            derivesContextualCubeCancellation contextWord
              (substitution 0) (substitution 1)
              (substitution 2) (substitution 3)
  | refl =>
      exact Derives.refl _
  | symm _ inductionHypothesis =>
      exact Derives.symm (inductionHypothesis contextWord substitution)
  | trans _ _ firstHypothesis secondHypothesis =>
      exact Derives.trans
        (firstHypothesis contextWord substitution)
        (secondHypothesis contextWord substitution)
  | prepend added _ inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        inductionHypothesis
          (contextWord ++ added.bind substitution) substitution
  | appendRight _ added inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (inductionHypothesis contextWord substitution)
          (added.bind substitution)
  | subst _ firstSubstitution inductionHypothesis =>
      simpa [bind_bind] using
        inductionHypothesis contextWord
          (fun letter => (firstSubstitution letter).bind substitution)

private def marker : Word Nat := Word.singleton 0
private def markerSquare : Word Nat := marker ++ marker
private def markerCube : Word Nat := markerSquare ++ marker

/-- In the length-at-least-four region, the root laws replay the complete
modulo-three normal form while keeping every intermediate word in that region. -/
private theorem derivesLongModThree
    (left right : Word Nat)
    (leftLong : 4 ≤ left.toList.length)
    (rightLong : 4 ≤ right.toList.length)
    (modEq : ∀ tested,
      left.toList.count tested % 3 =
        right.toList.count tested % 3) :
    Derives rootBasis left right := by
  have expandLeft := derivesLongCubeExpansion left marker leftLong
  have expandRight := derivesLongCubeExpansion right marker rightLong
  have arrangeLeft :
      Derives rootBasis
        (left ++ markerCube)
        (marker ++ (markerSquare ++ left)) := by
    simpa [markerCube, markerSquare, Word.append_assoc] using
      derivesCommutativity left markerCube
  have arrangeRight :
      Derives rootBasis
        (right ++ markerCube)
        (marker ++ (markerSquare ++ right)) := by
    simpa [markerCube, markerSquare, Word.append_assoc] using
      derivesCommutativity right markerCube
  have markerSquareLength : markerSquare.toList.length = 2 := by
    rfl
  have leftSuffixLong :
      3 ≤ (markerSquare ++ left).toList.length := by
    rw [Word.toList_append, List.length_append, markerSquareLength]
    omega
  have rightSuffixLong :
      3 ≤ (markerSquare ++ right).toList.length := by
    rw [Word.toList_append, List.length_append, markerSquareLength]
    omega
  have suffixModEq : ∀ tested,
      (markerSquare ++ left).toList.count tested % 3 =
        (markerSquare ++ right).toList.count tested % 3 := by
    intro tested
    simp only [Word.toList_append, List.count_append]
    have countsMod := modEq tested
    omega
  have suffixDerivation :=
    cyclicThreeThreeDerivesLongModThree
      (markerSquare ++ left) (markerSquare ++ right)
      leftSuffixLong rightSuffixLong suffixModEq
  have lifted :
      Derives rootBasis
        (marker ++ (markerSquare ++ left))
        (marker ++ (markerSquare ++ right)) := by
    simpa [bind_singleton] using
      derivesCyclicThreeThreeBehind
        suffixDerivation marker Word.singleton
  exact Derives.trans expandLeft <|
    Derives.trans arrangeLeft <|
    Derives.trans lifted <|
    Derives.trans (Derives.symm arrangeRight)
      (Derives.symm expandRight)

/- The following local evaluator is deliberately kept in this CoRoot. It
extracts only the C(4,1) length strata and the length-three support test needed
for this intersection proof. -/

private def rightState (length : Nat) : Fin 4 :=
  if length = 1 then 3
  else if length = 2 then 1
  else if length = 3 then 2
  else 0

private theorem rightMul_state_one
    (length : Nat) (positive : 0 < length) :
    cyclicFourOneMul (rightState length) (rightState 1) =
      rightState (length + 1) := by
  by_cases one : length = 1
  · subst length
    rfl
  · by_cases two : length = 2
    · subst length
      rfl
    · by_cases three : length = 3
      · subst length
        rfl
      · have zero : length ≠ 0 := by omega
        have nextOne : length + 1 ≠ 1 := by omega
        have nextTwo : length + 1 ≠ 2 := by omega
        have nextThree : length + 1 ≠ 3 := by omega
        apply Fin.ext
        simp [rightState, cyclicFourOneMul, zero, one, two, three,
          nextOne, nextTwo, nextThree]

private theorem rightMul_state_two
    (length : Nat) (positive : 0 < length) :
    cyclicFourOneMul (rightState length) (rightState 2) =
      rightState (length + 2) := by
  by_cases one : length = 1
  · subst length
    rfl
  · by_cases two : length = 2
    · subst length
      rfl
    · by_cases three : length = 3
      · subst length
        rfl
      · have zero : length ≠ 0 := by omega
        have nextOne : length + 2 ≠ 1 := by omega
        have nextTwo : length + 2 ≠ 2 := by omega
        have nextThree : length + 2 ≠ 3 := by omega
        apply Fin.ext
        simp [rightState, cyclicFourOneMul, zero, one, two, three,
          nextOne, nextTwo, nextThree]

private def rightWeightedValuation
    (weight : Nat → Nat) : Nat → Fin 4 :=
  fun letter => rightState (weight letter)

private def rightWeightSum
    (weight : Nat → Nat) : List Nat → Nat
  | [] => 0
  | letter :: rest => weight letter + rightWeightSum weight rest

private theorem rightFold_weighted
    (weight : Nat → Nat)
    (oneOrTwo : ∀ letter, weight letter = 1 ∨ weight letter = 2)
    (letters : List Nat) (accumulator : Nat)
    (positive : 0 < accumulator) :
    letters.foldl
        (fun current letter =>
          cyclicFourOneMul current (rightWeightedValuation weight letter))
        (rightState accumulator) =
      rightState (accumulator + rightWeightSum weight letters) := by
  induction letters generalizing accumulator with
  | nil =>
      simp [rightWeightSum]
  | cons letter rest inductionHypothesis =>
      simp only [List.foldl_cons]
      rcases oneOrTwo letter with one | two
      · rw [show rightWeightedValuation weight letter =
          rightState 1 by simp [rightWeightedValuation, one]]
        rw [rightMul_state_one accumulator positive]
        rw [inductionHypothesis (accumulator + 1) (by omega)]
        simp [rightWeightSum, one]
        congr 1
        omega
      · rw [show rightWeightedValuation weight letter =
          rightState 2 by simp [rightWeightedValuation, two]]
        rw [rightMul_state_two accumulator positive]
        rw [inductionHypothesis (accumulator + 2) (by omega)]
        simp [rightWeightSum, two]
        congr 1
        omega

private theorem rightEval_weighted
    (weight : Nat → Nat)
    (oneOrTwo : ∀ letter, weight letter = 1 ∨ weight letter = 2)
    (word : Word Nat) :
    cyclicFourOne.semigroup.eval (rightWeightedValuation weight) word =
      rightState (rightWeightSum weight word.toList) := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current letter =>
              cyclicFourOneMul current
                (rightWeightedValuation weight letter))
            (rightWeightedValuation weight head) =
          rightState (rightWeightSum weight (head :: tail))
      rw [show rightWeightedValuation weight head =
          rightState (weight head) by rfl]
      have headPositive : 0 < weight head := by
        rcases oneOrTwo head with one | two <;> omega
      rw [rightFold_weighted weight oneOrTwo tail
        (weight head) headPositive]
      simp [rightWeightSum]

private def unitWeight : Nat → Nat := fun _ => 1

private def doubledWeight (tested : Nat) : Nat → Nat :=
  fun letter => if letter = tested then 2 else 1

private theorem rightWeightSum_unit (letters : List Nat) :
    rightWeightSum unitWeight letters = letters.length := by
  induction letters with
  | nil => rfl
  | cons letter rest inductionHypothesis =>
      simp [rightWeightSum, unitWeight, inductionHypothesis]
      omega

private theorem rightWeightSum_doubled
    (tested : Nat) (letters : List Nat) :
    rightWeightSum (doubledWeight tested) letters =
      letters.length + letters.count tested := by
  induction letters with
  | nil =>
      simp [rightWeightSum]
  | cons letter rest inductionHypothesis =>
      by_cases selected : letter = tested
      · subst letter
        simp [rightWeightSum, doubledWeight, inductionHypothesis]
        omega
      · simp [rightWeightSum, doubledWeight, selected,
          inductionHypothesis]
        omega

private theorem rightEval_unit (word : Word Nat) :
    cyclicFourOne.semigroup.eval
        (rightWeightedValuation unitWeight) word =
      rightState word.toList.length := by
  rw [rightEval_weighted unitWeight (by
    intro letter
    exact Or.inl rfl)]
  rw [rightWeightSum_unit]

private theorem rightEval_doubled (tested : Nat) (word : Word Nat) :
    cyclicFourOne.semigroup.eval
        (rightWeightedValuation (doubledWeight tested)) word =
      rightState (word.toList.length + word.toList.count tested) := by
  rw [rightEval_weighted (doubledWeight tested) (by
    intro letter
    by_cases selected : letter = tested
    · exact Or.inr (by simp [doubledWeight, selected])
    · exact Or.inl (by simp [doubledWeight, selected]))]
  rw [rightWeightSum_doubled]

private theorem rightState_eq_one
    {length : Nat} (positive : 0 < length) :
    rightState length = rightState 1 ↔ length = 1 := by
  constructor
  · intro equality
    by_cases one : length = 1
    · exact one
    · by_cases two : length = 2
      · subst length
        simp [rightState] at equality
      · by_cases three : length = 3
        · subst length
          simp [rightState] at equality
        · simp [rightState, one, two, three] at equality
  · intro equality
    rw [equality]

private theorem rightState_eq_two
    {length : Nat} (positive : 0 < length) :
    rightState length = rightState 2 ↔ length = 2 := by
  constructor
  · intro equality
    by_cases one : length = 1
    · subst length
      simp [rightState] at equality
    · by_cases two : length = 2
      · exact two
      · by_cases three : length = 3
        · subst length
          simp [rightState] at equality
        · simp [rightState, one, two, three] at equality
  · intro equality
    rw [equality]

private theorem rightState_eq_three
    {length : Nat} (positive : 0 < length) :
    rightState length = rightState 3 ↔ length = 3 := by
  constructor
  · intro equality
    by_cases one : length = 1
    · subst length
      simp [rightState] at equality
    · by_cases two : length = 2
      · subst length
        simp [rightState] at equality
      · by_cases three : length = 3
        · exact three
        · simp [rightState, one, two, three] at equality
  · intro equality
    rw [equality]

private theorem rightState_three_add_zero_iff (count : Nat) :
    rightState (3 + count) = rightState 3 ↔ count = 0 := by
  by_cases zero : count = 0
  · subst count
    simp
  · have positive : 0 < count := Nat.pos_of_ne_zero zero
    have notOne : 3 + count ≠ 1 := by omega
    have notTwo : 3 + count ≠ 2 := by omega
    have notThree : 3 + count ≠ 3 := by omega
    simp [rightState, notOne, notTwo, notThree, zero]

/-- A valid C(4,1) identity stays in one of four local length strata:
exactly one, exactly two, exactly three, or at least four. -/
private theorem rightLengthShape
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy cyclicFourOne.semigroup) :
    (identity.lhs.toList.length = 1 ∧
        identity.rhs.toList.length = 1) ∨
      (identity.lhs.toList.length = 2 ∧
        identity.rhs.toList.length = 2) ∨
      (identity.lhs.toList.length = 3 ∧
        identity.rhs.toList.length = 3) ∨
      (4 ≤ identity.lhs.toList.length ∧
        4 ≤ identity.rhs.toList.length) := by
  have stateEq :
      rightState identity.lhs.toList.length =
        rightState identity.rhs.toList.length := by
    have evaluated := valid (rightWeightedValuation unitWeight)
    rw [rightEval_unit, rightEval_unit] at evaluated
    exact evaluated
  have lhsPositive : 0 < identity.lhs.toList.length := by
    cases identity.lhs
    simp [Word.toList]
  have rhsPositive : 0 < identity.rhs.toList.length := by
    cases identity.rhs
    simp [Word.toList]
  by_cases lhsOne : identity.lhs.toList.length = 1
  · have rhsOne : identity.rhs.toList.length = 1 := by
      apply (rightState_eq_one rhsPositive).mp
      rw [← stateEq, lhsOne]
    exact Or.inl ⟨lhsOne, rhsOne⟩
  · by_cases lhsTwo : identity.lhs.toList.length = 2
    · have rhsTwo : identity.rhs.toList.length = 2 := by
        apply (rightState_eq_two rhsPositive).mp
        rw [← stateEq, lhsTwo]
      exact Or.inr <| Or.inl ⟨lhsTwo, rhsTwo⟩
    · by_cases lhsThree : identity.lhs.toList.length = 3
      · have rhsThree : identity.rhs.toList.length = 3 := by
          apply (rightState_eq_three rhsPositive).mp
          rw [← stateEq, lhsThree]
        exact Or.inr <| Or.inr <| Or.inl ⟨lhsThree, rhsThree⟩
      · have lhsLong : 4 ≤ identity.lhs.toList.length := by omega
        have rhsNotOne : identity.rhs.toList.length ≠ 1 := by
          intro rhsOne
          have lhsStateOne :
              rightState identity.lhs.toList.length = rightState 1 := by
            rw [stateEq, rhsOne]
          exact lhsOne <| (rightState_eq_one lhsPositive).mp lhsStateOne
        have rhsNotTwo : identity.rhs.toList.length ≠ 2 := by
          intro rhsTwo
          have lhsStateTwo :
              rightState identity.lhs.toList.length = rightState 2 := by
            rw [stateEq, rhsTwo]
          exact lhsTwo <| (rightState_eq_two lhsPositive).mp lhsStateTwo
        have rhsNotThree : identity.rhs.toList.length ≠ 3 := by
          intro rhsThree
          have lhsStateThree :
              rightState identity.lhs.toList.length = rightState 3 := by
            rw [stateEq, rhsThree]
          exact lhsThree <|
            (rightState_eq_three lhsPositive).mp lhsStateThree
        have rhsLong : 4 ≤ identity.rhs.toList.length := by omega
        exact Or.inr <| Or.inr <| Or.inr ⟨lhsLong, rhsLong⟩

private theorem rightCountZeroEq_of_length_three
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy cyclicFourOne.semigroup)
    (lhsThree : identity.lhs.toList.length = 3)
    (rhsThree : identity.rhs.toList.length = 3) :
    ∀ tested,
      identity.lhs.toList.count tested = 0 ↔
        identity.rhs.toList.count tested = 0 := by
  intro tested
  have weightedState :
      rightState
          (identity.lhs.toList.length +
            identity.lhs.toList.count tested) =
        rightState
          (identity.rhs.toList.length +
            identity.rhs.toList.count tested) := by
    have evaluated :=
      valid (rightWeightedValuation (doubledWeight tested))
    rw [rightEval_doubled, rightEval_doubled] at evaluated
    exact evaluated
  constructor
  · intro lhsZero
    apply (rightState_three_add_zero_iff
      (identity.rhs.toList.count tested)).mp
    simpa [lhsThree, rhsThree, lhsZero] using weightedState.symm
  · intro rhsZero
    apply (rightState_three_add_zero_iff
      (identity.lhs.toList.count tested)).mp
    simpa [lhsThree, rhsThree, rhsZero] using weightedState

private theorem catalogueS3_18_table_eq_cyclicThree :
    SemigroupBasis.Generated.Catalogue.S3_18.table = cyclicThree := by
  calc
    SemigroupBasis.Generated.Catalogue.S3_18.table =
        SemigroupBasis.Generated.S3_18.table :=
      SemigroupBasis.Generated.S3_18.table_eq_canonical_catalogue.symm
    _ = cyclicThree :=
      SemigroupBasis.Generated.S3_18.table_eq_catalogue_model

private theorem catalogueS4_11_table_eq_cyclicFourOne :
    SemigroupBasis.Generated.Catalogue.S4_11.table = cyclicFourOne := by
  calc
    SemigroupBasis.Generated.Catalogue.S4_11.table =
        SemigroupBasis.Generated.S4_11.table :=
      SemigroupBasis.Generated.S4_11.table_eq_canonical_catalogue.symm
    _ = cyclicFourOne := rfl

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
        SemigroupBasis.Generated.Catalogue.S4_11.table.semigroup) :
    Derives rootBasis identity.lhs identity.rhs := by
  have leftValid' : identity.SatisfiedBy cyclicThree.semigroup :=
    satisfiedBy_of_table_eq catalogueS3_18_table_eq_cyclicThree
      identity leftValid
  have rightValid' : identity.SatisfiedBy cyclicFourOne.semigroup :=
    satisfiedBy_of_table_eq catalogueS4_11_table_eq_cyclicFourOne
      identity rightValid
  have modEq : ∀ tested,
      identity.lhs.toList.count tested % 3 =
        identity.rhs.toList.count tested % 3 :=
    cyclicThreeValid_mod_eq identity leftValid'
  rcases rightLengthShape identity rightValid' with
    ⟨lhsOne, rhsOne⟩ |
    ⟨lhsTwo, rhsTwo⟩ |
    ⟨lhsThree, rhsThree⟩ |
    ⟨lhsLong, rhsLong⟩
  · have countEq : ∀ tested,
        identity.lhs.toList.count tested =
          identity.rhs.toList.count tested := by
      intro tested
      have lhsBound :=
        List.count_le_length
          (a := tested) (l := identity.lhs.toList)
      have rhsBound :=
        List.count_le_length
          (a := tested) (l := identity.rhs.toList)
      have residue := modEq tested
      omega
    exact derivesPermutation identity.lhs identity.rhs <|
      List.perm_iff_count.mpr countEq
  · have countEq : ∀ tested,
        identity.lhs.toList.count tested =
          identity.rhs.toList.count tested := by
      intro tested
      have lhsBound :=
        List.count_le_length
          (a := tested) (l := identity.lhs.toList)
      have rhsBound :=
        List.count_le_length
          (a := tested) (l := identity.rhs.toList)
      have residue := modEq tested
      omega
    exact derivesPermutation identity.lhs identity.rhs <|
      List.perm_iff_count.mpr countEq
  · have countZeroEq :=
      rightCountZeroEq_of_length_three identity rightValid'
        lhsThree rhsThree
    have countEq : ∀ tested,
        identity.lhs.toList.count tested =
          identity.rhs.toList.count tested := by
      intro tested
      have lhsBound :=
        List.count_le_length
          (a := tested) (l := identity.lhs.toList)
      have rhsBound :=
        List.count_le_length
          (a := tested) (l := identity.rhs.toList)
      have residue := modEq tested
      have zeroEq := countZeroEq tested
      omega
    exact derivesPermutation identity.lhs identity.rhs <|
      List.perm_iff_count.mpr countEq
  · exact derivesLongModThree identity.lhs identity.rhs
      lhsLong rhsLong modEq

private theorem leftFactorModels :
    Models
      SemigroupBasis.Generated.Catalogue.S3_18.table.semigroup
      rootBasis := by
  intro identity member
  exact factorPair.left.pushforwardIdentity identity
    (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.models
      identity member)

private theorem rightFactorModels :
    Models
      SemigroupBasis.Generated.Catalogue.S4_11.table.semigroup
      rootBasis := by
  intro identity member
  exact factorPair.right.pushforwardIdentity identity
    (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5765.models
      identity member)

/-- Exact unconditional basis endpoint for the mixed generic-CAS root
`S6_5765`. -/
theorem basisFor : BasisFor rootSemigroup rootBasis :=
  (IntersectionBasis.mk leftFactorModels rightFactorModels
    factorIntersectionComplete).basisFor factorPair

end SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_5765
