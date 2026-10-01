import SemigroupBasis.CoRoots.S5_216
import SemigroupBasis.Examples.CyclicFourOne
import SemigroupBasis.Examples.LeftZeroTwo
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S5_216

open SemigroupBasis
open SemigroupBasis.Examples
open DirectCompletenessArchitecture

/-- The zero-based copy `[0,1,2,3]` of `C_{4,1}` in `S5_216`. -/
def cyclicEmbedding :
    Embedding cyclicFourOne.semigroup table.semigroup where
  toFun := fun value =>
    if value.val = 0 then (0 : Fin 5)
    else if value.val = 1 then (1 : Fin 5)
    else if value.val = 2 then (2 : Fin 5)
    else (3 : Fin 5)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem cyclicEmbedding_outputs :
    cyclicEmbedding.toFun (0 : Fin 4) = (0 : Fin 5) ∧
      cyclicEmbedding.toFun (1 : Fin 4) = (1 : Fin 5) ∧
        cyclicEmbedding.toFun (2 : Fin 4) = (2 : Fin 5) ∧
          cyclicEmbedding.toFun (3 : Fin 4) = (3 : Fin 5) := by
  decide

/-- The zero-based copy `[0,4]` of the two-element left-zero semigroup. -/
def leftZeroEmbedding :
    Embedding leftZeroTwo.semigroup table.semigroup where
  toFun := fun value =>
    if value.val = 0 then (0 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem leftZeroEmbedding_outputs :
    leftZeroEmbedding.toFun (0 : Fin 2) = (0 : Fin 5) ∧
      leftZeroEmbedding.toFun (1 : Fin 2) = (4 : Fin 5) := by
  decide

theorem valid_cyclicFourOne
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy cyclicFourOne.semigroup :=
  cyclicEmbedding.pullback_identity identity valid

theorem valid_leftZeroTwo
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy leftZeroTwo.semigroup :=
  leftZeroEmbedding.pullback_identity identity valid

/-- The left-zero factor recovers the literal head variable. -/
theorem valid_head
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  have pulled := valid_leftZeroTwo identity valid
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 := fun letter =>
    if letter = identity.lhs.head then 0 else 1
  have evaluated := pulled valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm different] at evaluated

/-- The state of `g^n` in the cyclic factor, with `3` as generator. -/
private def cyclicState (n : Nat) : Fin 4 :=
  if n = 1 then 3
  else if n = 2 then 1
  else if n = 3 then 2
  else 0

private theorem cyclicMul_state_one
    (n : Nat) (positive : 0 < n) :
    cyclicFourOneMul (cyclicState n) (cyclicState 1) =
      cyclicState (n + 1) := by
  by_cases one : n = 1
  · subst n
    rfl
  · by_cases two : n = 2
    · subst n
      rfl
    · by_cases three : n = 3
      · subst n
        rfl
      · have zero : n ≠ 0 := by omega
        have nextOne : n + 1 ≠ 1 := by omega
        have nextTwo : n + 1 ≠ 2 := by omega
        have nextThree : n + 1 ≠ 3 := by omega
        apply Fin.ext
        simp [cyclicState, cyclicFourOneMul, zero, one, two, three,
          nextOne, nextTwo, nextThree]

private theorem cyclicMul_state_two
    (n : Nat) (positive : 0 < n) :
    cyclicFourOneMul (cyclicState n) (cyclicState 2) =
      cyclicState (n + 2) := by
  by_cases one : n = 1
  · subst n
    rfl
  · by_cases two : n = 2
    · subst n
      rfl
    · by_cases three : n = 3
      · subst n
        rfl
      · have zero : n ≠ 0 := by omega
        have nextOne : n + 2 ≠ 1 := by omega
        have nextTwo : n + 2 ≠ 2 := by omega
        have nextThree : n + 2 ≠ 3 := by omega
        apply Fin.ext
        simp [cyclicState, cyclicFourOneMul, zero, one, two, three,
          nextOne, nextTwo, nextThree]

private def weightedValuation (weight : Nat → Nat) : Nat → Fin 4 :=
  fun letter => cyclicState (weight letter)

private def weightSum (weight : Nat → Nat) : List Nat → Nat
  | [] => 0
  | letter :: rest => weight letter + weightSum weight rest

private theorem cyclicFold_weighted
    (weight : Nat → Nat)
    (oneOrTwo : ∀ letter, weight letter = 1 ∨ weight letter = 2)
    (letters : List Nat) (accumulator : Nat)
    (positive : 0 < accumulator) :
    letters.foldl
        (fun current letter =>
          cyclicFourOneMul current (weightedValuation weight letter))
        (cyclicState accumulator) =
      cyclicState (accumulator + weightSum weight letters) := by
  induction letters generalizing accumulator with
  | nil =>
      simp [weightSum]
  | cons letter rest ih =>
      simp only [List.foldl_cons]
      rcases oneOrTwo letter with weightOne | weightTwo
      · rw [show weightedValuation weight letter =
          cyclicState 1 by simp [weightedValuation, weightOne]]
        rw [cyclicMul_state_one accumulator positive]
        rw [ih (accumulator + 1) (by omega)]
        simp [weightSum, weightOne]
        congr 1
        omega
      · rw [show weightedValuation weight letter =
          cyclicState 2 by simp [weightedValuation, weightTwo]]
        rw [cyclicMul_state_two accumulator positive]
        rw [ih (accumulator + 2) (by omega)]
        simp [weightSum, weightTwo]
        congr 1
        omega

private theorem cyclicEval_weighted
    (weight : Nat → Nat)
    (oneOrTwo : ∀ letter, weight letter = 1 ∨ weight letter = 2)
    (word : Word Nat) :
    cyclicFourOne.semigroup.eval (weightedValuation weight) word =
      cyclicState (weightSum weight word.toList) := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current letter =>
              cyclicFourOneMul current (weightedValuation weight letter))
            (weightedValuation weight head) =
          cyclicState (weightSum weight (head :: tail))
      rw [show weightedValuation weight head =
          cyclicState (weight head) by rfl]
      have positive : 0 < weight head := by
        rcases oneOrTwo head with weightOne | weightTwo <;> omega
      rw [cyclicFold_weighted weight oneOrTwo tail
        (weight head) positive]
      simp [weightSum]

private def unitWeight : Nat → Nat := fun _ => 1

private def doubledWeight (tested : Nat) : Nat → Nat :=
  fun letter => if letter = tested then 2 else 1

private theorem weightSum_unit (letters : List Nat) :
    weightSum unitWeight letters = letters.length := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      simp [weightSum, unitWeight, ih]
      omega

private theorem weightSum_doubled
    (tested : Nat) (letters : List Nat) :
    weightSum (doubledWeight tested) letters =
      letters.length + letters.count tested := by
  induction letters with
  | nil =>
      simp [weightSum]
  | cons letter rest ih =>
      by_cases hit : letter = tested
      · subst letter
        simp [weightSum, doubledWeight, ih]
        omega
      · simp [weightSum, doubledWeight, hit, ih]
        omega

private theorem cyclicEval_unit (word : Word Nat) :
    cyclicFourOne.semigroup.eval (weightedValuation unitWeight) word =
      cyclicState word.toList.length := by
  rw [cyclicEval_weighted unitWeight (by
    intro letter
    exact Or.inl rfl)]
  rw [weightSum_unit]

private theorem cyclicEval_doubled
    (tested : Nat) (word : Word Nat) :
    cyclicFourOne.semigroup.eval
        (weightedValuation (doubledWeight tested)) word =
      cyclicState (word.toList.length + word.toList.count tested) := by
  rw [cyclicEval_weighted (doubledWeight tested) (by
    intro letter
    by_cases hit : letter = tested
    · exact Or.inr (by simp [doubledWeight, hit])
    · exact Or.inl (by simp [doubledWeight, hit]))]
  rw [weightSum_doubled]

private theorem cyclicState_eq_one
    {n : Nat} (positive : 0 < n) :
    cyclicState n = cyclicState 1 ↔ n = 1 := by
  constructor
  · intro equal
    by_cases one : n = 1
    · exact one
    · by_cases two : n = 2
      · subst n
        simp [cyclicState] at equal
      · by_cases three : n = 3
        · subst n
          simp [cyclicState] at equal
        · simp [cyclicState, one, two, three] at equal
  · intro equal
    rw [equal]

private theorem cyclicState_eq_two
    {n : Nat} (positive : 0 < n) :
    cyclicState n = cyclicState 2 ↔ n = 2 := by
  constructor
  · intro equal
    by_cases one : n = 1
    · subst n
      simp [cyclicState] at equal
    · by_cases two : n = 2
      · exact two
      · by_cases three : n = 3
        · subst n
          simp [cyclicState] at equal
        · simp [cyclicState, one, two, three] at equal
  · intro equal
    rw [equal]

private theorem cyclicState_eq_three
    {n : Nat} (positive : 0 < n) :
    cyclicState n = cyclicState 3 ↔ n = 3 := by
  constructor
  · intro equal
    by_cases one : n = 1
    · subst n
      simp [cyclicState] at equal
    · by_cases two : n = 2
      · subst n
        simp [cyclicState] at equal
      · by_cases three : n = 3
        · exact three
        · simp [cyclicState, one, two, three] at equal
  · intro equal
    rw [equal]

private theorem cyclicState_one_add_injective
    {left right : Nat} (leftBound : left ≤ 1)
    (rightBound : right ≤ 1)
    (equal : cyclicState (1 + left) = cyclicState (1 + right)) :
    left = right := by
  have leftCases : left = 0 ∨ left = 1 := by omega
  have rightCases : right = 0 ∨ right = 1 := by omega
  rcases leftCases with rfl | rfl <;>
    rcases rightCases with rfl | rfl <;>
    simp [cyclicState] at equal ⊢

private theorem cyclicState_two_add_injective
    {left right : Nat} (leftBound : left ≤ 2)
    (rightBound : right ≤ 2)
    (equal : cyclicState (2 + left) = cyclicState (2 + right)) :
    left = right := by
  have leftCases : left = 0 ∨ left = 1 ∨ left = 2 := by omega
  have rightCases : right = 0 ∨ right = 1 ∨ right = 2 := by omega
  rcases leftCases with rfl | rfl | rfl <;>
    rcases rightCases with rfl | rfl | rfl <;>
    simp [cyclicState] at equal ⊢

private theorem cyclicState_three_add_zero_iff (count : Nat) :
    cyclicState (3 + count) = cyclicState 3 ↔ count = 0 := by
  by_cases zero : count = 0
  · subst count
    simp
  · have sumOne : 3 + count ≠ 1 := by omega
    have sumTwo : 3 + count ≠ 2 := by omega
    have sumThree : 3 + count ≠ 3 := by omega
    simp [cyclicState, sumOne, sumTwo, sumThree, zero]

private theorem wordLength_positive (word : Word Nat) :
    0 < word.toList.length := by
  cases word
  simp [Word.toList]

private theorem lengthState_one_iff (word : Word Nat) :
    lengthState word = .one ↔ word.toList.length = 1 := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [lengthState, Word.toList]
      | cons second rest =>
          cases rest with
          | nil =>
              simp [lengthState, Word.toList]
          | cons third more =>
              cases more with
              | nil =>
                  simp [lengthState, Word.toList]
              | cons fourth remaining =>
                  simp [lengthState, Word.toList]

private theorem lengthState_two_iff (word : Word Nat) :
    lengthState word = .two ↔ word.toList.length = 2 := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [lengthState, Word.toList]
      | cons second rest =>
          cases rest with
          | nil =>
              simp [lengthState, Word.toList]
          | cons third more =>
              cases more with
              | nil =>
                  simp [lengthState, Word.toList]
              | cons fourth remaining =>
                  simp [lengthState, Word.toList]

private theorem lengthState_three_iff (word : Word Nat) :
    lengthState word = .three ↔ word.toList.length = 3 := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [lengthState, Word.toList]
      | cons second rest =>
          cases rest with
          | nil =>
              simp [lengthState, Word.toList]
          | cons third more =>
              cases more with
              | nil =>
                  simp [lengthState, Word.toList]
              | cons fourth remaining =>
                  simp [lengthState, Word.toList]

private theorem lengthState_long_of_length
    (word : Word Nat) (long : 4 ≤ word.toList.length) :
    lengthState word = .long := by
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
                  rfl

private theorem cyclic_length_state
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy cyclicFourOne.semigroup) :
    cyclicState identity.lhs.toList.length =
      cyclicState identity.rhs.toList.length := by
  have evaluated := valid (weightedValuation unitWeight)
  rw [cyclicEval_unit, cyclicEval_unit] at evaluated
  exact evaluated

private theorem cyclic_doubled_state
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy cyclicFourOne.semigroup) :
    ∀ tested,
      cyclicState
          (identity.lhs.toList.length +
            identity.lhs.toList.count tested) =
        cyclicState
          (identity.rhs.toList.length +
            identity.rhs.toList.count tested) := by
  intro tested
  have evaluated := valid (weightedValuation (doubledWeight tested))
  rw [cyclicEval_doubled, cyclicEval_doubled] at evaluated
  exact evaluated

/-- The cyclic factor distinguishes lengths one, two, three, and at least
four. -/
theorem valid_lengthState
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    lengthState identity.lhs = lengthState identity.rhs := by
  have equal := cyclic_length_state identity
    (valid_cyclicFourOne identity valid)
  have leftPositive := wordLength_positive identity.lhs
  have rightPositive := wordLength_positive identity.rhs
  by_cases leftOne : identity.lhs.toList.length = 1
  · have rightOne : identity.rhs.toList.length = 1 := by
      apply (cyclicState_eq_one rightPositive).mp
      rw [← equal, leftOne]
    rw [(lengthState_one_iff identity.lhs).2 leftOne,
      (lengthState_one_iff identity.rhs).2 rightOne]
  · by_cases leftTwo : identity.lhs.toList.length = 2
    · have rightTwo : identity.rhs.toList.length = 2 := by
        apply (cyclicState_eq_two rightPositive).mp
        rw [← equal, leftTwo]
      rw [(lengthState_two_iff identity.lhs).2 leftTwo,
        (lengthState_two_iff identity.rhs).2 rightTwo]
    · by_cases leftThree : identity.lhs.toList.length = 3
      · have rightThree : identity.rhs.toList.length = 3 := by
          apply (cyclicState_eq_three rightPositive).mp
          rw [← equal, leftThree]
        rw [(lengthState_three_iff identity.lhs).2 leftThree,
          (lengthState_three_iff identity.rhs).2 rightThree]
      · have leftLong : 4 ≤ identity.lhs.toList.length := by omega
        have rightNotOne : identity.rhs.toList.length ≠ 1 := by
          intro rightOne
          apply leftOne
          apply (cyclicState_eq_one leftPositive).mp
          rw [equal, rightOne]
        have rightNotTwo : identity.rhs.toList.length ≠ 2 := by
          intro rightTwo
          apply leftTwo
          apply (cyclicState_eq_two leftPositive).mp
          rw [equal, rightTwo]
        have rightNotThree : identity.rhs.toList.length ≠ 3 := by
          intro rightThree
          apply leftThree
          apply (cyclicState_eq_three leftPositive).mp
          rw [equal, rightThree]
        have rightLong : 4 ≤ identity.rhs.toList.length := by omega
        rw [lengthState_long_of_length identity.lhs leftLong,
          lengthState_long_of_length identity.rhs rightLong]

/-- In the singleton stratum, the cyclic factor recovers every exact
multiplicity. -/
theorem valid_lengthOne_count_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (leftOne : lengthState identity.lhs = .one) :
    ∀ tested,
      identity.lhs.toList.count tested =
        identity.rhs.toList.count tested := by
  have states := valid_lengthState identity valid
  have rightOne : lengthState identity.rhs = .one := by
    rw [← states]
    exact leftOne
  have leftLength := (lengthState_one_iff identity.lhs).1 leftOne
  have rightLength := (lengthState_one_iff identity.rhs).1 rightOne
  have doubled := cyclic_doubled_state identity
    (valid_cyclicFourOne identity valid)
  intro tested
  apply cyclicState_one_add_injective
  · simpa [leftLength] using
      (List.count_le_length
        (a := tested) (l := identity.lhs.toList))
  · simpa [rightLength] using
      (List.count_le_length
        (a := tested) (l := identity.rhs.toList))
  · simpa [leftLength, rightLength] using doubled tested

/-- In the quadratic stratum, the cyclic factor recovers every exact
multiplicity. -/
theorem valid_lengthTwo_count_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (leftTwo : lengthState identity.lhs = .two) :
    ∀ tested,
      identity.lhs.toList.count tested =
        identity.rhs.toList.count tested := by
  have states := valid_lengthState identity valid
  have rightTwo : lengthState identity.rhs = .two := by
    rw [← states]
    exact leftTwo
  have leftLength := (lengthState_two_iff identity.lhs).1 leftTwo
  have rightLength := (lengthState_two_iff identity.rhs).1 rightTwo
  have doubled := cyclic_doubled_state identity
    (valid_cyclicFourOne identity valid)
  intro tested
  apply cyclicState_two_add_injective
  · simpa [leftLength] using
      (List.count_le_length
        (a := tested) (l := identity.lhs.toList))
  · simpa [rightLength] using
      (List.count_le_length
        (a := tested) (l := identity.rhs.toList))
  · simpa [leftLength, rightLength] using doubled tested

private theorem sameSupport_of_count_eq
    {left right : Word Nat}
    (counts : ∀ tested,
      left.toList.count tested = right.toList.count tested) :
    SameSupport left right := by
  intro tested
  constructor
  · intro member
    have positive : 0 < left.toList.count tested :=
      List.count_pos_iff.mpr member
    rw [counts tested] at positive
    exact List.count_pos_iff.mp positive
  · intro member
    have positive : 0 < right.toList.count tested :=
      List.count_pos_iff.mpr member
    rw [← counts tested] at positive
    exact List.count_pos_iff.mp positive

theorem valid_lengthOne_support
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (leftOne : lengthState identity.lhs = .one) :
    SameSupport identity.lhs identity.rhs :=
  sameSupport_of_count_eq
    (valid_lengthOne_count_eq identity valid leftOne)

theorem valid_lengthTwo_support
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (leftTwo : lengthState identity.lhs = .two) :
    SameSupport identity.lhs identity.rhs :=
  sameSupport_of_count_eq
    (valid_lengthTwo_count_eq identity valid leftTwo)

private theorem word_eq_of_length_one_and_head
    (left right : Word Nat)
    (leftLength : left.toList.length = 1)
    (rightLength : right.toList.length = 1)
    (heads : left.head = right.head) :
    left = right := by
  cases left with
  | mk leftHead leftTail =>
      cases leftTail with
      | nil =>
          cases right with
          | mk rightHead rightTail =>
              cases rightTail with
              | nil =>
                  simp only at heads
                  subst rightHead
                  rfl
              | cons rightNext rightRest =>
                  simp [Word.toList] at rightLength
      | cons leftNext leftRest =>
          simp [Word.toList] at leftLength

private theorem word_eq_of_length_two_head_support
    (left right : Word Nat)
    (leftLength : left.toList.length = 2)
    (rightLength : right.toList.length = 2)
    (heads : left.head = right.head)
    (support : SameSupport left right) :
    left = right := by
  cases left with
  | mk leftHead leftTail =>
      cases leftTail with
      | nil =>
          simp [Word.toList] at leftLength
      | cons leftNext leftRest =>
          cases leftRest with
          | nil =>
              cases right with
              | mk rightHead rightTail =>
                  cases rightTail with
                  | nil =>
                      simp [Word.toList] at rightLength
                  | cons rightNext rightRest =>
                      cases rightRest with
                      | nil =>
                          simp only at heads
                          subst rightHead
                          by_cases nextIsHead : leftNext = leftHead
                          · subst leftNext
                            have rightInLeft :=
                              (support rightNext).mpr (by
                                simp [Word.toList])
                            have rightIsHead : rightNext = leftHead := by
                              simpa [Word.toList] using rightInLeft
                            subst rightNext
                            rfl
                          · have leftInRight :=
                              (support leftNext).mp (by
                                simp [Word.toList])
                            have nextEqual : leftNext = rightNext := by
                              simpa [Word.toList, nextIsHead] using
                                leftInRight
                            subst rightNext
                            rfl
                      | cons rightThird rightMore =>
                          simp [Word.toList] at rightLength
          | cons leftThird leftMore =>
              simp [Word.toList] at leftLength

/-- Equal head plus the singleton length state forces literal word
equality. -/
theorem valid_lengthOne_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (leftOne : lengthState identity.lhs = .one) :
    identity.lhs = identity.rhs := by
  have states := valid_lengthState identity valid
  have rightOne : lengthState identity.rhs = .one := by
    rw [← states]
    exact leftOne
  exact word_eq_of_length_one_and_head identity.lhs identity.rhs
    ((lengthState_one_iff identity.lhs).1 leftOne)
    ((lengthState_one_iff identity.rhs).1 rightOne)
    (valid_head identity valid)

/-- Equal head plus the exact quadratic support recovered from cyclic
counts forces literal word equality. -/
theorem valid_lengthTwo_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (leftTwo : lengthState identity.lhs = .two) :
    identity.lhs = identity.rhs := by
  have states := valid_lengthState identity valid
  have rightTwo : lengthState identity.rhs = .two := by
    rw [← states]
    exact leftTwo
  exact word_eq_of_length_two_head_support identity.lhs identity.rhs
    ((lengthState_two_iff identity.lhs).1 leftTwo)
    ((lengthState_two_iff identity.rhs).1 rightTwo)
    (valid_head identity valid)
    (valid_lengthTwo_support identity valid leftTwo)

/-- At total length three, doubled cyclic valuations recover exactly the
support, though not all multiplicities. -/
theorem valid_lengthThreeSupport
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (leftThree : lengthState identity.lhs = .three) :
    SameSupport identity.lhs identity.rhs := by
  have states := valid_lengthState identity valid
  have rightThree : lengthState identity.rhs = .three := by
    rw [← states]
    exact leftThree
  have leftLength :=
    (lengthState_three_iff identity.lhs).1 leftThree
  have rightLength :=
    (lengthState_three_iff identity.rhs).1 rightThree
  have doubled := cyclic_doubled_state identity
    (valid_cyclicFourOne identity valid)
  have countZero : ∀ tested,
      identity.lhs.toList.count tested = 0 ↔
        identity.rhs.toList.count tested = 0 := by
    intro tested
    constructor
    · intro leftZero
      apply (cyclicState_three_add_zero_iff
        (identity.rhs.toList.count tested)).mp
      simpa [leftLength, rightLength, leftZero] using
        (doubled tested).symm
    · intro rightZero
      apply (cyclicState_three_add_zero_iff
        (identity.lhs.toList.count tested)).mp
      simpa [leftLength, rightLength, rightZero] using doubled tested
  intro tested
  constructor
  · intro leftMember
    apply Decidable.byContradiction
    intro rightAbsent
    have rightZero := List.count_eq_zero.mpr rightAbsent
    exact
      (List.count_eq_zero.mp ((countZero tested).mpr rightZero))
        leftMember
  · intro rightMember
    apply Decidable.byContradiction
    intro leftAbsent
    have leftZero := List.count_eq_zero.mpr leftAbsent
    exact
      (List.count_eq_zero.mp ((countZero tested).mp leftZero))
        rightMember

/-- Every identity valid in the exact `S5_216` table carries the planned
head/content/length necessity signature. No completeness claim is made. -/
theorem valid_sameSignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameHeadContentLengthSignature identity.lhs identity.rhs :=
  { head := valid_head identity valid
    state := valid_lengthState identity valid
    lengthOne := fun leftOne =>
      congrArg Word.toList (valid_lengthOne_eq identity valid leftOne)
    lengthTwo := fun leftTwo =>
      congrArg Word.toList (valid_lengthTwo_eq identity valid leftTwo)
    lengthThreeSupport := fun leftThree =>
      valid_lengthThreeSupport identity valid leftThree }

set_option maxRecDepth 100000 in
/-- Every derivation from the recorded basis preserves the semantic
necessity signature, including through contexts and substitutions. -/
theorem derives_sameSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameHeadContentLengthSignature left right :=
  valid_sameSignature ⟨left, right⟩
    (fun valuation => derivation.sound models valuation)

/-- Every displayed basis law preserves the signature after an arbitrary
simultaneous nonempty-word substitution. -/
theorem basisLaw_bind_sameSignature
    (identity : Identity Nat) (member : identity ∈ basis)
    (substitution : Nat → Word Nat) :
    SameHeadContentLengthSignature
      (identity.lhs.bind substitution)
      (identity.rhs.bind substitution) :=
  derives_sameSignature <|
    Derives.subst
      (Derives.fromBasis (basis := basis) member) substitution

end SemigroupBasis.CoRoots.S5_216
