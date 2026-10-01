import SemigroupBasis.Generated.S4_11

namespace SemigroupBasis.CoRoots.Order6GenericCASSubdirectS4_11Family

open SemigroupBasis
open SemigroupBasis.Examples

/-- Identify the generated catalogue factor with the concrete cyclic
semigroup `C(4,1)`. -/
theorem catalogueTable_eq_cyclicFourOne :
    SemigroupBasis.Generated.Catalogue.S4_11.table = cyclicFourOne := by
  calc
    SemigroupBasis.Generated.Catalogue.S4_11.table =
        SemigroupBasis.Generated.S4_11.table :=
      SemigroupBasis.Generated.S4_11.table_eq_canonical_catalogue.symm
    _ = cyclicFourOne := rfl

private def lengthState (length : Nat) : Fin 4 :=
  if length = 1 then 3
  else if length = 2 then 1
  else if length = 3 then 2
  else 0

private theorem mul_lengthState_generator
    (length : Nat) (positive : 0 < length) :
    cyclicFourOneMul (lengthState length) (lengthState 1) =
      lengthState (length + 1) := by
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
        simp [lengthState, cyclicFourOneMul, zero, one, two, three,
          nextOne, nextTwo, nextThree]

private theorem fold_generator
    (letters : List Nat) (accumulator : Nat)
    (positive : 0 < accumulator) :
    letters.foldl
        (fun current _ =>
          cyclicFourOneMul current (lengthState 1))
        (lengthState accumulator) =
      lengthState (accumulator + letters.length) := by
  induction letters generalizing accumulator with
  | nil => simp
  | cons letter rest inductionHypothesis =>
      simp only [List.foldl_cons, List.length_cons]
      rw [mul_lengthState_generator accumulator positive]
      rw [inductionHypothesis (accumulator + 1) (by omega)]
      congr 1
      omega

private def generatorValuation : Nat → Fin 4 :=
  fun _ => lengthState 1

private theorem eval_generator (word : Word Nat) :
    cyclicFourOne.semigroup.eval generatorValuation word =
      lengthState word.toList.length := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ =>
              cyclicFourOneMul current (lengthState 1))
            (lengthState 1) =
          lengthState (List.length (head :: tail))
      rw [fold_generator tail 1 (by omega)]
      simp [Nat.add_comm]

private theorem lengthState_eq_one
    {length : Nat} (positive : 0 < length) :
    lengthState length = lengthState 1 ↔ length = 1 := by
  constructor
  · intro equality
    by_cases one : length = 1
    · exact one
    · by_cases two : length = 2
      · subst length
        simp [lengthState] at equality
      · by_cases three : length = 3
        · subst length
          simp [lengthState] at equality
        · simp [lengthState, one, two, three] at equality
  · intro equality
    rw [equality]

private theorem lengthState_eq_two
    {length : Nat} (positive : 0 < length) :
    lengthState length = lengthState 2 ↔ length = 2 := by
  constructor
  · intro equality
    by_cases one : length = 1
    · subst length
      simp [lengthState] at equality
    · by_cases two : length = 2
      · exact two
      · by_cases three : length = 3
        · subst length
          simp [lengthState] at equality
        · simp [lengthState, one, two, three] at equality
  · intro equality
    rw [equality]

private theorem lengthState_eq_three
    {length : Nat} (positive : 0 < length) :
    lengthState length = lengthState 3 ↔ length = 3 := by
  constructor
  · intro equality
    by_cases one : length = 1
    · subst length
      simp [lengthState] at equality
    · by_cases two : length = 2
      · subst length
        simp [lengthState] at equality
      · by_cases three : length = 3
        · exact three
        · simp [lengthState, one, two, three] at equality
  · intro equality
    rw [equality]

/-- Every identity valid in the catalogue copy of `C(4,1)` has both words in
the same one-, two-, three-, or at-least-four length stratum. -/
theorem lengthShape
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S4_11.table.semigroup) :
    (identity.lhs.toList.length = 1 ∧
        identity.rhs.toList.length = 1) ∨
      (identity.lhs.toList.length = 2 ∧
        identity.rhs.toList.length = 2) ∨
      (identity.lhs.toList.length = 3 ∧
        identity.rhs.toList.length = 3) ∨
      (4 ≤ identity.lhs.toList.length ∧
        4 ≤ identity.rhs.toList.length) := by
  have concreteValid :
      identity.SatisfiedBy cyclicFourOne.semigroup := by
    rw [← catalogueTable_eq_cyclicFourOne]
    exact valid
  have stateEq :
      lengthState identity.lhs.toList.length =
        lengthState identity.rhs.toList.length := by
    have evaluated := concreteValid generatorValuation
    rw [eval_generator, eval_generator] at evaluated
    exact evaluated
  have lhsPositive : 0 < identity.lhs.toList.length := by
    cases identity.lhs
    simp [Word.toList]
  have rhsPositive : 0 < identity.rhs.toList.length := by
    cases identity.rhs
    simp [Word.toList]
  by_cases lhsOne : identity.lhs.toList.length = 1
  · have rhsOne : identity.rhs.toList.length = 1 := by
      apply (lengthState_eq_one rhsPositive).mp
      rw [← stateEq, lhsOne]
    exact Or.inl ⟨lhsOne, rhsOne⟩
  · by_cases lhsTwo : identity.lhs.toList.length = 2
    · have rhsTwo : identity.rhs.toList.length = 2 := by
        apply (lengthState_eq_two rhsPositive).mp
        rw [← stateEq, lhsTwo]
      exact Or.inr <| Or.inl ⟨lhsTwo, rhsTwo⟩
    · by_cases lhsThree : identity.lhs.toList.length = 3
      · have rhsThree : identity.rhs.toList.length = 3 := by
          apply (lengthState_eq_three rhsPositive).mp
          rw [← stateEq, lhsThree]
        exact Or.inr <| Or.inr <| Or.inl ⟨lhsThree, rhsThree⟩
      · have lhsLong : 4 ≤ identity.lhs.toList.length := by omega
        have rhsNotOne : identity.rhs.toList.length ≠ 1 := by
          intro rhsOne
          have lhsStateOne :
              lengthState identity.lhs.toList.length =
                lengthState 1 := by
            rw [stateEq, rhsOne]
          exact lhsOne <| (lengthState_eq_one lhsPositive).mp lhsStateOne
        have rhsNotTwo : identity.rhs.toList.length ≠ 2 := by
          intro rhsTwo
          have lhsStateTwo :
              lengthState identity.lhs.toList.length =
                lengthState 2 := by
            rw [stateEq, rhsTwo]
          exact lhsTwo <| (lengthState_eq_two lhsPositive).mp lhsStateTwo
        have rhsNotThree : identity.rhs.toList.length ≠ 3 := by
          intro rhsThree
          have lhsStateThree :
              lengthState identity.lhs.toList.length =
                lengthState 3 := by
            rw [stateEq, rhsThree]
          exact lhsThree <|
            (lengthState_eq_three lhsPositive).mp lhsStateThree
        have rhsLong : 4 ≤ identity.rhs.toList.length := by omega
        exact Or.inr <| Or.inr <| Or.inr ⟨lhsLong, rhsLong⟩

end SemigroupBasis.CoRoots.Order6GenericCASSubdirectS4_11Family
