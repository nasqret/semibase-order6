import SemigroupBasis.CoRoots.S5_194Normalization
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part02
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_194

open SemigroupBasis

/-- The exact stored Smallsemi representative `S5_194`. -/
abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_194.table

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S5_194.table := rfl

def finiteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def finiteLongCancellationLaw : Identity (Fin 6) :=
  ⟨⟨0, [1, 2, 3, 4, 5]⟩, ⟨1, [2, 3, 4, 5]⟩⟩

def finiteMultiplicityTransferLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

theorem finiteCommutativityLaw_map :
    finiteCommutativityLaw.map Fin.val = commutativityLaw := rfl

theorem finiteLongCancellationLaw_map :
    finiteLongCancellationLaw.map Fin.val =
      longCancellationLaw := rfl

theorem finiteMultiplicityTransferLaw_map :
    finiteMultiplicityTransferLaw.map Fin.val =
      multiplicityTransferLaw := rfl

private theorem mul_val_le_pred (left right : Fin 5) :
    (SemigroupBasis.Generated.Catalogue.S5_194.mul left right).val ≤
      left.val - 1 := by
  revert left right
  decide

private theorem mul_five_eq_zero
    (a b c d e : Fin 5) :
    SemigroupBasis.Generated.Catalogue.S5_194.mul
        (SemigroupBasis.Generated.Catalogue.S5_194.mul
          (SemigroupBasis.Generated.Catalogue.S5_194.mul
            (SemigroupBasis.Generated.Catalogue.S5_194.mul a b) c) d) e =
      (0 : Fin 5) := by
  have aBound : a.val < 5 := a.isLt
  have abBound := mul_val_le_pred a b
  have abcBound := mul_val_le_pred
    (SemigroupBasis.Generated.Catalogue.S5_194.mul a b) c
  have abcdBound := mul_val_le_pred
    (SemigroupBasis.Generated.Catalogue.S5_194.mul
      (SemigroupBasis.Generated.Catalogue.S5_194.mul a b) c) d
  have abcdeBound := mul_val_le_pred
    (SemigroupBasis.Generated.Catalogue.S5_194.mul
      (SemigroupBasis.Generated.Catalogue.S5_194.mul
        (SemigroupBasis.Generated.Catalogue.S5_194.mul a b) c) d) e
  apply Fin.ext
  change
    (SemigroupBasis.Generated.Catalogue.S5_194.mul
      (SemigroupBasis.Generated.Catalogue.S5_194.mul
        (SemigroupBasis.Generated.Catalogue.S5_194.mul
          (SemigroupBasis.Generated.Catalogue.S5_194.mul a b) c) d) e).val = 0
  omega

private theorem zero_mul (value : Fin 5) :
    SemigroupBasis.Generated.Catalogue.S5_194.mul (0 : Fin 5) value = 0 := by
  revert value
  decide

private theorem longCancellation_eval
    (a b c d e f : Fin 5) :
    SemigroupBasis.Generated.Catalogue.S5_194.mul
        (SemigroupBasis.Generated.Catalogue.S5_194.mul
          (SemigroupBasis.Generated.Catalogue.S5_194.mul
            (SemigroupBasis.Generated.Catalogue.S5_194.mul
              (SemigroupBasis.Generated.Catalogue.S5_194.mul a b) c) d) e) f =
      SemigroupBasis.Generated.Catalogue.S5_194.mul
        (SemigroupBasis.Generated.Catalogue.S5_194.mul
          (SemigroupBasis.Generated.Catalogue.S5_194.mul
            (SemigroupBasis.Generated.Catalogue.S5_194.mul b c) d) e) f := by
  calc
    _ = SemigroupBasis.Generated.Catalogue.S5_194.mul 0 f := by
      rw [mul_five_eq_zero a b c d e]
    _ = 0 := zero_mul f
    _ = _ := (mul_five_eq_zero b c d e f).symm

private theorem longCancellationLaw_valid :
    longCancellationLaw.SatisfiedBy table.semigroup := by
  intro valuation
  change
    SemigroupBasis.Generated.Catalogue.S5_194.mul
        (SemigroupBasis.Generated.Catalogue.S5_194.mul
          (SemigroupBasis.Generated.Catalogue.S5_194.mul
            (SemigroupBasis.Generated.Catalogue.S5_194.mul
              (SemigroupBasis.Generated.Catalogue.S5_194.mul
                (valuation 0) (valuation 1)) (valuation 2))
              (valuation 3)) (valuation 4)) (valuation 5) =
      SemigroupBasis.Generated.Catalogue.S5_194.mul
        (SemigroupBasis.Generated.Catalogue.S5_194.mul
          (SemigroupBasis.Generated.Catalogue.S5_194.mul
            (SemigroupBasis.Generated.Catalogue.S5_194.mul
              (valuation 1) (valuation 2)) (valuation 3))
          (valuation 4)) (valuation 5)
  exact longCancellation_eval
    (valuation 0) (valuation 1) (valuation 2)
    (valuation 3) (valuation 4) (valuation 5)

/-- The exact catalogue table models all three recorded identities. -/
theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · rw [← finiteCommutativityLaw_map]
    exact table.checkIdentityNat_sound finiteCommutativityLaw (by decide)
  · exact longCancellationLaw_valid
  · rw [← finiteMultiplicityTransferLaw_map]
    exact table.checkIdentityNat_sound
      finiteMultiplicityTransferLaw (by decide)

/-- The state of the generator power `g^n`, where one-based generator `5`
has powers `5,4,3,2,1,1,...`. -/
def powerState (n : Nat) : Fin 5 :=
  if n = 1 then 4
  else if n = 2 then 3
  else if n = 3 then 2
  else if n = 4 then 1
  else 0

private theorem mul_state_one (n : Nat) (nPos : 0 < n) :
    SemigroupBasis.Generated.Catalogue.S5_194.mul
        (powerState n) (powerState 1) =
      powerState (n + 1) := by
  by_cases nOne : n = 1
  · subst n
    rfl
  · by_cases nTwo : n = 2
    · subst n
      rfl
    · by_cases nThree : n = 3
      · subst n
        rfl
      · by_cases nFour : n = 4
        · subst n
          rfl
        · have nFive : 5 ≤ n := by omega
          have nZero : n ≠ 0 := by omega
          have nextOne : n + 1 ≠ 1 := by omega
          have nextTwo : n + 1 ≠ 2 := by omega
          have nextThree : n + 1 ≠ 3 := by omega
          have nextFour : n + 1 ≠ 4 := by omega
          apply Fin.ext
          simp [powerState, nZero, nOne, nTwo, nThree, nFour,
            nextOne, nextTwo, nextThree, nextFour,
            SemigroupBasis.Generated.Catalogue.S5_194.mul]

private theorem mul_state_two (n : Nat) (nPos : 0 < n) :
    SemigroupBasis.Generated.Catalogue.S5_194.mul
        (powerState n) (powerState 2) =
      powerState (n + 2) := by
  by_cases nOne : n = 1
  · subst n
    rfl
  · by_cases nTwo : n = 2
    · subst n
      rfl
    · by_cases nThree : n = 3
      · subst n
        rfl
      · by_cases nFour : n = 4
        · subst n
          rfl
        · have nFive : 5 ≤ n := by omega
          have nZero : n ≠ 0 := by omega
          have nextOne : n + 2 ≠ 1 := by omega
          have nextTwo : n + 2 ≠ 2 := by omega
          have nextThree : n + 2 ≠ 3 := by omega
          have nextFour : n + 2 ≠ 4 := by omega
          apply Fin.ext
          simp [powerState, nZero, nOne, nTwo, nThree, nFour,
            nextOne, nextTwo, nextThree, nextFour,
            SemigroupBasis.Generated.Catalogue.S5_194.mul]

def weightSum (weight : Nat → Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => weight x + weightSum weight xs

def weightedValuation (weight : Nat → Nat) : Nat → Fin 5 :=
  fun x => powerState (weight x)

private theorem fold_weighted
    (weight : Nat → Nat)
    (oneOrTwo : ∀ x, weight x = 1 ∨ weight x = 2)
    (xs : List Nat) (acc : Nat) (accPos : 0 < acc) :
    xs.foldl
        (fun current x =>
          SemigroupBasis.Generated.Catalogue.S5_194.mul current
            (weightedValuation weight x))
        (powerState acc) =
      powerState (acc + weightSum weight xs) := by
  induction xs generalizing acc with
  | nil =>
      simp [weightSum]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases oneOrTwo x with weightOne | weightTwo
      · rw [show weightedValuation weight x =
          powerState 1 by simp [weightedValuation, weightOne]]
        rw [mul_state_one acc accPos]
        rw [ih (acc + 1) (by omega)]
        simp [weightSum, weightOne]
        congr 1
        omega
      · rw [show weightedValuation weight x =
          powerState 2 by simp [weightedValuation, weightTwo]]
        rw [mul_state_two acc accPos]
        rw [ih (acc + 2) (by omega)]
        simp [weightSum, weightTwo]
        congr 1
        omega

theorem eval_weighted
    (weight : Nat → Nat)
    (oneOrTwo : ∀ x, weight x = 1 ∨ weight x = 2)
    (word : Word Nat) :
    table.semigroup.eval (weightedValuation weight) word =
      powerState (weightSum weight word.toList) := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              SemigroupBasis.Generated.Catalogue.S5_194.mul current
                (weightedValuation weight x))
            (weightedValuation weight head) =
          powerState (weightSum weight (head :: tail))
      rw [show weightedValuation weight head =
          powerState (weight head) by rfl]
      have headPos : 0 < weight head := by
        rcases oneOrTwo head with equal | equal <;> omega
      rw [fold_weighted weight oneOrTwo tail
        (weight head) headPos]
      simp [weightSum]

def unitWeight : Nat → Nat := fun _ => 1

def doubledWeight (z : Nat) : Nat → Nat :=
  fun x => if x = z then 2 else 1

def complementWeight (z : Nat) : Nat → Nat :=
  fun x => if x = z then 1 else 2

theorem weightSum_unit (xs : List Nat) :
    weightSum unitWeight xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [weightSum, unitWeight, ih, Nat.add_comm]

theorem weightSum_doubled (z : Nat) (xs : List Nat) :
    weightSum (doubledWeight z) xs =
      xs.length + xs.count z := by
  induction xs with
  | nil =>
      simp [weightSum]
  | cons x xs ih =>
      by_cases equal : x = z
      · subst x
        simp [weightSum, doubledWeight, ih]
        omega
      · simp [weightSum, doubledWeight, equal, ih]
        omega

theorem weightSum_complement (z : Nat) (xs : List Nat) :
    weightSum (complementWeight z) xs =
      xs.length + (xs.length - xs.count z) := by
  induction xs with
  | nil =>
      simp [weightSum]
  | cons x xs ih =>
      have countBound :=
        List.count_le_length (a := z) (l := xs)
      by_cases equal : x = z
      · subst x
        simp [weightSum, complementWeight, ih]
        omega
      · simp [weightSum, complementWeight, equal, ih]
        omega

theorem eval_unit (word : Word Nat) :
    table.semigroup.eval (weightedValuation unitWeight) word =
      powerState word.toList.length := by
  rw [eval_weighted unitWeight (by
    intro x
    exact Or.inl rfl)]
  rw [weightSum_unit]

theorem eval_doubled (z : Nat) (word : Word Nat) :
    table.semigroup.eval (weightedValuation (doubledWeight z)) word =
      powerState (word.toList.length + word.toList.count z) := by
  rw [eval_weighted (doubledWeight z) (by
    intro x
    by_cases equal : x = z
    · exact Or.inr (by simp [doubledWeight, equal])
    · exact Or.inl (by simp [doubledWeight, equal]))]
  rw [weightSum_doubled]

theorem eval_complement (z : Nat) (word : Word Nat) :
    table.semigroup.eval (weightedValuation (complementWeight z)) word =
      powerState
        (word.toList.length +
          (word.toList.length - word.toList.count z)) := by
  rw [eval_weighted (complementWeight z) (by
    intro x
    by_cases equal : x = z
    · exact Or.inl (by simp [complementWeight, equal])
    · exact Or.inr (by simp [complementWeight, equal]))]
  rw [weightSum_complement]

private theorem state_eq_one {n : Nat} (nPos : 0 < n) :
    powerState n = powerState 1 ↔ n = 1 := by
  constructor
  · intro equal
    by_cases nOne : n = 1
    · exact nOne
    · by_cases nTwo : n = 2
      · subst n
        simp [powerState] at equal
      · by_cases nThree : n = 3
        · subst n
          simp [powerState] at equal
        · by_cases nFour : n = 4
          · subst n
            simp [powerState] at equal
          · simp [powerState, nOne, nTwo, nThree, nFour] at equal
  · intro equal
    rw [equal]

private theorem state_eq_two {n : Nat} (nPos : 0 < n) :
    powerState n = powerState 2 ↔ n = 2 := by
  constructor
  · intro equal
    by_cases nOne : n = 1
    · subst n
      simp [powerState] at equal
    · by_cases nTwo : n = 2
      · exact nTwo
      · by_cases nThree : n = 3
        · subst n
          simp [powerState] at equal
        · by_cases nFour : n = 4
          · subst n
            simp [powerState] at equal
          · simp [powerState, nOne, nTwo, nThree, nFour] at equal
  · intro equal
    rw [equal]

private theorem state_eq_three {n : Nat} (nPos : 0 < n) :
    powerState n = powerState 3 ↔ n = 3 := by
  constructor
  · intro equal
    by_cases nOne : n = 1
    · subst n
      simp [powerState] at equal
    · by_cases nTwo : n = 2
      · subst n
        simp [powerState] at equal
      · by_cases nThree : n = 3
        · exact nThree
        · by_cases nFour : n = 4
          · subst n
            simp [powerState] at equal
          · simp [powerState, nOne, nTwo, nThree, nFour] at equal
  · intro equal
    rw [equal]

private theorem state_eq_four {n : Nat} (nPos : 0 < n) :
    powerState n = powerState 4 ↔ n = 4 := by
  constructor
  · intro equal
    by_cases nOne : n = 1
    · subst n
      simp [powerState] at equal
    · by_cases nTwo : n = 2
      · subst n
        simp [powerState] at equal
      · by_cases nThree : n = 3
        · subst n
          simp [powerState] at equal
        · by_cases nFour : n = 4
          · exact nFour
          · simp [powerState, nOne, nTwo, nThree, nFour] at equal
  · intro equal
    rw [equal]

private theorem state_one_add_injective
    {m n : Nat} (mLe : m ≤ 1) (nLe : n ≤ 1)
    (equal : powerState (1 + m) = powerState (1 + n)) :
    m = n := by
  have mCases : m = 0 ∨ m = 1 := by omega
  have nCases : n = 0 ∨ n = 1 := by omega
  rcases mCases with rfl | rfl <;>
    rcases nCases with rfl | rfl <;>
    simp [powerState] at equal ⊢

private theorem state_two_add_injective
    {m n : Nat} (mLe : m ≤ 2) (nLe : n ≤ 2)
    (equal : powerState (2 + m) = powerState (2 + n)) :
    m = n := by
  have mCases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  have nCases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases mCases with rfl | rfl | rfl <;>
    rcases nCases with rfl | rfl | rfl <;>
    simp [powerState] at equal ⊢

private theorem state_three_counts_injective
    {m n : Nat} (mLe : m ≤ 3) (nLe : n ≤ 3)
    (forward :
      powerState (3 + m) = powerState (3 + n))
    (complement :
      powerState (3 + (3 - m)) =
        powerState (3 + (3 - n))) :
    m = n := by
  have mCases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
  have nCases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases mCases with rfl | rfl | rfl | rfl <;>
    rcases nCases with rfl | rfl | rfl | rfl <;>
    simp [powerState] at forward complement ⊢

private theorem state_four_add_zero_iff (n : Nat) :
    powerState (4 + n) = powerState 4 ↔ n = 0 := by
  by_cases nZero : n = 0
  · subst n
    simp
  · have nPos : 0 < n := Nat.pos_of_ne_zero nZero
    have sumOne : 4 + n ≠ 1 := by omega
    have sumTwo : 4 + n ≠ 2 := by omega
    have sumThree : 4 + n ≠ 3 := by omega
    have sumFour : 4 + n ≠ 4 := by omega
    simp [powerState, sumOne, sumTwo, sumThree, sumFour, nZero]

theorem valid_length_state
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    powerState identity.lhs.toList.length =
      powerState identity.rhs.toList.length := by
  have evaluated := valid (weightedValuation unitWeight)
  rw [eval_unit, eval_unit] at evaluated
  exact evaluated

theorem valid_doubled_state
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ z,
      powerState
          (identity.lhs.toList.length +
            identity.lhs.toList.count z) =
        powerState
          (identity.rhs.toList.length +
            identity.rhs.toList.count z) := by
  intro z
  have evaluated := valid (weightedValuation (doubledWeight z))
  rw [eval_doubled, eval_doubled] at evaluated
  exact evaluated

theorem valid_complement_state
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ z,
      powerState
          (identity.lhs.toList.length +
            (identity.lhs.toList.length -
              identity.lhs.toList.count z)) =
        powerState
          (identity.rhs.toList.length +
            (identity.rhs.toList.length -
              identity.rhs.toList.count z)) := by
  intro z
  have evaluated := valid (weightedValuation (complementWeight z))
  rw [eval_complement, eval_complement] at evaluated
  exact evaluated

/-- The normal-form invariant is exact multiplicity through length three,
support at length four, and one universal class from length five onward. -/
theorem basis_complete : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  have lengthState := valid_length_state identity valid
  have doubledState := valid_doubled_state identity valid
  have complementState := valid_complement_state identity valid
  have lhsPos : 0 < identity.lhs.toList.length := by
    cases identity.lhs
    simp [Word.toList]
  have rhsPos : 0 < identity.rhs.toList.length := by
    cases identity.rhs
    simp [Word.toList]
  by_cases lhsOne : identity.lhs.toList.length = 1
  · have rhsOne : identity.rhs.toList.length = 1 := by
      apply (state_eq_one rhsPos).mp
      rw [← lengthState, lhsOne]
    have countEq :
        ∀ z,
          identity.lhs.toList.count z =
            identity.rhs.toList.count z := by
      intro z
      apply state_one_add_injective
      · simpa [lhsOne] using
          (List.count_le_length
            (a := z) (l := identity.lhs.toList))
      · simpa [rhsOne] using
          (List.count_le_length
            (a := z) (l := identity.rhs.toList))
      · simpa [lhsOne, rhsOne] using doubledState z
    exact derivesPermutation identity.lhs identity.rhs <|
      List.perm_iff_count.mpr countEq
  · by_cases lhsTwo : identity.lhs.toList.length = 2
    · have rhsTwo : identity.rhs.toList.length = 2 := by
        apply (state_eq_two rhsPos).mp
        rw [← lengthState, lhsTwo]
      have countEq :
          ∀ z,
            identity.lhs.toList.count z =
              identity.rhs.toList.count z := by
        intro z
        apply state_two_add_injective
        · simpa [lhsTwo] using
            (List.count_le_length
              (a := z) (l := identity.lhs.toList))
        · simpa [rhsTwo] using
            (List.count_le_length
              (a := z) (l := identity.rhs.toList))
        · simpa [lhsTwo, rhsTwo] using doubledState z
      exact derivesPermutation identity.lhs identity.rhs <|
        List.perm_iff_count.mpr countEq
    · by_cases lhsThree : identity.lhs.toList.length = 3
      · have rhsThree : identity.rhs.toList.length = 3 := by
          apply (state_eq_three rhsPos).mp
          rw [← lengthState, lhsThree]
        have countEq :
            ∀ z,
              identity.lhs.toList.count z =
                identity.rhs.toList.count z := by
          intro z
          apply state_three_counts_injective
          · simpa [lhsThree] using
              (List.count_le_length
                (a := z) (l := identity.lhs.toList))
          · simpa [rhsThree] using
              (List.count_le_length
                (a := z) (l := identity.rhs.toList))
          · simpa [lhsThree, rhsThree] using doubledState z
          · simpa [lhsThree, rhsThree] using complementState z
        exact derivesPermutation identity.lhs identity.rhs <|
          List.perm_iff_count.mpr countEq
      · by_cases lhsFour : identity.lhs.toList.length = 4
        · have rhsFour : identity.rhs.toList.length = 4 := by
            apply (state_eq_four rhsPos).mp
            rw [← lengthState, lhsFour]
          have countZeroEq :
              ∀ z,
                identity.lhs.toList.count z = 0 ↔
                  identity.rhs.toList.count z = 0 := by
            intro z
            constructor
            · intro lhsZero
              apply (state_four_add_zero_iff
                (identity.rhs.toList.count z)).mp
              simpa [lhsFour, rhsFour, lhsZero] using
                (doubledState z).symm
            · intro rhsZero
              apply (state_four_add_zero_iff
                (identity.lhs.toList.count z)).mp
              simpa [lhsFour, rhsFour, rhsZero] using
                doubledState z
          have supportEq :
              ∀ z,
                z ∈ identity.lhs.toList ↔
                  z ∈ identity.rhs.toList := by
            intro z
            constructor
            · intro lhsMember
              have lhsPositive :
                  0 < identity.lhs.toList.count z :=
                List.count_pos_iff.mpr lhsMember
              have rhsNonzero :
                  identity.rhs.toList.count z ≠ 0 := by
                intro rhsZero
                have lhsZero := (countZeroEq z).mpr rhsZero
                omega
              exact List.count_pos_iff.mp
                (Nat.pos_of_ne_zero rhsNonzero)
            · intro rhsMember
              have rhsPositive :
                  0 < identity.rhs.toList.count z :=
                List.count_pos_iff.mpr rhsMember
              have lhsNonzero :
                  identity.lhs.toList.count z ≠ 0 := by
                intro lhsZero
                have rhsZero := (countZeroEq z).mp lhsZero
                omega
              exact List.count_pos_iff.mp
                (Nat.pos_of_ne_zero lhsNonzero)
          exact derivesLengthFourSupport
            identity.lhs identity.rhs lhsFour rhsFour supportEq
        · have lhsLong : 5 ≤ identity.lhs.toList.length := by omega
          have rhsNotOne : identity.rhs.toList.length ≠ 1 := by
            intro rhsOne
            have lhsStateOne :
                powerState identity.lhs.toList.length =
                  powerState 1 := by
              rw [lengthState, rhsOne]
            exact lhsOne <| (state_eq_one lhsPos).mp lhsStateOne
          have rhsNotTwo : identity.rhs.toList.length ≠ 2 := by
            intro rhsTwo
            have lhsStateTwo :
                powerState identity.lhs.toList.length =
                  powerState 2 := by
              rw [lengthState, rhsTwo]
            exact lhsTwo <| (state_eq_two lhsPos).mp lhsStateTwo
          have rhsNotThree : identity.rhs.toList.length ≠ 3 := by
            intro rhsThree
            have lhsStateThree :
                powerState identity.lhs.toList.length =
                  powerState 3 := by
              rw [lengthState, rhsThree]
            exact lhsThree <|
              (state_eq_three lhsPos).mp lhsStateThree
          have rhsNotFour : identity.rhs.toList.length ≠ 4 := by
            intro rhsFour
            have lhsStateFour :
                powerState identity.lhs.toList.length =
                  powerState 4 := by
              rw [lengthState, rhsFour]
            exact lhsFour <| (state_eq_four lhsPos).mp lhsStateFour
          have rhsLong : 5 ≤ identity.rhs.toList.length := by omega
          exact derivesLongWords
            identity.lhs identity.rhs lhsLong rhsLong

theorem representative_basis : BasisFor table.semigroup basis :=
  basis_complete

theorem self_dual :
    table.semigroup.opposite = table.semigroup := by
  unfold table SemigroupBasis.Generated.Catalogue.S5_194.table
    SemigroupBasis.Generated.Catalogue.S5_194.mul
    FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext a b
  apply Fin.ext
  decide +revert

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite basis := by
  rw [self_dual]
  exact basis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite basis :=
  opposite_basis_complete

end SemigroupBasis.CoRoots.S5_194
