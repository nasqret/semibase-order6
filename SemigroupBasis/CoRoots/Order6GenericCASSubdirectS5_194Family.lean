import SemigroupBasis.CoRoots.S5_194
import SemigroupBasis.Generated.CatalogueOrder2
import SemigroupBasis.Generated.S2_2
import SemigroupBasis.Generated.S2_3
import SemigroupBasis.Subdirect

namespace SemigroupBasis.CoRoots.Order6GenericCASSubdirectS5_194Family

open SemigroupBasis
open SemigroupBasis.Examples

/-- A word constructor convenient for list-level permutation arguments. -/
def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private inductive ListDerives (basis : List (Identity Nat)) :
    List Nat → List Nat → Prop
  | empty : ListDerives basis [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives basis (wordOfCons x xs) (wordOfCons y ys) →
        ListDerives basis (x :: xs) (y :: ys)

private theorem listDerives_of_perm
    {basis : List (Identity Nat)}
    (commutes : ∀ u v : Word Nat,
      Derives basis (u ++ v) (v ++ u))
    {xs ys : List Nat} (permutation : xs.Perm ys) :
    ListDerives basis xs ys := by
  induction permutation with
  | nil =>
      exact ListDerives.empty
  | cons x _ ih =>
      cases ih with
      | empty =>
          exact ListDerives.words (Derives.refl _)
      | words derivation =>
          exact ListDerives.words <| by
            simpa [wordOfCons, Word.singleton, Word.append] using
              Derives.prepend (Word.singleton x) derivation
  | swap x y xs =>
      exact ListDerives.words <| by
        cases xs with
        | nil =>
            simpa [wordOfCons, Word.append, Word.singleton] using
              commutes (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (commutes (Word.singleton y) (Word.singleton x))
                (wordOfCons z zs)
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using swapped
  | trans _ _ first second =>
      cases first with
      | empty =>
          cases second
          exact ListDerives.empty
      | words firstDerivation =>
          cases second with
          | words secondDerivation =>
              exact ListDerives.words
                (Derives.trans firstDerivation secondDerivation)

/-- Global commutativity derives every permutation of a nonempty word. -/
theorem derivesPermutation
    {basis : List (Identity Nat)}
    (commutes : ∀ u v : Word Nat,
      Derives basis (u ++ v) (v ++ u))
    (u v : Word Nat) (permutation : u.toList.Perm v.toList) :
    Derives basis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm commutes permutation with
          | words derivation =>
              exact derivation

theorem catalogueS2_2_table_eq_cyclicTwo :
    SemigroupBasis.Generated.Catalogue.S2_2.table = cyclicTwo := by
  rw [← SemigroupBasis.Generated.S2_2.table_eq_catalogue_model]
  unfold SemigroupBasis.Generated.Catalogue.S2_2.table
    SemigroupBasis.Generated.Catalogue.S2_2.mul
    SemigroupBasis.Generated.S2_2.table cyclicTwoMul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext left right
  decide +revert

theorem catalogueS2_3_table_eq_semilatticeTwo :
    SemigroupBasis.Generated.Catalogue.S2_3.table = semilatticeTwo := by
  rw [← SemigroupBasis.Generated.S2_3.table_eq_catalogue_model]
  unfold SemigroupBasis.Generated.Catalogue.S2_3.table
    SemigroupBasis.Generated.Catalogue.S2_3.mul
    SemigroupBasis.Generated.S2_3.table semilatticeTwoMul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext left right
  decide +revert

def SameCounts (left right : Word Nat) : Prop :=
  ∀ z, left.toList.count z = right.toList.count z

def SameSupport (left right : Word Nat) : Prop :=
  ∀ z, z ∈ left.toList ↔ z ∈ right.toList

/-- The exact information supplied by `S5_194`: multiplicities through
degree three, support in degree four, and one class from degree five. -/
inductive S5_194Shape (left right : Word Nat) : Prop
  | one :
      left.toList.length = 1 → right.toList.length = 1 →
        SameCounts left right → S5_194Shape left right
  | two :
      left.toList.length = 2 → right.toList.length = 2 →
        SameCounts left right → S5_194Shape left right
  | three :
      left.toList.length = 3 → right.toList.length = 3 →
        SameCounts left right → S5_194Shape left right
  | four :
      left.toList.length = 4 → right.toList.length = 4 →
        SameSupport left right → S5_194Shape left right
  | long :
      5 ≤ left.toList.length → 5 ≤ right.toList.length →
        S5_194Shape left right

private theorem state_eq_one {n : Nat} (nPos : 0 < n) :
    SemigroupBasis.CoRoots.S5_194.powerState n =
        SemigroupBasis.CoRoots.S5_194.powerState 1 ↔
      n = 1 := by
  constructor
  · intro equal
    by_cases nOne : n = 1
    · exact nOne
    · by_cases nTwo : n = 2
      · subst n
        simp [SemigroupBasis.CoRoots.S5_194.powerState] at equal
      · by_cases nThree : n = 3
        · subst n
          simp [SemigroupBasis.CoRoots.S5_194.powerState] at equal
        · by_cases nFour : n = 4
          · subst n
            simp [SemigroupBasis.CoRoots.S5_194.powerState] at equal
          · simp [SemigroupBasis.CoRoots.S5_194.powerState,
              nOne, nTwo, nThree, nFour] at equal
  · intro equal
    rw [equal]

private theorem state_eq_two {n : Nat} (nPos : 0 < n) :
    SemigroupBasis.CoRoots.S5_194.powerState n =
        SemigroupBasis.CoRoots.S5_194.powerState 2 ↔
      n = 2 := by
  constructor
  · intro equal
    by_cases nOne : n = 1
    · subst n
      simp [SemigroupBasis.CoRoots.S5_194.powerState] at equal
    · by_cases nTwo : n = 2
      · exact nTwo
      · by_cases nThree : n = 3
        · subst n
          simp [SemigroupBasis.CoRoots.S5_194.powerState] at equal
        · by_cases nFour : n = 4
          · subst n
            simp [SemigroupBasis.CoRoots.S5_194.powerState] at equal
          · simp [SemigroupBasis.CoRoots.S5_194.powerState,
              nOne, nTwo, nThree, nFour] at equal
  · intro equal
    rw [equal]

private theorem state_eq_three {n : Nat} (nPos : 0 < n) :
    SemigroupBasis.CoRoots.S5_194.powerState n =
        SemigroupBasis.CoRoots.S5_194.powerState 3 ↔
      n = 3 := by
  constructor
  · intro equal
    by_cases nOne : n = 1
    · subst n
      simp [SemigroupBasis.CoRoots.S5_194.powerState] at equal
    · by_cases nTwo : n = 2
      · subst n
        simp [SemigroupBasis.CoRoots.S5_194.powerState] at equal
      · by_cases nThree : n = 3
        · exact nThree
        · by_cases nFour : n = 4
          · subst n
            simp [SemigroupBasis.CoRoots.S5_194.powerState] at equal
          · simp [SemigroupBasis.CoRoots.S5_194.powerState,
              nOne, nTwo, nThree, nFour] at equal
  · intro equal
    rw [equal]

private theorem state_eq_four {n : Nat} (nPos : 0 < n) :
    SemigroupBasis.CoRoots.S5_194.powerState n =
        SemigroupBasis.CoRoots.S5_194.powerState 4 ↔
      n = 4 := by
  constructor
  · intro equal
    by_cases nOne : n = 1
    · subst n
      simp [SemigroupBasis.CoRoots.S5_194.powerState] at equal
    · by_cases nTwo : n = 2
      · subst n
        simp [SemigroupBasis.CoRoots.S5_194.powerState] at equal
      · by_cases nThree : n = 3
        · subst n
          simp [SemigroupBasis.CoRoots.S5_194.powerState] at equal
        · by_cases nFour : n = 4
          · exact nFour
          · simp [SemigroupBasis.CoRoots.S5_194.powerState,
              nOne, nTwo, nThree, nFour] at equal
  · intro equal
    rw [equal]

private theorem state_one_add_injective
    {m n : Nat} (mLe : m ≤ 1) (nLe : n ≤ 1)
    (equal :
      SemigroupBasis.CoRoots.S5_194.powerState (1 + m) =
        SemigroupBasis.CoRoots.S5_194.powerState (1 + n)) :
    m = n := by
  have mCases : m = 0 ∨ m = 1 := by omega
  have nCases : n = 0 ∨ n = 1 := by omega
  rcases mCases with rfl | rfl <;>
    rcases nCases with rfl | rfl <;>
    simp [SemigroupBasis.CoRoots.S5_194.powerState] at equal ⊢

private theorem state_two_add_injective
    {m n : Nat} (mLe : m ≤ 2) (nLe : n ≤ 2)
    (equal :
      SemigroupBasis.CoRoots.S5_194.powerState (2 + m) =
        SemigroupBasis.CoRoots.S5_194.powerState (2 + n)) :
    m = n := by
  have mCases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  have nCases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases mCases with rfl | rfl | rfl <;>
    rcases nCases with rfl | rfl | rfl <;>
    simp [SemigroupBasis.CoRoots.S5_194.powerState] at equal ⊢

private theorem state_three_counts_injective
    {m n : Nat} (mLe : m ≤ 3) (nLe : n ≤ 3)
    (forward :
      SemigroupBasis.CoRoots.S5_194.powerState (3 + m) =
        SemigroupBasis.CoRoots.S5_194.powerState (3 + n))
    (complement :
      SemigroupBasis.CoRoots.S5_194.powerState (3 + (3 - m)) =
        SemigroupBasis.CoRoots.S5_194.powerState (3 + (3 - n))) :
    m = n := by
  have mCases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
  have nCases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases mCases with rfl | rfl | rfl | rfl <;>
    rcases nCases with rfl | rfl | rfl | rfl <;>
    simp [SemigroupBasis.CoRoots.S5_194.powerState] at forward complement ⊢

private theorem state_four_add_zero_iff (n : Nat) :
    SemigroupBasis.CoRoots.S5_194.powerState (4 + n) =
        SemigroupBasis.CoRoots.S5_194.powerState 4 ↔
      n = 0 := by
  by_cases nZero : n = 0
  · subst n
    simp
  · have sumOne : 4 + n ≠ 1 := by omega
    have sumTwo : 4 + n ≠ 2 := by omega
    have sumThree : 4 + n ≠ 3 := by omega
    have sumFour : 4 + n ≠ 4 := by omega
    simp [SemigroupBasis.CoRoots.S5_194.powerState,
      sumOne, sumTwo, sumThree, sumFour, nZero]

/-- Extract the reusable length/multiplicity/support trichotomy from validity
in the exact `S5_194` catalogue factor. -/
theorem s5_194Shape_of_valid (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_194.table.semigroup) :
    S5_194Shape identity.lhs identity.rhs := by
  have lengthState :=
    SemigroupBasis.CoRoots.S5_194.valid_length_state identity valid
  have doubledState :=
    SemigroupBasis.CoRoots.S5_194.valid_doubled_state identity valid
  have complementState :=
    SemigroupBasis.CoRoots.S5_194.valid_complement_state identity valid
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
    have countEq : SameCounts identity.lhs identity.rhs := by
      intro z
      apply state_one_add_injective
      · simpa [lhsOne] using
          (List.count_le_length
            (a := z) (l := identity.lhs.toList))
      · simpa [rhsOne] using
          (List.count_le_length
            (a := z) (l := identity.rhs.toList))
      · simpa [lhsOne, rhsOne] using doubledState z
    exact S5_194Shape.one lhsOne rhsOne countEq
  · by_cases lhsTwo : identity.lhs.toList.length = 2
    · have rhsTwo : identity.rhs.toList.length = 2 := by
        apply (state_eq_two rhsPos).mp
        rw [← lengthState, lhsTwo]
      have countEq : SameCounts identity.lhs identity.rhs := by
        intro z
        apply state_two_add_injective
        · simpa [lhsTwo] using
            (List.count_le_length
              (a := z) (l := identity.lhs.toList))
        · simpa [rhsTwo] using
            (List.count_le_length
              (a := z) (l := identity.rhs.toList))
        · simpa [lhsTwo, rhsTwo] using doubledState z
      exact S5_194Shape.two lhsTwo rhsTwo countEq
    · by_cases lhsThree : identity.lhs.toList.length = 3
      · have rhsThree : identity.rhs.toList.length = 3 := by
          apply (state_eq_three rhsPos).mp
          rw [← lengthState, lhsThree]
        have countEq : SameCounts identity.lhs identity.rhs := by
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
        exact S5_194Shape.three lhsThree rhsThree countEq
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
              simpa [lhsFour, rhsFour, rhsZero] using doubledState z
          have supportEq : SameSupport identity.lhs identity.rhs := by
            intro z
            constructor
            · intro lhsMember
              have lhsPositive : 0 < identity.lhs.toList.count z :=
                List.count_pos_iff.mpr lhsMember
              have rhsNonzero : identity.rhs.toList.count z ≠ 0 := by
                intro rhsZero
                have lhsZero := (countZeroEq z).mpr rhsZero
                omega
              exact List.count_pos_iff.mp
                (Nat.pos_of_ne_zero rhsNonzero)
            · intro rhsMember
              have rhsPositive : 0 < identity.rhs.toList.count z :=
                List.count_pos_iff.mpr rhsMember
              have lhsNonzero : identity.lhs.toList.count z ≠ 0 := by
                intro lhsZero
                have rhsZero := (countZeroEq z).mp lhsZero
                omega
              exact List.count_pos_iff.mp
                (Nat.pos_of_ne_zero lhsNonzero)
          exact S5_194Shape.four lhsFour rhsFour supportEq
        · have lhsLong : 5 ≤ identity.lhs.toList.length := by omega
          have rhsNotOne : identity.rhs.toList.length ≠ 1 := by
            intro rhsOne
            have lhsStateOne :
                SemigroupBasis.CoRoots.S5_194.powerState
                    identity.lhs.toList.length =
                  SemigroupBasis.CoRoots.S5_194.powerState 1 := by
              rw [lengthState, rhsOne]
            exact lhsOne <| (state_eq_one lhsPos).mp lhsStateOne
          have rhsNotTwo : identity.rhs.toList.length ≠ 2 := by
            intro rhsTwo
            have lhsStateTwo :
                SemigroupBasis.CoRoots.S5_194.powerState
                    identity.lhs.toList.length =
                  SemigroupBasis.CoRoots.S5_194.powerState 2 := by
              rw [lengthState, rhsTwo]
            exact lhsTwo <| (state_eq_two lhsPos).mp lhsStateTwo
          have rhsNotThree : identity.rhs.toList.length ≠ 3 := by
            intro rhsThree
            have lhsStateThree :
                SemigroupBasis.CoRoots.S5_194.powerState
                    identity.lhs.toList.length =
                  SemigroupBasis.CoRoots.S5_194.powerState 3 := by
              rw [lengthState, rhsThree]
            exact lhsThree <|
              (state_eq_three lhsPos).mp lhsStateThree
          have rhsNotFour : identity.rhs.toList.length ≠ 4 := by
            intro rhsFour
            have lhsStateFour :
                SemigroupBasis.CoRoots.S5_194.powerState
                    identity.lhs.toList.length =
                  SemigroupBasis.CoRoots.S5_194.powerState 4 := by
              rw [lengthState, rhsFour]
            exact lhsFour <| (state_eq_four lhsPos).mp lhsStateFour
          have rhsLong : 5 ≤ identity.rhs.toList.length := by omega
          exact S5_194Shape.long lhsLong rhsLong

end SemigroupBasis.CoRoots.Order6GenericCASSubdirectS5_194Family
