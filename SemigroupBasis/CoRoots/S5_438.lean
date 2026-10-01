import SemigroupBasis.Examples.HeadSortedParityTail
import SemigroupBasis.Examples.LeftZeroTwo
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part04
import SemigroupBasis.Opposite
import SemigroupBasis.Transfer

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_438

open SemigroupBasis
open SemigroupBasis.Examples

def storedXX : Word Nat := ⟨0, [0]⟩
def storedXXXX : Word Nat := ⟨0, [0, 0, 0]⟩
def storedXY : Word Nat := ⟨0, [1]⟩
def storedXXXY : Word Nat := ⟨0, [0, 0, 1]⟩
def storedXYX : Word Nat := ⟨0, [1, 0]⟩
def storedYXX : Word Nat := ⟨1, [0, 0]⟩
def storedXYZ : Word Nat := ⟨0, [1, 2]⟩
def storedYXZ : Word Nat := ⟨1, [0, 2]⟩

def storedPowerLaw : Identity Nat :=
  ⟨storedXX, storedXXXX⟩

def storedPrefixInflationLaw : Identity Nat :=
  ⟨storedXY, storedXXXY⟩

def storedGatherLaw : Identity Nat :=
  ⟨storedXYX, storedYXX⟩

def storedPrefixSwapLaw : Identity Nat :=
  ⟨storedXYZ, storedYXZ⟩

/-- The exact stored basis for `S5_438` and `S5_461`:
`xx = xxxx`, `xy = xxxy`, `xyx = yxx`, and `xyz = yxz`. -/
def basis : List (Identity Nat) :=
  [storedPowerLaw, storedPrefixInflationLaw,
    storedGatherLaw, storedPrefixSwapLaw]

def reversedYX : Word Nat := ⟨1, [0]⟩
def reversedYXXX : Word Nat := ⟨1, [0, 0, 0]⟩
def reversedXXY : Word Nat := ⟨0, [0, 1]⟩
def reversedZYX : Word Nat := ⟨2, [1, 0]⟩
def reversedZXY : Word Nat := ⟨2, [0, 1]⟩

def literalReversedPowerLaw : Identity Nat :=
  ⟨storedXX, storedXXXX⟩

def literalReversedInflationLaw : Identity Nat :=
  ⟨reversedYX, reversedYXXX⟩

def literalReversedGatherLaw : Identity Nat :=
  ⟨storedXYX, reversedXXY⟩

def literalReversedSwapLaw : Identity Nat :=
  ⟨reversedZYX, reversedZXY⟩

/-- The literal reverse-word transform of the stored basis. -/
def literalReversedBasis : List (Identity Nat) :=
  [literalReversedPowerLaw, literalReversedInflationLaw,
    literalReversedGatherLaw, literalReversedSwapLaw]

theorem reversedBasis_eq_literal :
    reversedBasis basis = literalReversedBasis := by
  rfl

/-- The alpha-renamed and symmetrically oriented cleaner basis used for
normalization in the opposite semigroup. -/
def oppositeCleanerBasis : List (Identity Nat) :=
  headSortedParityTailBasis

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_438.table

/-- The exact opposite multiplication table, retained as a `FiniteTable`
so the generic finite completeness theorem can be applied directly. -/
def oppositeTable : FiniteTable where
  order := 5
  mul := fun left right =>
    Generated.Catalogue.S5_438.mul right left
  assoc := by decide

def finiteStoredPowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteStoredPrefixInflationLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 0, 1]⟩⟩

def finiteStoredGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteStoredPrefixSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

theorem finiteStoredPowerLaw_map :
    finiteStoredPowerLaw.map Fin.val = storedPowerLaw := rfl

theorem finiteStoredPrefixInflationLaw_map :
    finiteStoredPrefixInflationLaw.map Fin.val =
      storedPrefixInflationLaw := rfl

theorem finiteStoredGatherLaw_map :
    finiteStoredGatherLaw.map Fin.val = storedGatherLaw := rfl

theorem finiteStoredPrefixSwapLaw_map :
    finiteStoredPrefixSwapLaw.map Fin.val =
      storedPrefixSwapLaw := rfl

theorem representativeModels :
    Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · rw [← finiteStoredPowerLaw_map]
    exact table.checkIdentityNat_sound
      finiteStoredPowerLaw (by decide)
  · rw [← finiteStoredPrefixInflationLaw_map]
    exact table.checkIdentityNat_sound
      finiteStoredPrefixInflationLaw (by decide)
  · rw [← finiteStoredGatherLaw_map]
    exact table.checkIdentityNat_sound
      finiteStoredGatherLaw (by decide)
  · rw [← finiteStoredPrefixSwapLaw_map]
    exact table.checkIdentityNat_sound
      finiteStoredPrefixSwapLaw (by decide)

theorem literalReversedModels :
    Models oppositeTable.semigroup literalReversedBasis := by
  rw [← reversedBasis_eq_literal]
  simpa [oppositeTable, table, FiniteTable.semigroup,
    Semigroup.opposite] using representativeModels.oppositeReversed

private def swapFirstTwo : Nat → Word Nat
  | 0 => Word.singleton 1
  | 1 => Word.singleton 0
  | n + 2 => Word.singleton (n + 2)

private def swapFirstThird : Nat → Word Nat
  | 0 => Word.singleton 2
  | 1 => Word.singleton 1
  | 2 => Word.singleton 0
  | n + 3 => Word.singleton (n + 3)

/-- Exact alpha-renaming and symmetry bridge: every cleaner axiom is
derivable from the literal reversed stored basis. -/
theorem cleanerAxiomsDeriveLiteral
    (identity : Identity Nat)
    (member : identity ∈ oppositeCleanerBasis) :
    Derives literalReversedBasis identity.lhs identity.rhs := by
  simp only [oppositeCleanerBasis, headSortedParityTailBasis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · simpa [literalReversedBasis,
      literalReversedPowerLaw,
      headSortedParityTailHeadPowerLaw,
      headSortedParityTailXX, headSortedParityTailXXXX] using
      (Derives.fromBasis
        (e := literalReversedPowerLaw)
        (List.Mem.head _) :
        Derives literalReversedBasis
          storedXX storedXXXX)
  · have base :
        Derives literalReversedBasis
          reversedYX reversedYXXX :=
      Derives.fromBasis
        (e := literalReversedInflationLaw) <|
        List.Mem.tail _ (List.Mem.head _)
    have renamed := Derives.subst base swapFirstTwo
    simpa [literalReversedInflationLaw,
      headSortedParityTailContextPowerLaw,
      reversedYX, reversedYXXX,
      headSortedParityTailXY, headSortedParityTailXYYY,
      swapFirstTwo, Word.bind, Word.append,
      Word.singleton] using renamed
  · have base :
        Derives literalReversedBasis
          storedXYX reversedXXY :=
      Derives.fromBasis
        (e := literalReversedGatherLaw) <|
        List.Mem.tail _ <|
          List.Mem.tail _ (List.Mem.head _)
    simpa [literalReversedGatherLaw,
      headSortedParityTailGatherLaw,
      storedXYX, reversedXXY,
      headSortedParityTailXXY,
      headSortedParityTailXYX] using
      Derives.symm base
  · have base :
        Derives literalReversedBasis
          reversedZYX reversedZXY :=
      Derives.fromBasis
        (e := literalReversedSwapLaw) <|
        List.Mem.tail _ <|
          List.Mem.tail _ <|
            List.Mem.tail _ (List.Mem.head _)
    have renamed := Derives.subst base swapFirstThird
    simpa [literalReversedSwapLaw,
      headSortedParityTailSwapLaw,
      reversedZYX, reversedZXY,
      headSortedParityTailXYZ, headSortedParityTailXZY,
      swapFirstThird, Word.bind, Word.append,
      Word.singleton] using renamed

theorem cleanerModels :
    Models oppositeTable.semigroup oppositeCleanerBasis := by
  intro identity member valuation
  exact
    (cleanerAxiomsDeriveLiteral identity member).sound
      literalReversedModels valuation

/-- The one-based copy `[4,5]` of the two-element left-zero semigroup in
`S5_438.opposite`. -/
private def leftZeroSource0 : Fin leftZeroTwo.order :=
  ⟨0, by decide⟩

private def leftZeroTarget3 : Fin oppositeTable.order :=
  ⟨3, by decide⟩

private def leftZeroTarget4 : Fin oppositeTable.order :=
  ⟨4, by decide⟩

def leftZeroEmbedding :
    Embedding leftZeroTwo.semigroup oppositeTable.semigroup where
  toFun := fun value =>
    if value = leftZeroSource0 then leftZeroTarget3 else leftZeroTarget4
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

def leftZeroEmbeddingOneBased : List Nat := [4, 5]

theorem leftZeroEmbeddingOneBased_certificate :
    leftZeroEmbeddingOneBased = [4, 5] := rfl

/-- The one-based copy `[1,3,4]` of `parityIdentityThree` in
`S5_438.opposite`. -/
private def paritySource0 : Fin parityIdentityThree.order :=
  ⟨0, by decide⟩

private def paritySource1 : Fin parityIdentityThree.order :=
  ⟨1, by decide⟩

private def parityTarget0 : Fin oppositeTable.order :=
  ⟨0, by decide⟩

private def parityTarget2 : Fin oppositeTable.order :=
  ⟨2, by decide⟩

private def parityTarget3 : Fin oppositeTable.order :=
  ⟨3, by decide⟩

def parityEmbedding :
    Embedding parityIdentityThree.semigroup
      oppositeTable.semigroup where
  toFun := fun value =>
    if value = paritySource0 then parityTarget0
    else if value = paritySource1 then parityTarget2
    else parityTarget3
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

def parityEmbeddingOneBased : List Nat := [1, 3, 4]

theorem parityEmbeddingOneBased_certificate :
    parityEmbeddingOneBased = [1, 3, 4] := rfl

private theorem leftZeroValid_head_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftZeroTwo.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  apply Decidable.byContradiction
  intro headsNe
  let valuation : Nat → Fin 2 :=
    fun letter =>
      if letter = identity.lhs.head then 0 else 1
  have evaluated := valid valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm headsNe] at evaluated

theorem valid_head
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy oppositeTable.semigroup) :
    identity.lhs.head = identity.rhs.head :=
  leftZeroValid_head_eq identity <|
    leftZeroEmbedding.pullback_identity identity valid

theorem valid_support
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy oppositeTable.semigroup) :
    ∀ letter,
      letter ∈ identity.lhs.toList ↔
        letter ∈ identity.rhs.toList :=
  parityIdentityValid_support identity <|
    parityEmbedding.pullback_identity identity valid

theorem valid_parity
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy oppositeTable.semigroup) :
    ∀ letter,
      identity.lhs.toList.count letter % 2 =
        identity.rhs.toList.count letter % 2 :=
  parityIdentityValid_parity identity <|
    parityEmbedding.pullback_identity identity valid

/-- One-based table element `4`, a right identity in the opposite table. -/
def rightIdentity : Fin 5 := 3

/-- One-based table element `3`, used for the explicit tail
absence/odd/even profile. -/
def tailParityWitness : Fin 5 := 2

def tailParityProfileOneBased : List Nat :=
  [rightIdentity.val + 1, tailParityWitness.val + 1,
    (oppositeTable.mul tailParityWitness tailParityWitness).val + 1]

theorem tailParityProfileOneBased_certificate :
    tailParityProfileOneBased = [4, 3, 1] := by
  decide

/-- One-based head witnesses `2` and `3`. -/
def headPowerWitness (index : Fin 2) : Fin 5 :=
  if index = 0 then 1 else 2

theorem rightIdentity_certificate (value : Fin 5) :
    oppositeTable.mul value rightIdentity = value := by
  decide +revert

def headPowerWitnessesOneBased : List Nat :=
  [(headPowerWitness 0).val + 1,
    (headPowerWitness 1).val + 1]

theorem headPowerWitnessesOneBased_certificate :
    headPowerWitnessesOneBased = [2, 3] := by
  decide

private theorem headExponent_le_three (n : Nat) :
    periodTwoFromTwoExponent n ≤ 3 := by
  unfold periodTwoFromTwoExponent
  split <;> omega

private theorem headExponent_lt_four (n : Nat) :
    periodTwoFromTwoExponent n < 4 := by
  have bound := headExponent_le_three n
  omega

private def headExponentState (n : Nat) : Fin 4 :=
  ⟨periodTwoFromTwoExponent n, headExponent_lt_four n⟩

private def headExponentNext (state : Fin 4) : Fin 4 :=
  if h : state.val < 3 then
    ⟨state.val + 1, by omega⟩
  else
    ⟨state.val - 1, by omega⟩

private theorem headExponentState_succ (n : Nat) :
    headExponentState (n + 1) =
      headExponentNext (headExponentState n) := by
  apply Fin.ext
  by_cases h : periodTwoFromTwoExponent n < 3
  · simp [headExponentState, headExponentNext, h,
      periodTwoFromTwoExponent_succ]
  · simp [headExponentState, headExponentNext, h,
      periodTwoFromTwoExponent_succ]

def headPowerCode (state : Fin 4) : Fin 5 × Fin 5 :=
  if state = 0 then
    (rightIdentity, rightIdentity)
  else if state = 1 then
    (1, 2)
  else if state = 2 then
    (0, 0)
  else
    (0, 2)

def headPowerProfilesOneBased : List (List Nat) :=
  [[(headPowerCode 1).1.val + 1,
      (headPowerCode 1).2.val + 1],
    [(headPowerCode 2).1.val + 1,
      (headPowerCode 2).2.val + 1],
    [(headPowerCode 3).1.val + 1,
      (headPowerCode 3).2.val + 1]]

theorem headPowerProfilesOneBased_certificate :
    headPowerProfilesOneBased =
      [[2, 3], [1, 1], [1, 3]] := by
  decide

theorem headPowerCode_injective :
    Function.Injective headPowerCode := by
  intro left right
  revert left right
  decide

private def headPowerCoordinate
    (profile : Fin 5 × Fin 5) (index : Fin 2) : Fin 5 :=
  if index = 0 then profile.1 else profile.2

private theorem headPowerCode_step
    (state : Fin 4) (index : Fin 2)
    (nonzero : state ≠ 0) :
    oppositeTable.mul
        (headPowerCoordinate (headPowerCode state) index)
        (headPowerWitness index) =
      headPowerCoordinate
        (headPowerCode (headExponentNext state)) index := by
  revert state index
  decide

private theorem positiveHeadExponentState_ne_zero (n : Nat) :
    headExponentState (n + 1) ≠ 0 := by
  intro equal
  have values := congrArg Fin.val equal
  change periodTwoFromTwoExponent (n + 1) = 0 at values
  have positive :=
    periodTwoFromTwoExponent_pos (n := n + 1) (by omega)
  omega

/-- State after the head has supplied the first occurrence and `n`
additional head occurrences have appeared in the tail. -/
private def headPowerState
    (index : Fin 2) (n : Nat) : Fin 5 :=
  headPowerCoordinate
    (headPowerCode (headExponentState (n + 1))) index

private theorem headPowerState_step
    (index : Fin 2) (n : Nat) :
    oppositeTable.mul
        (headPowerState index n) (headPowerWitness index) =
      headPowerState index (n + 1) := by
  calc
    oppositeTable.mul
        (headPowerState index n) (headPowerWitness index) =
        headPowerCoordinate
          (headPowerCode
            (headExponentNext
              (headExponentState (n + 1)))) index := by
      exact headPowerCode_step
        (headExponentState (n + 1)) index
        (positiveHeadExponentState_ne_zero n)
    _ = headPowerState index (n + 1) := by
      simp [headPowerState, headExponentState_succ,
        Nat.add_assoc]

private theorem headPowerState_other
    (index : Fin 2) (n : Nat) :
    oppositeTable.mul
        (headPowerState index n) rightIdentity =
      headPowerState index n :=
  rightIdentity_certificate _

def headPowerValuation
    (index : Fin 2) (head : Nat) : Nat → Fin 5 :=
  fun letter =>
    if letter = head then headPowerWitness index
    else rightIdentity

private theorem headPowerValuation_self
    (index : Fin 2) (head : Nat) :
    headPowerValuation index head head =
      headPowerState index 0 := by
  by_cases first : index = 0
  · subst index
    simp [headPowerValuation, headPowerState,
      headPowerCoordinate, headPowerCode, headExponentState,
      periodTwoFromTwoExponent, headPowerWitness,
      rightIdentity]
  · have second : index = 1 := by
      apply Fin.ext
      omega
    subst index
    simp [headPowerValuation, headPowerState,
      headPowerCoordinate, headPowerCode, headExponentState,
      periodTwoFromTwoExponent, headPowerWitness,
      rightIdentity]

private theorem headPowerFold
    (index : Fin 2) (head : Nat) :
    ∀ (tail : List Nat) (n : Nat),
      tail.foldl
          (fun current letter =>
            oppositeTable.mul current
              (headPowerValuation index head letter))
          (headPowerState index n) =
        headPowerState index (n + tail.count head)
  | [], _ => by
      simp
  | letter :: tail, n => by
      simp only [List.foldl_cons]
      by_cases isHead : letter = head
      · subst letter
        rw [show headPowerValuation index head head =
            headPowerWitness index by
          simp [headPowerValuation]]
        rw [headPowerState_step, headPowerFold,
          List.count_cons_self]
        congr 1
        omega
      · rw [show headPowerValuation index head letter =
            rightIdentity by
          simp [headPowerValuation, isHead]]
        rw [headPowerState_other, headPowerFold,
          List.count_cons_of_ne isHead]

theorem eval_headPower
    (index : Fin 2) (head : Nat) (word : Word Nat)
    (startsWith : word.head = head) :
    oppositeTable.semigroup.eval
        (headPowerValuation index head) word =
      headPowerState index (word.tail.count head) := by
  cases word with
  | mk first tail =>
      simp only at startsWith
      subst first
      change
        tail.foldl
            (fun current letter =>
              oppositeTable.mul current
                (headPowerValuation index head letter))
            (headPowerValuation index head head) =
          headPowerState index (tail.count head)
      rw [headPowerValuation_self, headPowerFold]
      simp

theorem valid_headExponent
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy oppositeTable.semigroup) :
    periodTwoFromTwoExponent
        (identity.lhs.toList.count identity.lhs.head) =
      periodTwoFromTwoExponent
        (identity.rhs.toList.count identity.lhs.head) := by
  have heads := valid_head identity valid
  have first := valid
    (headPowerValuation 0 identity.lhs.head)
  have second := valid
    (headPowerValuation 1 identity.lhs.head)
  rw [eval_headPower 0 identity.lhs.head identity.lhs rfl,
    eval_headPower 0 identity.lhs.head identity.rhs heads.symm]
    at first
  rw [eval_headPower 1 identity.lhs.head identity.lhs rfl,
    eval_headPower 1 identity.lhs.head identity.rhs heads.symm]
    at second
  have profiles :
      headPowerCode
          (headExponentState
            (identity.lhs.tail.count identity.lhs.head + 1)) =
        headPowerCode
          (headExponentState
            (identity.rhs.tail.count identity.lhs.head + 1)) := by
    apply Prod.ext
    · simpa [headPowerState, headPowerCoordinate] using first
    · simpa [headPowerState, headPowerCoordinate] using second
  have states := headPowerCode_injective profiles
  have values := congrArg Fin.val states
  simpa [Word.toList, heads] using values

theorem cleaner_basis_complete :
    BasisFor oppositeTable.semigroup oppositeCleanerBasis := by
  simpa only [oppositeCleanerBasis] using
    headSortedParityTailBasis_complete_of_separates
      oppositeTable cleanerModels valid_head valid_support
      valid_parity valid_headExponent

/-- Completeness of the literal reverse-word basis in `S5_438.opposite`.
The call to `BasisFor.replace` records the exact alpha/symmetry bridge. -/
theorem literal_reversed_basis_complete :
    BasisFor oppositeTable.semigroup literalReversedBasis :=
  cleaner_basis_complete.replace
    literalReversedModels cleanerAxiomsDeriveLiteral

/-- Unrestricted exact basis theorem in the opposite orientation. -/
theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite (reversedBasis basis) := by
  rw [reversedBasis_eq_literal]
  simpa [oppositeTable, table, FiniteTable.semigroup,
    Semigroup.opposite] using literal_reversed_basis_complete

/-- Unrestricted exact basis theorem in the stored catalogue orientation. -/
theorem basis_complete :
    BasisFor table.semigroup basis := by
  have reversed := opposite_basis_complete.oppositeReversed
  simpa using reversed

end SemigroupBasis.CoRoots.S5_438
