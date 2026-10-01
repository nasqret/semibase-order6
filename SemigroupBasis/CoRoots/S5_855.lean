import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.CoRoots.S5_855Normalization
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_855

open SemigroupBasis
open SemigroupBasis.Examples

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_855.table

def finiteRightDuplicationLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def finiteInitialMoveLaw : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

theorem finiteRightDuplicationLaw_map :
    finiteRightDuplicationLaw.map Fin.val =
      rightDuplicationLaw := rfl

theorem finiteInitialMoveLaw_map :
    finiteInitialMoveLaw.map Fin.val = initialMoveLaw := rfl

/-- The exact catalogue table satisfies the ordered two-law basis. -/
theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [← finiteRightDuplicationLaw_map]
    exact table.checkIdentityNat_sound
      finiteRightDuplicationLaw (by decide)
  · rw [← finiteInitialMoveLaw_map]
    exact table.checkIdentityNat_sound
      finiteInitialMoveLaw (by decide)

/-- Quotient recording the complete first-occurrence sequence. -/
def firstOccurrenceQuotient :
    SplitSurjection table.semigroup leftRegularBandThree.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨0, by decide⟩ else
        if value.val = 2 then ⟨2, by decide⟩ else
          ⟨1, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨3, by decide⟩ else
        ⟨2, by decide⟩
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

theorem valid_firstOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
    identity
    (firstOccurrenceQuotient.pushforwardIdentity identity valid)

/-- Zero-based states `3` and `4` preserve every right factor. -/
def finalSeparator (tested : Nat) : Nat → Fin 5 :=
  fun letter => if letter = tested then 4 else 3

private theorem finalSeparator_mul
    (tested leftLetter rightLetter : Nat) :
    Generated.Catalogue.S5_855.mul
        (finalSeparator tested leftLetter)
        (finalSeparator tested rightLetter) =
      finalSeparator tested rightLetter := by
  by_cases leftEqual : leftLetter = tested
  · subst leftLetter
    by_cases rightEqual : rightLetter = tested
    · subst rightLetter
      simp [finalSeparator, Generated.Catalogue.S5_855.mul]
    · simp [finalSeparator, rightEqual, eq_comm,
        Generated.Catalogue.S5_855.mul]
  · by_cases rightEqual : rightLetter = tested
    · subst rightLetter
      simp [finalSeparator, leftEqual, eq_comm,
        Generated.Catalogue.S5_855.mul]
    · simp [finalSeparator, leftEqual, rightEqual, eq_comm,
        Generated.Catalogue.S5_855.mul]

theorem finalSeparator_eval
    (tested : Nat) (stem : List Nat) (final : Nat) :
    table.semigroup.eval (finalSeparator tested)
        (wordOfPrefixFinal stem final) =
      finalSeparator tested final := by
  induction stem with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton, induction]
      exact finalSeparator_mul tested letter final

private theorem final_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).final = final := by
  induction stem with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact induction

theorem valid_final_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.lhs.final = identity.rhs.final := by
  have splitFinalEq :
      (splitPrefixFinal identity.lhs).2 =
        (splitPrefixFinal identity.rhs).2 := by
    let tested := (splitPrefixFinal identity.lhs).2
    have evaluated := valid (finalSeparator tested)
    rw [← wordOfPrefixFinal_split identity.lhs,
      ← wordOfPrefixFinal_split identity.rhs,
      finalSeparator_eval, finalSeparator_eval] at evaluated
    apply Decidable.byContradiction
    intro different
    have reversed :
        (splitPrefixFinal identity.rhs).2 =
          (splitPrefixFinal identity.lhs).2 := by
      simpa [tested, finalSeparator, different] using evaluated
    exact different reversed.symm
  have leftFinal :
      (splitPrefixFinal identity.lhs).2 =
        identity.lhs.final := by
    have reconstructed :=
      congrArg Word.final (wordOfPrefixFinal_split identity.lhs)
    rw [final_wordOfPrefixFinal] at reconstructed
    exact reconstructed
  have rightFinal :
      (splitPrefixFinal identity.rhs).2 =
        identity.rhs.final := by
    have reconstructed :=
      congrArg Word.final (wordOfPrefixFinal_split identity.rhs)
    rw [final_wordOfPrefixFinal] at reconstructed
    exact reconstructed
  exact leftFinal.symm.trans (splitFinalEq.trans rightFinal)

/-- One-based state `2` survives pass states but collapses to one-based state
`1` after a second occurrence of the tested initial variable. -/
def initialMultiplicitySeparator (tested : Nat) : Nat → Fin 5 :=
  fun letter => if letter = tested then 1 else 3

private theorem zero_fold
    (tested : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            Generated.Catalogue.S5_855.mul current
              (initialMultiplicitySeparator tested letter))
          0 = 0
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [show
        Generated.Catalogue.S5_855.mul 0
            (initialMultiplicitySeparator tested letter) = 0 by
          by_cases equal : letter = tested
          · subst letter
            simp [initialMultiplicitySeparator,
              Generated.Catalogue.S5_855.mul]
          · have value :
                initialMultiplicitySeparator tested letter =
                  (3 : Fin 5) := by
              simp [initialMultiplicitySeparator, equal, eq_comm]
            rw [value]
            decide]
      exact zero_fold tested rest

private theorem initialMultiplicityFold
    (tested : Nat) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            Generated.Catalogue.S5_855.mul current
              (initialMultiplicitySeparator tested letter))
          1 =
        if tested ∈ letters then 0 else 1
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      by_cases equal : letter = tested
      · subst letter
        rw [show initialMultiplicitySeparator tested tested =
            (1 : Fin 5) by
          simp [initialMultiplicitySeparator]]
        rw [show Generated.Catalogue.S5_855.mul 1 1 = (0 : Fin 5) by
          decide]
        rw [zero_fold]
        simp
      · rw [show initialMultiplicitySeparator tested letter =
            (3 : Fin 5) by
          simp [initialMultiplicitySeparator, equal, eq_comm]]
        rw [show Generated.Catalogue.S5_855.mul 1 3 = (1 : Fin 5) by
          decide]
        rw [initialMultiplicityFold]
        have reverse : tested ≠ letter := Ne.symm equal
        simp [equal, reverse]

theorem initialMultiplicitySeparator_eval
    (tested : Nat) (tail : List Nat) :
    table.semigroup.eval (initialMultiplicitySeparator tested)
        ⟨tested, tail⟩ =
      if tested ∈ tail then (0 : Fin 5) else (1 : Fin 5) := by
  change
    tail.foldl
        (fun current letter =>
          Generated.Catalogue.S5_855.mul current
            (initialMultiplicitySeparator tested letter))
        (initialMultiplicitySeparator tested tested) =
      if tested ∈ tail then 0 else 1
  rw [show initialMultiplicitySeparator tested tested = (1 : Fin 5) by
    simp [initialMultiplicitySeparator]]
  exact initialMultiplicityFold tested tail

theorem valid_repeatedInitial_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    repeatedInitial identity.lhs =
      repeatedInitial identity.rhs := by
  have orderEq :=
    valid_firstOccurrenceSequence_eq identity valid
  rcases identity with
    ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
  simp only [Word.toList, firstOccurrenceSequence,
    List.cons.injEq] at orderEq
  have heads : leftHead = rightHead := orderEq.1
  let tested := leftHead
  have evaluated := valid (initialMultiplicitySeparator tested)
  subst rightHead
  change
    table.semigroup.eval
        (initialMultiplicitySeparator leftHead)
        ⟨leftHead, leftTail⟩ =
      table.semigroup.eval
        (initialMultiplicitySeparator leftHead)
        ⟨leftHead, rightTail⟩ at evaluated
  rw [initialMultiplicitySeparator_eval,
    initialMultiplicitySeparator_eval] at evaluated
  unfold repeatedInitial
  by_cases leftMember : leftHead ∈ leftTail
  · by_cases rightMember : leftHead ∈ rightTail
    · simp [leftMember, rightMember]
    · simp [leftMember, rightMember] at evaluated
  · by_cases rightMember : leftHead ∈ rightTail
    · simp [leftMember, rightMember] at evaluated
    · simp [leftMember, rightMember]

theorem valid_signature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameInitialFinalSignature identity.lhs identity.rhs :=
  ⟨valid_firstOccurrenceSequence_eq identity valid,
    valid_final_eq identity valid,
    valid_repeatedInitial_eq identity valid⟩

/-- Unconditional exact-basis theorem for the stored representative. -/
theorem representative_basis :
    BasisFor table.semigroup basis :=
  basis_complete_of_signature table.semigroup models valid_signature

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def yx : Word Nat := ⟨1, [0]⟩
def yyx : Word Nat := ⟨1, [1, 0]⟩
def zyxx : Word Nat := ⟨2, [1, 0, 0]⟩
def zxyx : Word Nat := ⟨2, [0, 1, 0]⟩

def expectedOppositeBasis : List (Identity Nat) :=
  [⟨yx, yyx⟩, ⟨zyxx, zxyx⟩]

theorem oppositeBasis_eq_expected :
    oppositeBasis = expectedOppositeBasis := by
  rfl

/-- Unconditional literal reverse-word basis for the opposite table. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite expectedOppositeBasis := by
  rw [← oppositeBasis_eq_expected]
  exact representative_basis.oppositeReversed

def firstOccurrenceQuotientOneBased : List Nat :=
  List.ofFn fun value : Fin 5 =>
    (firstOccurrenceQuotient.toFun value).val + 1

theorem firstOccurrenceQuotient_certificate :
    firstOccurrenceQuotientOneBased = [1, 1, 3, 2, 2] := by
  decide

theorem passStates_certificate :
    Generated.Catalogue.S5_855.mul 3 3 = 3 ∧
      Generated.Catalogue.S5_855.mul 3 4 = 4 ∧
      Generated.Catalogue.S5_855.mul 4 3 = 3 ∧
      Generated.Catalogue.S5_855.mul 4 4 = 4 := by
  decide

theorem orderStates_certificate (value : Fin 5) :
    Generated.Catalogue.S5_855.mul 0 value = 0 ∧
      Generated.Catalogue.S5_855.mul 2 value = 2 := by
  revert value
  decide

theorem orderSeparator_certificate :
    Generated.Catalogue.S5_855.mul 2 0 = 2 ∧
      Generated.Catalogue.S5_855.mul 0 2 = 0 := by
  decide

theorem initialMultiplicity_certificate :
    Generated.Catalogue.S5_855.mul 1 3 = 1 ∧
      Generated.Catalogue.S5_855.mul 1 1 = 0 := by
  decide

theorem finalStates_certificate :
    Generated.Catalogue.S5_855.mul 3 3 = 3 ∧
      Generated.Catalogue.S5_855.mul 3 4 = 4 ∧
      Generated.Catalogue.S5_855.mul 4 3 = 3 ∧
      Generated.Catalogue.S5_855.mul 4 4 = 4 := by
  exact passStates_certificate

end SemigroupBasis.CoRoots.S5_855
