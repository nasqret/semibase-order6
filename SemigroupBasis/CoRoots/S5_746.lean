import SemigroupBasis.CoRoots.S5_746Normalization
import SemigroupBasis.Generated.CatalogueOrder5Part06
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_746

open SemigroupBasis
open SemigroupBasis.Examples

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_746.table

def finiteLeftDuplicationLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteReturnDuplicationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

theorem finiteLeftDuplicationLaw_map :
    finiteLeftDuplicationLaw.map Fin.val = leftDuplicationLaw := rfl

theorem finiteReturnDuplicationLaw_map :
    finiteReturnDuplicationLaw.map Fin.val =
      returnDuplicationLaw := rfl

/-- The exact catalogue table satisfies the ordered two-law basis. -/
theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [← finiteLeftDuplicationLaw_map]
    exact table.checkIdentityNat_sound
      finiteLeftDuplicationLaw (by decide)
  · rw [← finiteReturnDuplicationLaw_map]
    exact table.checkIdentityNat_sound
      finiteReturnDuplicationLaw (by decide)

/-- Quotient recording the complete first-occurrence sequence. -/
def firstOccurrenceQuotient :
    SplitSurjection table.semigroup leftRegularBandThree.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨0, by decide⟩ else
        if value.val = 2 then ⟨1, by decide⟩ else
          if value.val = 3 then ⟨1, by decide⟩ else
            ⟨2, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨2, by decide⟩ else
        ⟨4, by decide⟩
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

/-- States `3` and `4` in one-based notation are pass states. -/
def finalSeparator (tested : Nat) : Nat → Fin 5 :=
  fun letter => if letter = tested then 2 else 3

private theorem finalSeparator_mul
    (tested letter : Nat) (value : Fin 5) :
    Generated.Catalogue.S5_746.mul
        (finalSeparator tested letter) value = value := by
  by_cases equal : letter = tested
  · subst letter
    simp [finalSeparator]
    revert value
    decide
  · simp [finalSeparator, equal]
    revert value
    decide

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
      exact finalSeparator_mul tested letter
        (finalSeparator tested final)

theorem valid_final_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    (splitPrefixFinal identity.lhs).2 =
      (splitPrefixFinal identity.rhs).2 := by
  let tested := (splitPrefixFinal identity.lhs).2
  have evaluated := valid (finalSeparator tested)
  rw [← wordOfPrefixFinal_split identity.lhs,
    ← wordOfPrefixFinal_split identity.rhs,
    finalSeparator_eval, finalSeparator_eval] at evaluated
  apply Decidable.byContradiction
  intro different
  have reverseDifferent :
      (splitPrefixFinal identity.rhs).2 ≠
        (splitPrefixFinal identity.lhs).2 :=
    Ne.symm different
  simp [tested, finalSeparator, reverseDifferent] at evaluated

/-- One-based state `2` survives only when it is the final factor; after any
following factor it collapses to one-based state `1`. -/
def repeatedFinalSeparator (tested : Nat) : Nat → Fin 5 :=
  fun letter => if letter = tested then 1 else 2

private theorem low_mul (value : Fin 5) :
    table.semigroup.mul (1 : Fin 5) value = (0 : Fin 5) := by
  change Generated.Catalogue.S5_746.mul 1 value = 0
  revert value
  decide

private theorem pass_mul (value : Fin 5) :
    table.semigroup.mul (2 : Fin 5) value = value := by
  change Generated.Catalogue.S5_746.mul 2 value = value
  revert value
  decide

theorem repeatedFinalSeparator_eval
    (tested : Nat) :
    ∀ stem : List Nat,
      (show Fin 5 from
        table.semigroup.eval (repeatedFinalSeparator tested)
          (wordOfPrefixFinal stem tested)) =
        if tested ∈ stem then (0 : Fin 5) else (1 : Fin 5)
  | [] => by simp [repeatedFinalSeparator]
  | letter :: rest => by
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton]
      by_cases equal : letter = tested
      · subst letter
        rw [show repeatedFinalSeparator tested tested = (1 : Fin 5) by
          simp [repeatedFinalSeparator]]
        rw [low_mul]
        simp
      · rw [show repeatedFinalSeparator tested letter = (2 : Fin 5) by
          simp [repeatedFinalSeparator, equal]]
        rw [pass_mul, repeatedFinalSeparator_eval tested rest]
        simp [Ne.symm equal]

theorem valid_final_mem_prefix_iff
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    (splitPrefixFinal identity.lhs).2 ∈
        (splitPrefixFinal identity.lhs).1 ↔
      (splitPrefixFinal identity.rhs).2 ∈
        (splitPrefixFinal identity.rhs).1 := by
  have finalEq := valid_final_eq identity valid
  rw [← finalEq]
  let tested := (splitPrefixFinal identity.lhs).2
  have evaluated := valid (repeatedFinalSeparator tested)
  rw [← wordOfPrefixFinal_split identity.lhs,
    ← wordOfPrefixFinal_split identity.rhs] at evaluated
  rw [← finalEq] at evaluated
  change
    table.semigroup.eval (repeatedFinalSeparator tested)
        (wordOfPrefixFinal
          (splitPrefixFinal identity.lhs).1 tested) =
      table.semigroup.eval (repeatedFinalSeparator tested)
        (wordOfPrefixFinal
          (splitPrefixFinal identity.rhs).1 tested) at evaluated
  have evaluatedMembership :
      (if tested ∈ (splitPrefixFinal identity.lhs).1 then
          (0 : Fin 5) else (1 : Fin 5)) =
        if tested ∈ (splitPrefixFinal identity.rhs).1 then
          (0 : Fin 5) else (1 : Fin 5) :=
    (repeatedFinalSeparator_eval tested
      (splitPrefixFinal identity.lhs).1).symm.trans <|
        evaluated.trans <|
          repeatedFinalSeparator_eval tested
            (splitPrefixFinal identity.rhs).1
  constructor
  · intro leftMember
    apply Decidable.byContradiction
    intro rightAbsent
    simp [tested, leftMember, rightAbsent] at evaluatedMembership
  · intro rightMember
    apply Decidable.byContradiction
    intro leftAbsent
    simp [tested, leftAbsent, rightMember] at evaluatedMembership

theorem valid_prefix_firstOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    firstOccurrenceSequence (splitPrefixFinal identity.lhs).1 =
      firstOccurrenceSequence (splitPrefixFinal identity.rhs).1 := by
  have fullEq :=
    valid_firstOccurrenceSequence_eq identity valid
  have finalEq := valid_final_eq identity valid
  have membership :=
    valid_final_mem_prefix_iff identity valid
  rw [toList_eq_splitPrefixFinal,
    toList_eq_splitPrefixFinal,
    firstOccurrenceSequence_append_final,
    firstOccurrenceSequence_append_final] at fullEq
  rw [finalEq] at fullEq membership
  by_cases leftMember :
      (splitPrefixFinal identity.rhs).2 ∈
        (splitPrefixFinal identity.lhs).1
  · have rightMember :
        (splitPrefixFinal identity.rhs).2 ∈
          (splitPrefixFinal identity.rhs).1 :=
      membership.mp leftMember
    simpa [leftMember, rightMember] using fullEq
  · have rightAbsent :
        (splitPrefixFinal identity.rhs).2 ∉
          (splitPrefixFinal identity.rhs).1 := by
      intro rightMember
      exact leftMember (membership.mpr rightMember)
    rw [if_neg leftMember, if_neg rightAbsent] at fullEq
    exact List.append_cancel_right fullEq

/-- Unconditional exact-basis theorem for the stored representative. -/
theorem representative_basis :
    BasisFor table.semigroup basis :=
  basis_complete_of_invariants table.semigroup models
    valid_prefix_firstOccurrenceSequence_eq valid_final_eq

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def yx : Word Nat := ⟨1, [0]⟩
def yxx : Word Nat := ⟨1, [0, 0]⟩
def zyx : Word Nat := ⟨2, [1, 0]⟩
def zxyx : Word Nat := ⟨2, [0, 1, 0]⟩

def expectedOppositeBasis : List (Identity Nat) :=
  [⟨yx, yxx⟩, ⟨zyx, zxyx⟩]

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
    firstOccurrenceQuotientOneBased = [1, 1, 2, 2, 3] := by
  decide

/-- Exact one-step order separator: high then low stays high, while low then
high collapses to one-based state `1`. -/
theorem orderSeparator_certificate :
    Generated.Catalogue.S5_746.mul 4 1 = 4 ∧
      Generated.Catalogue.S5_746.mul 1 4 = 0 := by
  decide

/-- The low state distinguishes a singleton from its square. -/
theorem singletonSeparator_certificate :
    table.semigroup.eval (fun _ : Nat => (1 : Fin 5))
        (Word.singleton 0) = (1 : Fin 5) ∧
      table.semigroup.eval (fun _ : Nat => (1 : Fin 5))
        ⟨0, [0]⟩ = (0 : Fin 5) := by
  decide

/-- Both pass states are exact left identities. -/
theorem passStates_certificate (value : Fin 5) :
    Generated.Catalogue.S5_746.mul 2 value = value ∧
      Generated.Catalogue.S5_746.mul 3 value = value := by
  revert value
  decide

/-- One-based state `5` is an exact left zero. -/
theorem highState_certificate (value : Fin 5) :
    Generated.Catalogue.S5_746.mul 4 value = 4 := by
  revert value
  decide

end SemigroupBasis.CoRoots.S5_746
