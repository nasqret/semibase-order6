import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0456FordNilBasis
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0446TailBudget
import SemigroupBasis.CoRoots.S5_254Family
import SemigroupBasis.CoRoots.S5_345Factors

/-! Exact unrestricted semantics for the two literal nil extensions.
The actual split projections reduce necessity and sufficiency to the
published S3_16 and M18 completeness theorems. This does not yet prove
completeness of B23: its guarded word-comparison theorem is separate. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil

open SemigroupBasis
open SemigroupBasis.Examples

def m18OppositeTable : FiniteTable where
  order := 5
  mul := fun left right => m18Table.mul right left
  assoc := by decide

private def m18ToFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

theorem m18BasisModelsOpposite : Models m18Table.semigroup.opposite S5_254.basis := by
  change Models m18OppositeTable.semigroup S5_254.basis
  exact FiniteCertificate.checkModels_sound m18OppositeTable S5_254.basis m18ToFinFour
    (by decide +kernel)

theorem m18OppositeBasisModels : Models m18Table.semigroup S5_254.oppositeBasis :=
  FiniteCertificate.checkModels_sound m18Table S5_254.oppositeBasis m18ToFinFour
    (by decide +kernel)

/-- Genuine unrestricted same-theory transport, using the complete lower
factor bases and actual finite model proofs in the other orientation. -/
theorem m18_valid_iff_opposite (identity : Identity Nat) :
    identity.SatisfiedBy m18Table.semigroup ↔
      identity.SatisfiedBy m18Table.semigroup.opposite := by
  constructor
  · intro valid
    exact (S5_254.basisFor.2 identity valid).sound m18BasisModelsOpposite
  · intro valid
    exact (S5_254.oppositeBasisFor.2 identity valid).sound m18OppositeBasisModels

theorem sameTheory6543_6605 (identity : Identity Nat) :
    identity.SatisfiedBy table6543.semigroup ↔ identity.SatisfiedBy table6605.semigroup := by
  rw [valid6543_iff_factors, valid6605_iff_factors, m18_valid_iff_opposite]

structure SameSignature (left right : Word Nat) : Prop where
  firstOrder : firstOccurrenceSequence left.toList = firstOccurrenceSequence right.toList
  m18 : S5_254.SameM18Signature left right

theorem leftRegularBand_valid_of_firstOrder (identity : Identity Nat)
    (order : firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList) :
    identity.SatisfiedBy fordTable.semigroup := by
  have leftNormal := lrbDerivesNormal identity.lhs
  have rightNormal := lrbDerivesNormal identity.rhs
  cases shape : firstOccurrenceSequence identity.lhs.toList with
  | nil =>
      have nonempty : firstOccurrenceSequence identity.lhs.toList ≠ [] := by
        cases identity.lhs with
        | mk head tail => simp [Word.toList, firstOccurrenceSequence]
      exact False.elim (nonempty shape)
  | cons head tail =>
      rw [shape] at leftNormal
      have rightShape := order.symm.trans shape
      rw [rightShape] at rightNormal
      exact (leftNormal.trans rightNormal.symm).sound leftRegularBandThreeBasis_models

theorem sameSignature_of_valid6543 (identity : Identity Nat)
    (valid : identity.SatisfiedBy table6543.semigroup) :
    SameSignature identity.lhs identity.rhs := by
  obtain ⟨fordValid, m18Valid⟩ := (valid6543_iff_factors identity).1 valid
  exact ⟨S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq identity fordValid,
    S5_254.sameM18Signature_of_valid identity m18Valid⟩

theorem valid6543_of_sameSignature (identity : Identity Nat)
    (same : SameSignature identity.lhs identity.rhs) :
    identity.SatisfiedBy table6543.semigroup := by
  apply (valid6543_iff_factors identity).2
  exact ⟨leftRegularBand_valid_of_firstOrder identity same.firstOrder,
    (S5_254.derivesOfSameM18Signature same.m18).sound S5_254.models⟩

theorem valid6543_iff_sameSignature (identity : Identity Nat) :
    identity.SatisfiedBy table6543.semigroup ↔ SameSignature identity.lhs identity.rhs :=
  ⟨sameSignature_of_valid6543 identity, valid6543_of_sameSignature identity⟩

theorem valid6605_iff_sameSignature (identity : Identity Nat) :
    identity.SatisfiedBy table6605.semigroup ↔ SameSignature identity.lhs identity.rhs :=
  (sameTheory6543_6605 identity).symm.trans (valid6543_iff_sameSignature identity)

abbrev cap2 := Msg0446TailBudget.cap 2

theorem cap2_eq_of_m18 {left right : Word Nat}
    (same : S5_254.SameM18Signature left right) (letter : Nat) :
    cap2 (left.toList.count letter) = cap2 (right.toList.count letter) := by
  apply (Msg0446TailBudget.cap_eq_iff 2 _ _).2
  refine ⟨?_, same.totalParity letter⟩
  have zeros : left.toList.count letter = 0 ↔ right.toList.count letter = 0 := by
    constructor
    · intro zero
      apply List.count_eq_zero.mpr
      intro member
      exact (List.count_eq_zero.mp zero) ((same.support letter).mpr member)
    · intro zero
      apply List.count_eq_zero.mpr
      intro member
      exact (List.count_eq_zero.mp zero) ((same.support letter).mp member)
  have ones : left.toList.count letter = 1 ↔ right.toList.count letter = 1 :=
    same.globallySimple letter
  by_cases zero : left.toList.count letter = 0
  · rw [zero, zeros.mp zero]
  · by_cases one : left.toList.count letter = 1
    · rw [one, ones.mp one]
    · have rightNotZero : right.toList.count letter ≠ 0 := fun h => zero (zeros.mpr h)
      have rightNotOne : right.toList.count letter ≠ 1 := fun h => one (ones.mpr h)
      omega

theorem SameSignature.counts {left right : Word Nat}
    (same : SameSignature left right) (letter : Nat) :
    cap2 (left.toList.count letter) = cap2 (right.toList.count letter) :=
  cap2_eq_of_m18 same.m18 letter

theorem derives_preserve_signature {left right : Word Nat}
    (derivation : Derives basis left right) : SameSignature left right :=
  sameSignature_of_valid6543 ⟨left, right⟩ (derivation.sound models6543)

theorem listDerives_preserve_caps {left right : List Nat}
    (derivation : S5_107.ListDerives basis left right) (letter : Nat) :
    cap2 (left.count letter) = cap2 (right.count letter) := by
  cases derivation with
  | empty => rfl
  | words wordDerivation => exact (derives_preserve_signature wordDerivation).counts letter

theorem listDerives_preserve_firstOrder {left right : List Nat}
    (derivation : S5_107.ListDerives basis left right) :
    firstOccurrenceSequence left = firstOccurrenceSequence right := by
  cases derivation with
  | empty => rfl
  | words wordDerivation => exact (derives_preserve_signature wordDerivation).firstOrder

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil
