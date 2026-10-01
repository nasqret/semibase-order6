import SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SigmaPlus
import SemigroupBasis.Examples.CyclicThree
import SemigroupBasis.Generated.S4_69
import SemigroupBasis.Normalization.OneLocalFordLord

/-!
# Rank006: exact unrestricted residue-and-separator semantics

The C3 factor records every multiplicity modulo three.  The S4_69 factor
records its independently complete canonical separator segments.  Their
product is an exact semantic descriptor on arbitrary Nat-words.  It is NOT
the first/last-occurrence profile: the original law xxyy = yxxy already
refutes the historical Ford/Lord necessity shortcut.

No lower-factor derivation below is relabelled as a Sigma+ derivation.
The remaining S1 obligation is exactly equality of this descriptor =>
Sigma+ derivability. The positively reviewed Sigma+ has thirteen laws;
the raw12 predecessor's incompleteness theorem remains unchanged.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Semantics

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SigmaPlus

theorem leftTable_eq_cyclicThree : leftTable = cyclicThree := by
  unfold leftTable Rank006Shape.leftTable Generated.Catalogue.S3_18.table cyclicThree
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext first second
  decide +revert

theorem rightTable_eq_uniqueSeparatorFour :
    rightTable = uniqueSeparatorFour :=
  Generated.S4_69.table_eq_canonical_catalogue.symm

/-- A mod-three equality yields a derivation in the C3 calculus only. -/
theorem cyclicDerivesOfModEq (identity : Identity Nat)
    (modEq : ∀ letter,
      identity.lhs.toList.count letter % 3 =
        identity.rhs.toList.count letter % 3) :
    Derives cyclicThreeBasis identity.lhs identity.rhs := by
  have reducedPerm :
      (ternaryReduce identity.lhs.toList).Perm
        (ternaryReduce identity.rhs.toList) :=
    ternaryReduce_perm_of_mod_eq modEq
  have leftNormal := cyclicThreeDerivesNormal identity.lhs
  have rightNormal := cyclicThreeDerivesNormal identity.rhs
  cases leftShape : ternaryReduce identity.lhs.toList with
  | nil =>
      rw [leftShape] at reducedPerm
      have rightShape : ternaryReduce identity.rhs.toList = [] :=
        reducedPerm.nil_eq.symm
      rw [leftShape] at leftNormal
      rw [rightShape] at rightNormal
      exact leftNormal.trans
        ((cyclicThreeDerivesCommonCube
          (Word.singleton identity.lhs.head)
          (Word.singleton identity.rhs.head)).trans rightNormal.symm)
  | cons first rest =>
      cases rightShape : ternaryReduce identity.rhs.toList with
      | nil =>
          rw [leftShape, rightShape] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons other otherRest =>
          rw [leftShape] at leftNormal
          rw [rightShape] at rightNormal
          rw [leftShape, rightShape] at reducedPerm
          exact leftNormal.trans
            ((cyclicThreeDerivesPermutation
              (Word.mk first rest) (Word.mk other otherRest)
              reducedPerm).trans rightNormal.symm)

theorem leftValid_iff_mod_eq (identity : Identity Nat) :
    identity.SatisfiedBy leftTable.semigroup ↔
      ∀ letter, identity.lhs.toList.count letter % 3 =
        identity.rhs.toList.count letter % 3 := by
  rw [leftTable_eq_cyclicThree]
  constructor
  · exact cyclicThreeValid_mod_eq identity
  · intro modEq
    exact (cyclicDerivesOfModEq identity modEq).sound cyclicThreeBasis_models

/-- The fallback is unreachable, since every canonical render is nonempty. -/
def separatorNormalWord (word : Word Nat) : Word Nat :=
  match uniqueSeparatorFourNormalRender word with
  | [] => word
  | first :: rest => Word.mk first rest

theorem separatorNormalizationWitness (word : Word Nat) :
    ∃ first rest,
      uniqueSeparatorFourNormalRender word = first :: rest ∧
        Derives uniqueSeparatorFourBasis word (Word.mk first rest) := by
  cases word with
  | mk first rest =>
      exact (uniqueSeparatorFour_derivesNormal (Word.mk first rest)).from_cons

theorem separatorNormalWord_toList (word : Word Nat) :
    (separatorNormalWord word).toList =
      uniqueSeparatorFourNormalRender word := by
  obtain ⟨first, rest, shape, _⟩ := separatorNormalizationWitness word
  simp only [separatorNormalWord, shape, Word.toList]

/-- This normalization uses the independent seven-law S4_69 basis, not raw12. -/
theorem separatorDerivesNormalWord (word : Word Nat) :
    Derives uniqueSeparatorFourBasis word (separatorNormalWord word) := by
  obtain ⟨first, rest, shape, derivation⟩ := separatorNormalizationWitness word
  simpa only [separatorNormalWord, shape] using derivation

theorem rightValid_normalSegments_eq (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    uniqueSeparatorFourNormalSegments identity.lhs =
      uniqueSeparatorFourNormalSegments identity.rhs := by
  rw [rightTable_eq_uniqueSeparatorFour] at valid
  apply uniqueSeparatorCanonical_eq_of_equalEval
    (uniqueSeparatorFourNormalSegments_canonical identity.lhs)
    (uniqueSeparatorFourNormalSegments_canonical identity.rhs)
    (separatorNormalWord identity.lhs) (separatorNormalWord identity.rhs)
  · exact separatorNormalWord_toList identity.lhs
  · exact separatorNormalWord_toList identity.rhs
  · intro valuation
    have leftSound := (separatorDerivesNormalWord identity.lhs).sound
      uniqueSeparatorFourBasis_models valuation
    have rightSound := (separatorDerivesNormalWord identity.rhs).sound
      uniqueSeparatorFourBasis_models valuation
    exact leftSound.symm.trans ((valid valuation).trans rightSound)

theorem rightValid_iff_normalSegments_eq (identity : Identity Nat) :
    identity.SatisfiedBy rightTable.semigroup ↔
      uniqueSeparatorFourNormalSegments identity.lhs =
        uniqueSeparatorFourNormalSegments identity.rhs := by
  constructor
  · exact rightValid_normalSegments_eq identity
  · intro sameSegments
    have sameWords : separatorNormalWord identity.lhs =
        separatorNormalWord identity.rhs := by
      apply Word.toList_injective
      rw [separatorNormalWord_toList, separatorNormalWord_toList]
      exact congrArg uniqueSeparatorCanonicalRender sameSegments
    have first := separatorDerivesNormalWord identity.lhs
    rw [sameWords] at first
    have lower : Derives uniqueSeparatorFourBasis identity.lhs identity.rhs :=
      first.trans (separatorDerivesNormalWord identity.rhs).symm
    rw [rightTable_eq_uniqueSeparatorFour]
    exact lower.sound uniqueSeparatorFourBasis_models

structure Descriptor where
  residues : Nat → Nat
  separatorSegments : List UniqueSeparatorCanonicalSegment

def descriptor (word : Word Nat) : Descriptor where
  residues := fun letter => word.toList.count letter % 3
  separatorSegments := uniqueSeparatorFourNormalSegments word

/-- Exact semantic characterization, with no alphabet or length restriction. -/
theorem factor_valid_iff_descriptor_eq (identity : Identity Nat) :
    (identity.SatisfiedBy leftTable.semigroup ∧
      identity.SatisfiedBy rightTable.semigroup) ↔
      descriptor identity.lhs = descriptor identity.rhs := by
  constructor
  · rintro ⟨leftValid, rightValid⟩
    have sameResidues := funext ((leftValid_iff_mod_eq identity).mp leftValid)
    have sameSegments := (rightValid_iff_normalSegments_eq identity).mp rightValid
    unfold descriptor
    rw [sameResidues, sameSegments]
  · intro same
    have sameResidues := congrArg Descriptor.residues same
    have sameSegments := congrArg Descriptor.separatorSegments same
    exact ⟨(leftValid_iff_mod_eq identity).mpr (fun letter => congrFun sameResidues letter),
      (rightValid_iff_normalSegments_eq identity).mpr sameSegments⟩

theorem derives_descriptor_eq {left right : Word Nat}
    (derivation : Derives sigmaPlus left right) :
    descriptor left = descriptor right :=
  (factor_valid_iff_descriptor_eq (Identity.mk left right)).mp
    (derives_factor_valid derivation)

/-- Exactly the remaining owner proof, separated from semantic necessity. -/
theorem complete_iff_descriptor_reach :
    Complete ↔ ∀ left right : Word Nat,
      descriptor left = descriptor right → Derives sigmaPlus left right := by
  constructor
  · intro complete left right same
    have factors :=
      (factor_valid_iff_descriptor_eq (Identity.mk left right)).mpr same
    exact complete (Identity.mk left right) factors.1 factors.2
  · intro reach identity leftValid rightValid
    exact reach identity.lhs identity.rhs
      ((factor_valid_iff_descriptor_eq identity).mp ⟨leftValid, rightValid⟩)

/-- Raw law 06 changes first-occurrence order although both factors validate it. -/
def profileCounterexample : Identity Nat :=
  ⟨Word.mk 0 [0, 1, 1], Word.mk 1 [0, 0, 1]⟩

theorem profileCounterexample_member : profileCounterexample ∈ sigmaPlus := by decide

theorem profileCounterexample_factor_valid :
    profileCounterexample.SatisfiedBy leftTable.semigroup ∧
      profileCounterexample.SatisfiedBy rightTable.semigroup :=
  ⟨modelsLeft _ profileCounterexample_member, modelsRight _ profileCounterexample_member⟩

theorem profileCounterexample_first_order_ne :
    firstOccurrenceSequence profileCounterexample.lhs.toList ≠
      firstOccurrenceSequence profileCounterexample.rhs.toList := by decide

theorem profileCounterexample_profile_ne :
    OneLocalFordLord.profile 2 3 profileCounterexample.lhs ≠
      OneLocalFordLord.profile 2 3 profileCounterexample.rhs := by
  intro same
  exact profileCounterexample_first_order_ne
    (congrArg OneLocalFordLord.Profile.ford same)

/-- The historical generated Ford/Lord wrapper has an impossible necessity
premise for this route. It is separate from the preserved raw12 falsification. -/
theorem fordLordProfileNecessaryImpossible :
    ¬ (∀ identity : Identity Nat,
      identity.SatisfiedBy leftTable.semigroup →
      identity.SatisfiedBy rightTable.semigroup →
      OneLocalFordLord.profile 2 3 identity.lhs =
        OneLocalFordLord.profile 2 3 identity.rhs) := by
  intro necessary
  exact profileCounterexample_profile_ne
    (necessary profileCounterexample
      profileCounterexample_factor_valid.1 profileCounterexample_factor_valid.2)

end SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Semantics
