import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002SiblingTransport
import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.Examples.AffineParityFour

/-!
# Exact rank-004 affine collision obligation and protected rewrites

The surviving `S3_16 × S4_96` and owner-attested recovered `S3_16 × S5_997`
shells share the immutable twelve-law basis.  This module proves the actual
semantic coordinates, four useful protected affine rewrites, and an exact
equivalence between independent unrestricted intersection completeness and
the missing first-occurrence-preserving affine lift.

The unrestricted lift is NOT constructed.  A concrete four-letter witness
shows why first-occurrence order, last-occurrence order, and even the entire
multiplicity vector do not suffice: affine suffix parity remains essential.
Every class endpoint below retains an explicit independent owner seed.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.AffineOwnerDiagnostic

open SemigroupBasis
open SemigroupBasis.Examples

private def instantiateTwo
    (first second : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | letter + 2 => Word.singleton (letter + 2)

/-- The actual frozen left table is exactly the standard LRB detector. -/
def canonicalLeftIntoActual :
    Embedding leftRegularBandThree.semigroup leftTable.semigroup where
  toFun := fun value => value
  map_mul := by
    intro first second
    apply Fin.ext
    revert first second
    decide
  injective := by
    intro first second equality
    exact equality

/-- The reverse identity embedding avoids assuming definitional table equality. -/
def actualLeftIntoCanonical :
    Embedding leftTable.semigroup leftRegularBandThree.semigroup where
  toFun := fun value => value
  map_mul := by
    intro first second
    apply Fin.ext
    revert first second
    decide
  injective := by
    intro first second equality
    exact equality

/-- The opposite three-element regular band occurs on actual affine states
`[2,0,3]`, so the right factor detects reverse first-occurrence order. -/
def oppositeLeftIntoAffine :
    Embedding leftRegularBandThree.semigroup.opposite rightTable.semigroup where
  toFun := fun (value : Fin 3) =>
    if value = 0 then (2 : Fin 4)
    else if value = 1 then (0 : Fin 4)
    else (3 : Fin 4)
  map_mul := by
    intro first second
    apply Fin.ext
    revert first second
    decide
  injective := by
    intro first second equality
    revert first second
    decide

theorem oppositeLeftIntoAffine_values :
    List.ofFn (fun value : Fin 3 =>
      (oppositeLeftIntoAffine.toFun value).val) = [2, 0, 3] := by
  decide

/-- Genuine frozen-left validity fixes the entire first-occurrence sequence. -/
theorem firstOccurrences_of_leftValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
    identity (canonicalLeftIntoActual.pullback_identity identity valid)

/-- First-occurrence equality is also sufficient for frozen-left validity. -/
theorem leftValid_of_firstOccurrences
    (identity : Identity Nat)
    (same : firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList) :
    identity.SatisfiedBy leftTable.semigroup := by
  have firstNormal := lrbDerivesNormal identity.lhs
  have secondNormal := lrbDerivesNormal identity.rhs
  cases normalShape : firstOccurrenceSequence identity.lhs.toList with
  | nil =>
      cases identity.lhs with
      | mk head tail =>
          simp [Word.toList, firstOccurrenceSequence] at normalShape
  | cons head tail =>
      have secondShape :
          firstOccurrenceSequence identity.rhs.toList = head :: tail :=
        same.symm.trans normalShape
      rw [normalShape] at firstNormal
      rw [secondShape] at secondNormal
      have canonicalValid :=
        (firstNormal.trans secondNormal.symm).sound
          leftRegularBandThreeBasis_models
      exact actualLeftIntoCanonical.pullback_identity
        identity canonicalValid

/-- Genuine affine validity fixes reverse first-occurrence order as well. -/
theorem reverseFirstOccurrences_of_rightValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    firstOccurrenceSequence identity.lhs.reverse.toList =
      firstOccurrenceSequence identity.rhs.reverse.toList := by
  have oppositeValid :=
    oppositeLeftIntoAffine.pullback_identity identity valid
  have reversedValid :=
    (Identity.satisfiedBy_opposite_iff_reversed
      identity leftRegularBandThree.semigroup).mp oppositeValid
  simpa [Identity.reversed] using
    SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      identity.reversed reversedValid

/-- Affine validity retains total period-two multiplicities. -/
theorem totalParity_of_rightValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    ∀ tested,
      identity.lhs.toList.count tested % 2 =
        identity.rhs.toList.count tested % 2 := by
  have affineValid : identity.SatisfiedBy affineParityFour.semigroup := by
    simpa [rightTable, affineParityFour] using valid
  exact affineParityValid_totalParity identity affineValid

/-- The missing owner-normalizer coordinate is suffix parity after EVERY
last marker, not just global parity or the two endpoint orders. -/
theorem suffixParity_of_rightValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    ∀ tested marker, tested ≠ marker →
      affineParitySuffixParity tested marker identity.lhs.toList =
        affineParitySuffixParity tested marker identity.rhs.toList := by
  have affineValid : identity.SatisfiedBy affineParityFour.semigroup := by
    simpa [rightTable, affineParityFour] using valid
  exact affineParityValid_suffixParity identity affineValid

/-- The frozen period-two law expands any nonempty word to its cube. -/
theorem derivesTripleExpansion (word : Word Nat) :
    Derives basis word ((word ++ word) ++ word) := by
  have literal :=
    Derives.fromBasis (basis := basis) (e := law00) (by decide)
  change Derives basis (Word.mk 0 []) (Word.mk 0 [0, 0]) at literal
  have substituted :=
    Derives.subst literal (instantiateTwo word word)
  simpa [instantiateTwo, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

/-- Once both variables appear in order `xy`, reverse frozen law 01 gives
the otherwise invalid affine square-return axiom under that exact guard. -/
theorem derivesSquareReturnUnderXY
    (first second : Word Nat) :
    Derives basis
      (((((first ++ second) ++ first) ++ first) ++ second) ++ first)
      (((first ++ second) ++ second) ++ first) := by
  have literal :=
    Derives.fromBasis (basis := basis) (e := law01) (by decide)
  change Derives basis (Word.mk 0 [0, 1]) (Word.mk 0 [1, 1, 0, 1]) at literal
  have substituted :=
    Derives.subst literal (instantiateTwo second first)
  simpa [instantiateTwo, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using
      Derives.prepend first substituted.symm

/-- Under the opposite `yx` guard, frozen power alone contracts the return. -/
theorem derivesSquareReturnUnderYX
    (first second : Word Nat) :
    Derives basis
      (((((second ++ first) ++ first) ++ first) ++ second) ++ first)
      (((second ++ first) ++ second) ++ first) := by
  have contracted :=
    Derives.prepend second (derivesTripleExpansion first).symm
  simpa [Word.append_assoc] using
    Derives.appendRight contracted (second ++ first)

/-- Reverse frozen law 02 gives the middle-square affine axiom after `xy`. -/
theorem derivesMiddleSquareUnderXY
    (first second : Word Nat) :
    Derives basis
      (((((first ++ second) ++ first) ++ second) ++ second) ++ first)
      (((((first ++ second) ++ second) ++ first) ++ second) ++ first) := by
  have literal :=
    Derives.fromBasis (basis := basis) (e := law02) (by decide)
  change Derives basis (Word.mk 0 [0, 1, 0, 1])
    (Word.mk 0 [1, 0, 0, 1]) at literal
  have substituted :=
    Derives.subst literal (instantiateTwo second first)
  simpa [instantiateTwo, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using
      Derives.prepend first substituted.symm

/-- Frozen law 03 gives the same middle-square axiom after `yx`. -/
theorem derivesMiddleSquareUnderYX
    (first second : Word Nat) :
    Derives basis
      (((((second ++ first) ++ first) ++ second) ++ second) ++ first)
      (((((second ++ first) ++ second) ++ first) ++ second) ++ first) := by
  have literal :=
    Derives.fromBasis (basis := basis) (e := law03) (by decide)
  change Derives basis (Word.mk 0 [0, 1, 1, 0])
    (Word.mk 0 [1, 0, 1, 0]) at literal
  have substituted :=
    Derives.subst literal (instantiateTwo first second)
  simpa [instantiateTwo, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using
      Derives.prepend second substituted

/-- This is the exact remaining unrestricted owner obligation, with no
bounded alphabet, finite-window hypothesis, or fabricated normalizer. -/
def FirstOccurrencePreservingAffineLift : Prop :=
  ∀ identity : Identity Nat,
    firstOccurrenceSequence identity.lhs.toList =
        firstOccurrenceSequence identity.rhs.toList →
      Derives affineParityFourBasis identity.lhs identity.rhs →
        Derives basis identity.lhs identity.rhs

/-- A genuine independent lift would immediately give the complete frozen
intersection; no quotient normalization is used before this implication. -/
def intersectionBasis_of_affineLift
    (lift : FirstOccurrencePreservingAffineLift) :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := by
    intro identity leftValid rightValid
    have affineValid : identity.SatisfiedBy affineParityFour.semigroup := by
      simpa [rightTable, affineParityFour] using rightValid
    exact lift identity
      (firstOccurrences_of_leftValid identity leftValid)
      (affineParityFourBasis_complete.2 identity affineValid)

/-- Conversely any independently proved owner intersection solves exactly
that unrestricted first-order-preserving affine derivation problem. -/
theorem affineLift_of_intersectionBasis
    (intersection :
      IntersectionBasis leftTable.semigroup rightTable.semigroup basis) :
    FirstOccurrencePreservingAffineLift := by
  intro identity same affineDerivation
  have affineValid : identity.SatisfiedBy affineParityFour.semigroup :=
    affineDerivation.sound affineParityFourBasis_models
  have rightValid : identity.SatisfiedBy rightTable.semigroup := by
    simpa [rightTable, affineParityFour] using affineValid
  exact intersection.complete identity
    (leftValid_of_firstOccurrences identity same) rightValid

/-- The collision is unrestrictedly closable IFF the named affine reach
obligation is actually discharged; this theorem does not discharge it. -/
theorem intersection_exists_iff_affineLift :
    Nonempty
      (IntersectionBasis leftTable.semigroup rightTable.semigroup basis) ↔
      FirstOccurrencePreservingAffineLift := by
  constructor
  · rintro ⟨intersection⟩
    exact affineLift_of_intersectionBasis intersection
  · intro lift
    exact ⟨intersectionBasis_of_affineLift lift⟩

/-- The smallest strict-profile witness: `xxyx = xyxx`. -/
def suffixParityCounterexample : Identity Nat :=
  ⟨Word.mk 0 [0, 1, 0], Word.mk 0 [1, 0, 0]⟩

theorem counterexample_firstOccurrences :
    firstOccurrenceSequence suffixParityCounterexample.lhs.toList =
      firstOccurrenceSequence suffixParityCounterexample.rhs.toList := by
  decide

theorem counterexample_reverseFirstOccurrences :
    firstOccurrenceSequence suffixParityCounterexample.lhs.reverse.toList =
      firstOccurrenceSequence suffixParityCounterexample.rhs.reverse.toList := by
  decide

/-- The witness even preserves EXACT variable multiplicities, not merely parity. -/
theorem counterexample_counts (letter : Nat) :
    suffixParityCounterexample.lhs.toList.count letter =
      suffixParityCounterexample.rhs.toList.count letter := by
  have permutation :
      suffixParityCounterexample.lhs.toList.Perm
        suffixParityCounterexample.rhs.toList := by
    decide
  exact (List.perm_iff_count.mp permutation) letter

theorem counterexample_suffixParity_ne :
    affineParitySuffixParity 0 1 suffixParityCounterexample.lhs.toList ≠
      affineParitySuffixParity 0 1 suffixParityCounterexample.rhs.toList := by
  decide

theorem counterexample_left_valid :
    suffixParityCounterexample.SatisfiedBy leftTable.semigroup :=
  leftValid_of_firstOccurrences suffixParityCounterexample
    counterexample_firstOccurrences

/-- Initial/final order plus even the exact count vector misses the affine
boundary coordinate; the actual right states `x=1,y=2` refute the identity. -/
theorem counterexample_right_not_valid :
    ¬ suffixParityCounterexample.SatisfiedBy rightTable.semigroup := by
  intro valid
  let valuation : Nat → Fin 4 :=
    fun letter => if letter = 0 then 1 else 2
  have evaluated := valid valuation
  change (3 : Fin 4) = 2 at evaluated
  exact (by decide : (3 : Fin 4) ≠ 2) evaluated

theorem counterexample_not_derivable :
    ¬ Derives basis
      suffixParityCounterexample.lhs suffixParityCounterexample.rhs := by
  intro derivation
  exact counterexample_right_not_valid
    (derivation.sound rightModels)

/-- Attempt 1: the naked complete affine square-return changes LRB initials. -/
theorem unguardedAffineSquareReturn_not_derivable :
    ¬ Derives basis (Word.mk 0 [0, 1, 0]) (Word.mk 1 [0]) := by
  intro derivation
  let valuation : Nat → Fin 3 :=
    fun letter => if letter = 0 then 0 else 2
  have evaluated := derivation.sound leftModels valuation
  change (0 : Fin 3) = 2 at evaluated
  exact (by decide : (0 : Fin 3) ≠ 2) evaluated

/-- Attempt 2: the kernel-green C3 proof's single fresh initial guard does
not protect the first appearances of the two affine variables. -/
theorem singleFreshGuardSquareReturn_not_derivable :
    ¬ Derives basis
      (Word.mk 2 [0, 0, 1, 0]) (Word.mk 2 [1, 0]) := by
  intro derivation
  let valuation : Nat → Fin 3 :=
    fun letter => if letter = 0 then 0 else if letter = 1 then 2 else 1
  have evaluated := derivation.sound leftModels valuation
  change (0 : Fin 3) = 2 at evaluated
  exact (by decide : (0 : Fin 3) ≠ 2) evaluated

/-- Doubling the same fresh guard does not repair the C3 shortcut. -/
theorem doubleFreshGuardSquareReturn_not_derivable :
    ¬ Derives basis
      (Word.mk 2 [2, 0, 0, 1, 0]) (Word.mk 2 [2, 1, 0]) := by
  intro derivation
  let valuation : Nat → Fin 3 :=
    fun letter => if letter = 0 then 0 else if letter = 1 then 2 else 1
  have evaluated := derivation.sound leftModels valuation
  change (0 : Fin 3) = 2 at evaluated
  exact (by decide : (0 : Fin 3) ≠ 2) evaluated

/-- Attempt 3: any period-one C1 block normalizer contradicts the actual
period-two affine state `1`. -/
theorem periodOnePower_not_derivable :
    ¬ Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) := by
  intro derivation
  have evaluated := derivation.sound rightModels (fun _ => (1 : Fin 4))
  change (0 : Fin 4) = 1 at evaluated
  exact (by decide : (0 : Fin 4) ≠ 1) evaluated

/-- The C1 first/last/count shortcut is independently false by the exact
four-letter affine suffix-parity counterexample. -/
theorem endpointOrderAndCounts_not_complete :
    ¬ (∀ identity : Identity Nat,
      firstOccurrenceSequence identity.lhs.toList =
          firstOccurrenceSequence identity.rhs.toList →
        firstOccurrenceSequence identity.lhs.reverse.toList =
          firstOccurrenceSequence identity.rhs.reverse.toList →
        (∀ letter,
          identity.lhs.toList.count letter =
            identity.rhs.toList.count letter) →
        Derives basis identity.lhs identity.rhs) := by
  intro complete
  exact counterexample_not_derivable
    (complete suffixParityCounterexample
      counterexample_firstOccurrences
      counterexample_reverseFirstOccurrences
      counterexample_counts)

/-- The immutable owner transport makes all three classes conditional on
the SINGLE precise affine lift; none is asserted without that input. -/
theorem all_three_collision_classes_of_affineLift
    (lift : FirstOccurrencePreservingAffineLift) :
    BasisFor S6_14895.table.semigroup basis ∧
      BasisFor S6_14895.table.semigroup.opposite (reversedBasis basis) ∧
      BasisFor
        Rank004Pair002Recovered.S6_14887.table.semigroup
        Rank004Pair002Recovered.basis ∧
      BasisFor
        Rank004Pair002Recovered.S6_14887.table.semigroup.opposite
        (reversedBasis Rank004Pair002Recovered.basis) ∧
      BasisFor
        Rank004Pair002Recovered.S6_14888.table.semigroup
        Rank004Pair002Recovered.basis ∧
      BasisFor
        Rank004Pair002Recovered.S6_14888.table.semigroup.opposite
        (reversedBasis Rank004Pair002Recovered.basis) := by
  let owner := intersectionBasis_of_affineLift lift
  let normalizer :=
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
      owner
  exact
    ⟨S6_14895.representative_basis_of_normalizer normalizer,
      S6_14895.opposite_basis_of_normalizer normalizer,
      Rank004Pair002SiblingTransport.recovered_representative_basis_S6_14887 owner,
      Rank004Pair002SiblingTransport.recovered_opposite_basis_S6_14887 owner,
      Rank004Pair002SiblingTransport.recovered_representative_basis_S6_14888 owner,
      Rank004Pair002SiblingTransport.recovered_opposite_basis_S6_14888 owner⟩

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.AffineOwnerDiagnostic
