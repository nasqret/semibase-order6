import SemigroupBasis.CoRoots.S5_626
import SemigroupBasis.Examples.AffineParityFour

namespace SemigroupBasis.CoRoots.S5_626

open SemigroupBasis
open SemigroupBasis.Examples

/-- The two complete factor theories attached to a pair of words.  This is
strictly a factor certificate: neither derivation is transported to the
eleven-law basis of `S5_626`. -/
structure SameFactorDerivability (left right : Word Nat) : Prop where
  affine :
    Derives affineParityFourOppositeBasis left right
  initialMarker :
    Derives finalMarkerThreeOppositeBasis left right

/-- Completeness of `S4_96` opposite turns affine-factor validity into an
actual derivation in the factor basis. -/
theorem affineFactorDerivesOfValid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        affineParityFactorTable.semigroup.opposite) :
    Derives affineParityFourOppositeBasis
      identity.lhs identity.rhs := by
  apply affineParityFourOppositeBasis_complete.2 identity
  simpa [affineParityFour] using valid

/-- Completeness of `S3_6` opposite turns marker-factor validity into an
actual derivation in the factor basis. -/
theorem initialMarkerFactorDerivesOfValid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        initialMarkerFactorTable.semigroup.opposite) :
    Derives finalMarkerThreeOppositeBasis
      identity.lhs identity.rhs := by
  exact finalMarkerThreeOppositeBasis_complete.2 identity valid

/-- The split product and the two already-proved factor completeness
theorems give an exact derivability characterization of the identities of
`S5_626`.  The bases on the right are factor bases, not the candidate basis
of `S5_626`. -/
theorem valid_iff_factorDerivability
    (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      SameFactorDerivability identity.lhs identity.rhs := by
  constructor
  · intro valid
    have factors := (valid_iff_factors identity).1 valid
    exact
      ⟨affineFactorDerivesOfValid identity factors.1,
        initialMarkerFactorDerivesOfValid identity factors.2⟩
  · intro derivable
    apply (valid_iff_factors identity).2
    constructor
    · intro valuation
      have evaluated :=
        derivable.affine.sound
          affineParityFourOppositeBasis_complete.1 valuation
      simpa [affineParityFour] using evaluated
    · exact derivable.initialMarker.sound
        finalMarkerThreeOppositeBasis_complete.1

/-- Right-to-left affine markers on the reversed word, restored to the
left-to-right orientation of the original word.  These are the affine
factor's canonical first-occurrence coordinates. -/
def affineOppositeMarkers (word : Word Nat) : List Nat :=
  (affineParityMarkers
      (affineParityNormalSegments word.toList.reverse)).reverse

/-- The parity seen before the first occurrence of `marker`.  Reversal turns
this into suffix parity after the last occurrence in the affine normalizer.
The marker's own boundary coordinate is fixed to zero. -/
def affineOppositeBoundaryParity
    (word : Word Nat) (tested marker : Nat) : Nat :=
  if tested = marker then 0
  else affineParitySuffixParity tested marker word.toList.reverse

def affineOppositeFinalParity
    (word : Word Nat) (tested : Nat) : Nat :=
  word.toList.count tested % 2

/-- A fully combinatorial view of the information forced by the affine
factor.  It deliberately uses the affine normalizer's marker coordinates;
identifying these coordinates definitionally with the older
`FirstOccurrenceParityProfile` representation is a separate, pure list
lemma. -/
structure SameAffineOppositeCombinatorics
    (left right : Word Nat) : Prop where
  markers : affineOppositeMarkers left = affineOppositeMarkers right
  boundaryParity :
    ∀ tested marker,
      affineOppositeBoundaryParity left tested marker =
        affineOppositeBoundaryParity right tested marker
  finalParity :
    ∀ tested,
      affineOppositeFinalParity left tested =
        affineOppositeFinalParity right tested

private theorem affineOppositeMarkers_eq_of_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        affineParityFactorTable.semigroup.opposite) :
    affineOppositeMarkers identity.lhs =
      affineOppositeMarkers identity.rhs := by
  have directValid :
      identity.reversed.SatisfiedBy affineParityFour.semigroup := by
    apply (Identity.satisfiedBy_opposite_iff_reversed
      identity affineParityFour.semigroup).1
    simpa [affineParityFour] using valid
  have lhsNormal :=
    affineParityNormalSegments_normal identity.lhs.reverse.toList
  have rhsNormal :=
    affineParityNormalSegments_normal identity.rhs.reverse.toList
  have lhsDerives := affineParityDerivesNormal identity.lhs.reverse
  have rhsDerives := affineParityDerivesNormal identity.rhs.reverse
  cases lhsSegmentsEq :
      affineParityNormalSegments identity.lhs.reverse.toList with
  | nil =>
      exact False.elim <|
        affineParityNormalSegments_cons_ne_nil
          identity.lhs.reverse.head identity.lhs.reverse.tail <| by
            simpa only [Word.toList] using lhsSegmentsEq
  | cons lhsHead lhsRest =>
      cases rhsSegmentsEq :
          affineParityNormalSegments identity.rhs.reverse.toList with
      | nil =>
          exact False.elim <|
            affineParityNormalSegments_cons_ne_nil
              identity.rhs.reverse.head identity.rhs.reverse.tail <| by
                simpa only [Word.toList] using rhsSegmentsEq
      | cons rhsHead rhsRest =>
          rw [lhsSegmentsEq] at lhsNormal lhsDerives
          rw [rhsSegmentsEq] at rhsNormal rhsDerives
          have equalEval :
              ∀ valuation : Nat → Fin 4,
                affineParityListEval valuation
                    (affineParityRender (lhsHead :: lhsRest)) =
                  affineParityListEval valuation
                    (affineParityRender (rhsHead :: rhsRest)) := by
            intro valuation
            have lhsSound :=
              lhsDerives.sound affineParityFourBasis_models valuation
            have rhsSound :=
              rhsDerives.sound affineParityFourBasis_models valuation
            have evaluated := lhsSound.symm.trans <|
              (directValid valuation).trans rhsSound
            rw [affineParityEval_eq_listEval,
              affineParityEval_eq_listEval,
              affineParityRenderWord_toList,
              affineParityRenderWord_toList] at evaluated
            exact evaluated
          have markerEq :=
            affineParityMarkers_eq_of_eval_eq
              lhsNormal rhsNormal equalEval
          unfold affineOppositeMarkers
          rw [← Word.toList_reverse identity.lhs,
            ← Word.toList_reverse identity.rhs]
          rw [lhsSegmentsEq, rhsSegmentsEq, markerEq]

/-- Opposite affine validity determines marker order, every boundary parity,
and final parity. -/
theorem sameAffineOppositeCombinatorics_of_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        affineParityFactorTable.semigroup.opposite) :
    SameAffineOppositeCombinatorics identity.lhs identity.rhs := by
  have directValid :
      identity.reversed.SatisfiedBy affineParityFour.semigroup := by
    apply (Identity.satisfiedBy_opposite_iff_reversed
      identity affineParityFour.semigroup).1
    simpa [affineParityFour] using valid
  refine
    ⟨affineOppositeMarkers_eq_of_valid identity valid, ?_, ?_⟩
  · intro tested marker
    by_cases same : tested = marker
    · simp [affineOppositeBoundaryParity, same]
    · have parity :=
        affineParityValid_suffixParity
          identity.reversed directValid tested marker same
      simpa [affineOppositeBoundaryParity, same,
        Identity.reversed] using parity
  · intro tested
    have parity :=
      affineParityValid_totalParity
        identity.reversed directValid tested
    simpa [affineOppositeFinalParity,
      Identity.reversed] using parity

/-- The strongest factor-to-combinatorics bridge currently needed by the
normalizer.  The affine factor supplies all segmented parity data and the
marker factor supplies the simple-initial threshold bit. -/
structure SameSegmentedFactorSignature
    (left right : Word Nat) : Prop where
  affine : SameAffineOppositeCombinatorics left right
  initialOccursExactlyOnce :
    InitialOccursExactlyOnce left ↔
      InitialOccursExactlyOnce right

theorem sameSegmentedFactorSignature_of_factors
    (identity : Identity Nat)
    (affineValid :
      identity.SatisfiedBy
        affineParityFactorTable.semigroup.opposite)
    (initialValid :
      identity.SatisfiedBy
        initialMarkerFactorTable.semigroup.opposite) :
    SameSegmentedFactorSignature identity.lhs identity.rhs :=
  ⟨sameAffineOppositeCombinatorics_of_valid identity affineValid,
    sameInitialOccursExactlyOnce_of_valid_s3_6_opposite
      identity initialValid⟩

theorem valid_segmentedFactorSignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameSegmentedFactorSignature identity.lhs identity.rhs := by
  have factors := (valid_iff_factors identity).1 valid
  exact sameSegmentedFactorSignature_of_factors
    identity factors.1 factors.2

end SemigroupBasis.CoRoots.S5_626
