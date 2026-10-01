import SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank058
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6Level2TierBHashE2c5e460
import SemigroupBasis.CoRoots.S5_804Completeness

/-!
# Exact parity/opposite-connected-cut boundary for authenticated rank 058

The immutable eleven-law owner basis is exactly the historical e2c basis with
its two genuinely invalid right-factor laws removed.  Neither the thirteen-law
e2c completeness theorem, the eight-law `S5_804` opposite completeness theorem,
nor the e2c protected `S5_442` replay can therefore be imported as an owner
proof.

The exact unrestricted missing obligation is a parity-preserving lift of the
complete opposite connected-cut normalizer.  This module proves that this
obligation is equivalent to the actual owner intersection and that the sole
authenticated class follows conditionally from that obligation.  It does not
assert the missing lift, owner completeness, kernel acceptance, or a seal.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank058.ParityConnectedCutDiagnostic

open SemigroupBasis
open SemigroupBasis.Examples

private def threeVariableValuation : Nat → Fin 5
  | 0 => 4
  | 1 => 2
  | _ => 3

private def guardedValuation : Nat → Fin 5
  | 0 => 2
  | 1 => 3
  | 3 => 4
  | _ => 0

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def componentIntoActualOppositeMap (value : Fin 4) : Fin 5 :=
  if value = 0 then 0 else
    if value = 1 then 1 else
      if value = 2 then 4 else 3

private def leftZeroIntoActualOppositeMap (value : Fin 2) : Fin 5 :=
  if value = 0 then 2 else 3

/-- The actual opposite factor contains the exact ordered four-state detector. -/
def componentIntoActualOpposite :
    Embedding connectedComponentFour.semigroup rightTable.semigroup where
  toFun := componentIntoActualOppositeMap
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- The same actual factor contains its independent first-letter detector. -/
def leftZeroIntoActualOpposite :
    Embedding leftZeroTwo.semigroup rightTable.semigroup where
  toFun := leftZeroIntoActualOppositeMap
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- Exact word reversal converts actual opposite-factor validity to `S5_804`. -/
theorem rightValidReversed
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.reversed.SatisfiedBy
      Generated.Catalogue.S5_804.table.semigroup := by
  change
    identity.SatisfiedBy
      Generated.Catalogue.S5_804.table.semigroup.opposite at valid
  exact (Identity.satisfiedBy_opposite_iff_reversed identity
    Generated.Catalogue.S5_804.table.semigroup).mp valid

/-- Right-factor validity fixes ALL reversed connected components and finals. -/
theorem oppositeConnectedCut_of_rightValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    S5_804.SameConnectedCutSignature
      identity.lhs.reverse identity.rhs.reverse :=
  S5_804.valid_sameConnectedCutSignature identity.reversed
    (rightValidReversed identity valid)

/-- Independent `S5_804` completeness makes the exact cut coordinate sufficient. -/
theorem rightValid_of_oppositeConnectedCut
    (identity : Identity Nat)
    (same : S5_804.SameConnectedCutSignature
      identity.lhs.reverse identity.rhs.reverse) :
    identity.SatisfiedBy rightTable.semigroup := by
  have reversedValid : identity.reversed.SatisfiedBy
      Generated.Catalogue.S5_804.table.semigroup :=
    (S5_804.derivesOfSameConnectedCutSignature same).sound
      S5_804.catalogueModels
  change identity.SatisfiedBy
    Generated.Catalogue.S5_804.table.semigroup.opposite
  exact (Identity.satisfiedBy_opposite_iff_reversed identity
    Generated.Catalogue.S5_804.table.semigroup).mpr reversedValid

/-- The left factor determines unrestricted occurrence parity. -/
theorem parity_of_leftValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    S5_442Invariant.SameOccurrenceParity identity.lhs identity.rhs := by
  have canonical : identity.SatisfiedBy parityZeroThree.semigroup := by
    rw [← S5_442Invariant.catalogueS3_11_table_eq_parityZeroThree]
    exact valid
  exact S5_442Invariant.sameOccurrenceParity_of_parityZeroThree_equalEval
    identity.lhs identity.rhs canonical

/-- Component support from the genuine right model closes the left converse. -/
theorem leftValid_of_parity_and_rightValid
    (identity : Identity Nat)
    (parity : S5_442Invariant.SameOccurrenceParity
      identity.lhs identity.rhs)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    identity.SatisfiedBy leftTable.semigroup := by
  have componentValid : identity.SatisfiedBy
      connectedComponentFour.semigroup :=
    componentIntoActualOpposite.pullback_identity identity rightValid
  have same : S5_442Invariant.SameParityComponentSignature
      identity.lhs identity.rhs :=
    ⟨S5_442Invariant.sameComponentSignature_of_connectedComponentFour_equalEval
        identity.lhs identity.rhs componentValid, parity⟩
  change identity.SatisfiedBy Generated.Catalogue.S3_11.table.semigroup
  rw [S5_442Invariant.catalogueS3_11_table_eq_parityZeroThree]
  exact S5_442Invariant.parityZeroThree_equalEval_of_sameSignature
    identity.lhs identity.rhs same

/-- The complete, width-free owner descriptor has no bounded-model premise. -/
structure SameParityOppositeConnectedCutSignature
    (left right : Word Nat) : Prop where
  parity : S5_442Invariant.SameOccurrenceParity left right
  cuts : S5_804.SameConnectedCutSignature left.reverse right.reverse

/-- Exact equivalence of the real two-factor identity theory and the descriptor. -/
theorem sameSignature_iff_factorValidity
    (identity : Identity Nat) :
    SameParityOppositeConnectedCutSignature identity.lhs identity.rhs ↔
      identity.SatisfiedBy leftTable.semigroup ∧
        identity.SatisfiedBy rightTable.semigroup := by
  constructor
  · intro same
    have rightValid := rightValid_of_oppositeConnectedCut identity same.cuts
    exact ⟨leftValid_of_parity_and_rightValid identity same.parity rightValid,
      rightValid⟩
  · rintro ⟨leftValid, rightValid⟩
    exact ⟨parity_of_leftValid identity leftValid,
      oppositeConnectedCut_of_rightValid identity rightValid⟩

/-- The actual factors also imply e2c's STRICTLY weaker guarded descriptor. -/
theorem coarseGuardedParityComponent_of_factorValidity
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Order6Level2TierBHashE2c5e460.SameGuardedParityComponentSignature
      identity.lhs identity.rhs := by
  have componentValid :=
    componentIntoActualOpposite.pullback_identity identity rightValid
  have firstValid :=
    leftZeroIntoActualOpposite.pullback_identity identity rightValid
  exact ⟨⟨S5_442Invariant.sameComponentSignature_of_connectedComponentFour_equalEval
      identity.lhs identity.rhs componentValid,
    parity_of_leftValid identity leftValid⟩,
    S5_790Invariant.leftZeroValid_head_eq identity firstValid⟩

/-- The immutable target is literally the eleven VALID e2c displayed laws. -/
theorem targetBasis_exactly_valid_e2c_laws :
    basis = [Order6Level2TierBHashE2c5e460.powerLaw,
      Order6Level2TierBHashE2c5e460.tripleLeftContractionLaw,
      Order6Level2TierBHashE2c5e460.endpointTransferLaw,
      Order6Level2TierBHashE2c5e460.splitEndpointContractionLaw,
      Order6Level2TierBHashE2c5e460.rightTripleExpansionLaw,
      Order6Level2TierBHashE2c5e460.xyxXYXYYLaw,
      Order6Level2TierBHashE2c5e460.xyxXYYXYLaw,
      Order6Level2TierBHashE2c5e460.xyxXYYYXLaw,
      Order6Level2TierBHashE2c5e460.alternatingLaw,
      Order6Level2TierBHashE2c5e460.attachmentLaw,
      Order6Level2TierBHashE2c5e460.componentSwapLaw] := by
  decide

/-- Honest route 1a: e2c's eleventh law is false on the ACTUAL right factor. -/
theorem e2cSquareTransfer_not_derivable :
    ¬ Derives basis
      Order6Level2TierBHashE2c5e460.guardedSquareTransferLaw.lhs
      Order6Level2TierBHashE2c5e460.guardedSquareTransferLaw.rhs := by
  intro derivation
  have evaluated := derivation.sound rightModels threeVariableValuation
  change (0 : Fin 5) = 1 at evaluated
  exact (by decide : (0 : Fin 5) ≠ 1) evaluated

/-- Honest route 1b: e2c's thirteenth law fails on the SAME exact valuation. -/
theorem e2cAlternatingTransfer_not_derivable :
    ¬ Derives basis
      Order6Level2TierBHashE2c5e460.guardedAlternatingTransferLaw.lhs
      Order6Level2TierBHashE2c5e460.guardedAlternatingTransferLaw.rhs := by
  intro derivation
  have evaluated := derivation.sound rightModels threeVariableValuation
  change (0 : Fin 5) = 1 at evaluated
  exact (by decide : (0 : Fin 5) ≠ 1) evaluated

/-- Therefore no sound retarget of the complete thirteen-law root exists. -/
theorem e2cFullBasisTransport_impossible :
    ¬ (∀ identity : Identity Nat,
      identity ∈ Order6Level2TierBHashE2c5e460.basis →
      Derives basis identity.lhs identity.rhs) := by
  intro transport
  exact e2cSquareTransfer_not_derivable
    (transport Order6Level2TierBHashE2c5e460.guardedSquareTransferLaw
      (by decide))

/-- Honest route 2: the complete right normalizer changes actual left parity. -/
theorem oppositeLowerPower_not_derivable :
    ¬ Derives basis
      S5_804.powerLaw.reversed.lhs
      S5_804.powerLaw.reversed.rhs := by
  intro derivation
  let valuation : Nat → Fin 3 := fun _ => 1
  have evaluated := derivation.sound leftModels valuation
  exact (by decide :
    leftTable.semigroup.eval valuation S5_804.powerLaw.reversed.lhs ≠
      leftTable.semigroup.eval valuation S5_804.powerLaw.reversed.rhs)
    evaluated

/-- No unguarded import of all eight independently complete opposite laws. -/
theorem oppositeLowerBasisTransport_impossible :
    ¬ (∀ identity : Identity Nat, identity ∈ S5_804.oppositeBasis →
      Derives basis identity.lhs identity.rhs) := by
  intro transport
  exact oppositeLowerPower_not_derivable
    (transport S5_804.powerLaw.reversed (by decide))

/-- Honest route 3: even e2c's protected S5_442 replay step is right-invalid. -/
theorem protectedParityNormalizerStep_not_derivable :
    ¬ Derives basis
      (Word.mk 3 [0, 0, 1, 0])
      (Word.mk 3 [1, 0, 1, 1]) := by
  intro derivation
  have evaluated := derivation.sound rightModels guardedValuation
  change (0 : Fin 5) = 1 at evaluated
  exact (by decide : (0 : Fin 5) ≠ 1) evaluated

/-- Consequently the historical unrestricted nonempty-prefix replay is false. -/
theorem protectedParityNormalizerTransport_impossible :
    ¬ (∀ {left right : Word Nat},
      Derives S5_442.basis left right →
        ∀ ctx : Word Nat,
          Derives basis (ctx ++ left) (ctx ++ right)) := by
  intro transport
  have lower : Derives S5_442.basis
      (Word.mk 0 [0, 1, 0]) (Word.mk 1 [0, 1, 1]) :=
    Derives.fromBasis (e := S5_442.xxyxYXYYLaw) (by decide)
  exact protectedParityNormalizerStep_not_derivable
    (transport lower (Word.singleton 3))

/-- The exact owner obligation: lift ONLY parity-preserving right derivations. -/
def ParityPreservingOppositeConnectedCutLift : Prop :=
  ∀ identity : Identity Nat,
    S5_442Invariant.SameOccurrenceParity identity.lhs identity.rhs →
      Derives S5_804.oppositeBasis identity.lhs identity.rhs →
        Derives basis identity.lhs identity.rhs

/-- Full reversed connected-cut equality provides an opposite lower proof. -/
theorem oppositeLowerDerivation_of_rightValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    Derives S5_804.oppositeBasis identity.lhs identity.rhs := by
  change identity.SatisfiedBy
    Generated.Catalogue.S5_804.table.semigroup.opposite at valid
  exact S5_804.oppositeBasisFor.2 identity valid

/-- Conversely a lower opposite derivation is sound on the ACTUAL factor. -/
theorem rightValid_of_oppositeLowerDerivation
    (identity : Identity Nat)
    (derivation :
      Derives S5_804.oppositeBasis identity.lhs identity.rhs) :
    identity.SatisfiedBy rightTable.semigroup := by
  change identity.SatisfiedBy
    Generated.Catalogue.S5_804.table.semigroup.opposite
  exact derivation.sound S5_804.catalogueOppositeModels

/-- Semantic reachability and the exact independent owner lift are equivalent. -/
theorem lift_iff_jointSignatureReach :
    ParityPreservingOppositeConnectedCutLift ↔
      (∀ {left right : Word Nat},
        SameParityOppositeConnectedCutSignature left right →
          Derives basis left right) := by
  constructor
  · intro lift left right same
    let identity : Identity Nat := ⟨left, right⟩
    have valid := rightValid_of_oppositeConnectedCut identity same.cuts
    exact lift identity same.parity
      (oppositeLowerDerivation_of_rightValid identity valid)
  · intro reach identity parity derivation
    have rightValid :=
      rightValid_of_oppositeLowerDerivation identity derivation
    exact reach ⟨parity,
      oppositeConnectedCut_of_rightValid identity rightValid⟩

/-- A GENUINELY independent lift closes the owner intersection, and nothing less. -/
def intersectionBasis_of_connectedCutLift
    (lift : ParityPreservingOppositeConnectedCutLift) :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := by
    intro identity leftValid rightValid
    exact lift identity (parity_of_leftValid identity leftValid)
      (oppositeLowerDerivation_of_rightValid identity rightValid)

/-- An independently supplied owner intersection supplies exactly this lift. -/
theorem connectedCutLift_of_intersectionBasis
    (intersection :
      IntersectionBasis leftTable.semigroup rightTable.semigroup basis) :
    ParityPreservingOppositeConnectedCutLift := by
  intro identity parity derivation
  have rightValid := rightValid_of_oppositeLowerDerivation identity derivation
  exact intersection.complete identity
    (leftValid_of_parity_and_rightValid identity parity rightValid)
    rightValid

/-- No fictitious normalizer or factor-separation premise is introduced. -/
theorem intersection_exists_iff_connectedCutLift :
    Nonempty (IntersectionBasis
      leftTable.semigroup rightTable.semigroup basis) ↔
      ParityPreservingOppositeConnectedCutLift := by
  constructor
  · rintro ⟨intersection⟩
    exact connectedCutLift_of_intersectionBasis intersection
  · intro lift
    exact ⟨intersectionBasis_of_connectedCutLift lift⟩

/-- The one class and both orientations remain STRICTLY conditional. -/
theorem both_orientations_of_connectedCutLift
    (lift : ParityPreservingOppositeConnectedCutLift) :
    BasisFor S6_11229.table.semigroup basis ∧
      BasisFor S6_11229.table.semigroup.opposite (reversedBasis basis) := by
  let intersection := intersectionBasis_of_connectedCutLift lift
  let normalizer :=
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
      intersection
  exact ⟨S6_11229.representative_basis_of_normalizer normalizer,
    S6_11229.opposite_basis_of_normalizer normalizer⟩

end SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank058.ParityConnectedCutDiagnostic
