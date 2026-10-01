import SemigroupBasis.ChainReplay
import SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank020
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.Order6Level2TierBHashE2c5e460
import SemigroupBasis.CoRoots.S5_806Completeness

/-!
# Unrestricted cyclic-two / S5_806 rank-020 seed

The frozen rank-020 basis is the same literal thirteen-law B13 used by the
independently owner-recorded S3_11 rank-020 proof.  The historical e2c root
already proves the genuine cyclic-two / S5_798 source intersection.  Duality
therefore supplies a certified cyclic-two-opposite / S5_798-opposite seed.

The one-way right-factor transport is genuinely unrestricted: the COMPLETE
eight-law S5_806 owner basis derives every S5_806-valid identity, and all
eight laws are independently satisfied by the actual S5_798 opposite table.
This is not a finite-table inference of arbitrary factor theories.

All thirteen reversed e2c laws receive individually typed frozen-B13
derivations.  Twelve are single checked edges; the attachment law is four
independently checked edges with all intermediate words explicit.  The
reviewed kernel-green `transportNormalizer` then yields exactly the S2-owned
S6_8865 representative and opposite endpoints.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank020.Seed

open SemigroupBasis

private def word (first : Nat) (rest : List Nat) : Word Nat :=
  Word.mk first rest

private def fixedStep
    (lawIndex : Nat) (direction : ChainReplay.Direction)
    (leftContext rightContext : List Nat)
    (substitution : List (List Nat)) : ChainReplay.Chain Nat :=
  [{lawIndex, direction, leftContext, rightContext, substitution}]

private def unchanged : List (List Nat) := [[0], [1], [2]]

/-- Historical `xx = xxxx`, literally reversed into frozen law 00. -/
theorem reversedSourceLaw00 :
    Derives basis
      Order6Level2TierBHashE2c5e460.powerLaw.reversed.lhs
      Order6Level2TierBHashE2c5e460.powerLaw.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 0 .forward [] [] unchanged) (by decide)

theorem reversedSourceLaw01 :
    Derives basis
      Order6Level2TierBHashE2c5e460.tripleLeftContractionLaw.reversed.lhs
      Order6Level2TierBHashE2c5e460.tripleLeftContractionLaw.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 5 .backward [] [] unchanged) (by decide)

theorem reversedSourceLaw02 :
    Derives basis
      Order6Level2TierBHashE2c5e460.endpointTransferLaw.reversed.lhs
      Order6Level2TierBHashE2c5e460.endpointTransferLaw.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 2 .backward [] [] unchanged) (by decide)

theorem reversedSourceLaw03 :
    Derives basis
      Order6Level2TierBHashE2c5e460.splitEndpointContractionLaw.reversed.lhs
      Order6Level2TierBHashE2c5e460.splitEndpointContractionLaw.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 3 .forward [] [] unchanged) (by decide)

theorem reversedSourceLaw04 :
    Derives basis
      Order6Level2TierBHashE2c5e460.rightTripleExpansionLaw.reversed.lhs
      Order6Level2TierBHashE2c5e460.rightTripleExpansionLaw.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 1 .backward [] [] unchanged) (by decide)

theorem reversedSourceLaw05 :
    Derives basis
      Order6Level2TierBHashE2c5e460.xyxXYXYYLaw.reversed.lhs
      Order6Level2TierBHashE2c5e460.xyxXYXYYLaw.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 8 .forward [] [] unchanged) (by decide)

theorem reversedSourceLaw06 :
    Derives basis
      Order6Level2TierBHashE2c5e460.xyxXYYXYLaw.reversed.lhs
      Order6Level2TierBHashE2c5e460.xyxXYYXYLaw.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 7 .forward [] [] unchanged) (by decide)

theorem reversedSourceLaw07 :
    Derives basis
      Order6Level2TierBHashE2c5e460.xyxXYYYXLaw.reversed.lhs
      Order6Level2TierBHashE2c5e460.xyxXYYYXLaw.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 6 .forward [] [] unchanged) (by decide)

theorem reversedSourceLaw08 :
    Derives basis
      Order6Level2TierBHashE2c5e460.alternatingLaw.reversed.lhs
      Order6Level2TierBHashE2c5e460.alternatingLaw.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 9 .forward [] [] [[1], [0], [2]]) (by decide)

/-- `yzxyx -> yxzyx`, retaining the protected final `x`. -/
theorem attachmentEdge00 :
    Derives basis (word 1 [2, 0, 1, 0]) (word 1 [0, 2, 1, 0]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 12 .forward [] [0] [[1], [2], [0]]) (by decide)

/-- `yxzyx -> yxyzx`, retaining the protected initial `y`. -/
theorem attachmentEdge01 :
    Derives basis (word 1 [0, 2, 1, 0]) (word 1 [0, 1, 2, 0]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 12 .forward [1] [] [[0], [2], [1]]) (by decide)

/-- `yxyzx -> xyyzx`, using the actual frozen law 11. -/
theorem attachmentEdge02 :
    Derives basis (word 1 [0, 1, 2, 0]) (word 0 [1, 1, 2, 0]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 11 .forward [] [] [[1], [0], [2]]) (by decide)

/-- `xyyzx -> xzyyx`, with the genuine composite substitution `yy`. -/
theorem attachmentEdge03 :
    Derives basis (word 0 [1, 1, 2, 0]) (word 0 [2, 1, 1, 0]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 12 .forward [] [] [[0], [1, 1], [2]]) (by decide)

/-- The sole nontrivial reversed source law has four typed checked edges. -/
theorem reversedSourceLaw09 :
    Derives basis
      Order6Level2TierBHashE2c5e460.attachmentLaw.reversed.lhs
      Order6Level2TierBHashE2c5e460.attachmentLaw.reversed.rhs :=
  attachmentEdge00.trans
    (attachmentEdge01.trans (attachmentEdge02.trans attachmentEdge03))

theorem reversedSourceLaw10 :
    Derives basis
      Order6Level2TierBHashE2c5e460.guardedSquareTransferLaw.reversed.lhs
      Order6Level2TierBHashE2c5e460.guardedSquareTransferLaw.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 4 .backward [] [] [[2], [1], [0]]) (by decide)

theorem reversedSourceLaw11 :
    Derives basis
      Order6Level2TierBHashE2c5e460.componentSwapLaw.reversed.lhs
      Order6Level2TierBHashE2c5e460.componentSwapLaw.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 12 .forward [] [] [[0], [2], [1]]) (by decide)

theorem reversedSourceLaw12 :
    Derives basis
      Order6Level2TierBHashE2c5e460.guardedAlternatingTransferLaw.reversed.lhs
      Order6Level2TierBHashE2c5e460.guardedAlternatingTransferLaw.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 10 .forward [] [] [[2], [1], [0]]) (by decide)

/-- Every literal reversed e2c axiom derives from the frozen S2 B13 basis. -/
theorem reversedSourceAxiomsDeriveFrozen
    (identity : Identity Nat)
    (member : identity ∈ reversedBasis Order6Level2TierBHashE2c5e460.basis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [Order6Level2TierBHashE2c5e460.basis, reversedBasis,
    List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact reversedSourceLaw00
  · exact reversedSourceLaw01
  · exact reversedSourceLaw02
  · exact reversedSourceLaw03
  · exact reversedSourceLaw04
  · exact reversedSourceLaw05
  · exact reversedSourceLaw06
  · exact reversedSourceLaw07
  · exact reversedSourceLaw08
  · exact reversedSourceLaw09
  · exact reversedSourceLaw10
  · exact reversedSourceLaw11
  · exact reversedSourceLaw12

/-- The actual historical cyclic-two factor is strictly self-opposite. -/
theorem sourceCyclicSelfDual :
    SemigroupBasis.Generated.S2_2.table.semigroup.opposite =
      SemigroupBasis.Generated.S2_2.table.semigroup := by
  unfold SemigroupBasis.Generated.S2_2.table
    FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext first second
  apply Fin.ext
  decide +revert

/-- The frozen S2 cyclic factor supplies actual historical opposite validity. -/
theorem targetLeftTheoryImpliesSourceOpposite
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    identity.SatisfiedBy
      SemigroupBasis.Generated.S2_2.table.semigroup.opposite := by
  rw [sourceCyclicSelfDual]
  change
    identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup at valid
  rw [SemigroupBasis.CoRoots.S5_442Invariant.catalogueS2_2_table_eq_cyclicTwo]
    at valid
  rw [SemigroupBasis.Generated.S2_2.table_eq_catalogue_model]
  exact valid

/-- All eight complete S5_806 owner axioms hold on actual S5_798-opposite.
Only these eight closed finite instances use `decide`; no arbitrary identity
or unrestricted factor implication is inferred by table reflection. -/
theorem sourceRightOppositeModelsCompleteLowerBasis :
    Models
      SemigroupBasis.Generated.Catalogue.S5_798.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_806.basis := by
  change
    Models
      (SemigroupBasis.Order6Subdirect.oppositeTable
        SemigroupBasis.Generated.Catalogue.S5_798.table).semigroup
      SemigroupBasis.CoRoots.S5_806.basis
  exact
    SemigroupBasis.CoRoots.S5_806.models_of_finite_checks
      (SemigroupBasis.Order6Subdirect.oppositeTable
        SemigroupBasis.Generated.Catalogue.S5_798.table)
      (by decide)

/-- Every S5_806-valid identity transfers to S5_798-opposite using the
COMPLETE eight-law lower owner proof and soundness of its derivation. -/
theorem targetRightTheoryImpliesSourceOpposite
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_798.table.semigroup.opposite := by
  have catalogueValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_806.table.semigroup := by
    simpa [rightTable] using valid
  have completeDerivation :
      Derives SemigroupBasis.CoRoots.S5_806.basis
        identity.lhs identity.rhs :=
    SemigroupBasis.CoRoots.S5_806.basisFor.2 identity catalogueValid
  intro valuation
  exact completeDerivation.sound
    sourceRightOppositeModelsCompleteLowerBasis valuation

/-- Duality of the already-proved historical cyclic/S5_798 intersection. -/
def historicalOppositeIntersection :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_798.table.semigroup.opposite
      (reversedBasis Order6Level2TierBHashE2c5e460.basis) :=
  Order6Level2TierBHashE2c5e460.intersectionBasisS2_2S5_798.oppositeReversed

/-- The target factor intersection is genuinely complete before any target
quotient normalization; all finite law witnesses and both one-way semantic
transports remain explicit. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have sourceDerivation :=
    historicalOppositeIntersection.complete identity
      (targetLeftTheoryImpliesSourceOpposite identity leftValid)
      (targetRightTheoryImpliesSourceOpposite identity rightValid)
  exact sourceDerivation.transport reversedSourceAxiomsDeriveFrozen

def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derivesOfFactorValid

/-- Quotient normalization is applied only to the pre-existing, complete
historical source intersection; never to an unproved target field. -/
noncomputable def historicalSourceNormalizer :
    IntersectionNormalizer
      SemigroupBasis.Generated.S2_2.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_798.table.semigroup.opposite
      (reversedBasis Order6Level2TierBHashE2c5e460.basis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    historicalOppositeIntersection

/-- Literal reuse of the reviewed, kernel-green owner transport normalizer. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    historicalSourceNormalizer
    reversedSourceAxiomsDeriveFrozen
    targetLeftTheoryImpliesSourceOpposite
    targetRightTheoryImpliesSourceOpposite

/-- The sole S2-owned rank-020 representative endpoint. -/
theorem s6_8865_representative_basis :
    BasisFor S6_8865.table.semigroup basis :=
  S6_8865.representative_basis_of_normalizer normalizer

/-- The S2-owned opposite endpoint, with the literal reversed B13 basis. -/
theorem s6_8865_opposite_basis :
    BasisFor S6_8865.table.semigroup.opposite (reversedBasis basis) :=
  S6_8865.opposite_basis_of_normalizer normalizer

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank020.Seed
