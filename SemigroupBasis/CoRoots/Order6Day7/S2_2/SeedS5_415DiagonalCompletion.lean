import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_415ParityCoordinates

/-!
# Rank040: complete intrinsic diagonal and Brandt/parity lifts

Actual exposure corners, regular closed-return absorption, and the C2
coordinate theorem supply the PRECISE existing DiagonalParityLift. The
previous two-inverse reduction then gives unrestricted pair completeness.

All four class endpoints below have NO owner premise. This is a proof
source, not an independent carrier receipt, acceptance or seal. The
frozen fifteen-law basis and both accepted design refutations are unchanged.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.DiagonalCompletion

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_415
open ExposureReplay ExposureCorners ClosedReturnReplay HeadRetargetBoundary
open NormalizedInverse RepeatedCellRegularity BrandtParityBridge DiagonalComparison
open RegularLoopModel ParityCoordinates

/-- Decode a sound Brandt signature into its actual graph path data.
This is only semantic necessity; it does NOT supply a derivation. -/
theorem closedReturnOfPrefixSignature {word loop : Word Nat}
    (same : SameBrandtSignature word ((loop ++ loop) ++ word)) : ClosedReturnWord word loop := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro letter member
    apply (same.1 letter).mpr
    simp only [Word.toList_append, List.mem_append]
    exact Or.inl (Or.inl member)
  · exact (incomingHeads_connected_of_sameBrandtSignature same).symm
  · intro first second member
    apply (brandtEndpointConnected_iff_of_sameBrandtSignature same _ _).mpr
    apply BrandtEndpointConnected.adjacency
    simp only [Word.adjacentPairs_append, List.mem_append, List.mem_cons]
    exact Or.inl (Or.inl member)
  · apply (brandtEndpointConnected_iff_of_sameBrandtSignature same _ _).mpr
    apply BrandtEndpointConnected.adjacency
    simp only [Word.adjacentPairs_append, Word.final_append, List.mem_append, List.mem_cons]
    exact Or.inr (Or.inl True.intro)

theorem closedReturnOfRightEquality {word loop : Word Nat}
    (equal : (Identity.mk word loop).SatisfiedBy Rank040.rightTable.semigroup)
    (diagonal : DiagonalBrandt word) : ClosedReturnWord word loop := by
  apply closedReturnOfPrefixSignature
  apply valid_sameBrandtSignature (identity := Identity.mk word ((loop ++ loop) ++ word))
  intro valuation
  have same := equal valuation
  have idempotent := diagonal valuation
  change Rank040.rightTable.semigroup.mul
    (Rank040.rightTable.semigroup.eval valuation word)
    (Rank040.rightTable.semigroup.eval valuation word) = _ at idempotent
  change Rank040.rightTable.semigroup.eval valuation word =
    Rank040.rightTable.semigroup.eval valuation ((loop ++ loop) ++ word)
  simp only [Semigroup.eval_append]
  rw [← same, idempotent, idempotent]

theorem closedReturnOfDiagonal {word : Word Nat} (diagonal : DiagonalBrandt word) :
    ClosedReturnWord word word := closedReturnOfRightEquality (fun _ => rfl) diagonal

/-- The exact formerly-open field, proved without replacing its intrinsic
signature by an ambient graph class and without inventing a common inverse. -/
theorem diagonalParityLift : DiagonalParityLift := by
  intro left right leftRegular rightRegular same even diagonal
  obtain ⟨leftWitness⟩ := leftRegular
  obtain ⟨rightWitness⟩ := rightRegular
  have rightEven := zeroParityOfSignature same even
  have rightDiagonal := diagonalBrandtOfSignature same diagonal
  have leftClosed := closedReturnOfDiagonal diagonal
  have rightClosed := closedReturnOfDiagonal rightDiagonal
  have leftIdempotent := zeroParityClosedWord_idempotent leftWitness leftClosed even
  have rightIdempotent := zeroParityClosedWord_idempotent rightWitness rightClosed rightEven
  have leftContracts := zeroParityClosedWord_idempotentDerives leftWitness leftClosed even
  have rightContracts := zeroParityClosedWord_idempotentDerives rightWitness rightClosed rightEven
  have equal := rightValid_of_sameBrandtSignature (Identity.mk left right) same.brandt
  have forward := regularClosedReturnDerivation leftWitness (closedReturnOfRightEquality equal diagonal)
  have backward := regularClosedReturnDerivation rightWitness
    (closedReturnOfRightEquality (fun valuation => (equal valuation).symm) rightDiagonal)
  have commute : Derives Rank040.basis (right ++ left) (left ++ right) :=
    (termClass_eq_iff_derives Rank040.basis).mp
      (modelIdempotentsCommute G (termSemigroup_models Rank040.basis) rightIdempotent leftIdempotent)
  exact (forward.trans (Derives.appendRight rightContracts left)).trans
    (commute.trans (backward.trans (Derives.appendRight leftContracts right)).symm)

theorem completeRegularPairLift : RegularPairParityLift :=
  regularPairParityLift_of_diagonalParityLift diagonalParityLift

theorem fullBrandtParityLift : BrandtParityLift :=
  brandtParityLift_iff_diagonalParityLift.mpr diagonalParityLift

theorem fullClosedReturnDerivation : ClosedReturnDerivation :=
  closedReturnDerivation_of_brandtParityLift fullBrandtParityLift

theorem fullEvenClosedReturnDerivation : EvenCoverage.EvenClosedReturnDerivation :=
  EvenCoverage.evenClosedReturnDerivation_iff.mpr fullClosedReturnDerivation

def completeIntersection :
    IntersectionBasis Rank040.leftTable.semigroup Rank040.rightTable.semigroup Rank040.basis :=
  intersectionBasis_of_ownerLift fullBrandtParityLift

noncomputable def completeNormalizer :
    IntersectionNormalizer Rank040.leftTable.semigroup Rank040.rightTable.semigroup Rank040.basis :=
  normalizer_of_ownerLift fullBrandtParityLift

theorem s6_4103_representative_basis : BasisFor Rank040.S6_4103.table.semigroup Rank040.basis :=
  s6_4103_representative_basis_of_ownerLift fullBrandtParityLift

theorem s6_4103_opposite_basis :
    BasisFor Rank040.S6_4103.table.semigroup.opposite (reversedBasis Rank040.basis) :=
  s6_4103_opposite_basis_of_ownerLift fullBrandtParityLift

theorem s6_4309_representative_basis : BasisFor Rank040.S6_4309.table.semigroup Rank040.basis :=
  s6_4309_representative_basis_of_ownerLift fullBrandtParityLift

theorem s6_4309_opposite_basis :
    BasisFor Rank040.S6_4309.table.semigroup.opposite (reversedBasis Rank040.basis) :=
  s6_4309_opposite_basis_of_ownerLift fullBrandtParityLift

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.DiagonalCompletion
