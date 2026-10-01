import SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Alignment

/-! Unrestricted completeness of the exact approved S6598 B25. The actual
sorted separator skeleton and anchored cap-two banks close SignatureReach.
No finite bound, sampled identity, or unproved reach field is a premise. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Completeness

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day7.LeeZhang
open Msg0456S6598Semantics Msg0456S6598Rewrites Msg0456S6598Signature
open Msg0456S6598Assembly Msg0456S6598Alignment

theorem listDerives_preserve_caps {left right : List Nat} (derivation : LD left right) :
    CapTwoGuardedBank.SameCaps left right := by
  cases derivation with
  | empty => exact fun _ => rfl
  | words proof => exact (derives_preserve_signature proof).counts

def bankRules : CapTwoGuardedBank.Rules basis where
  centralPair := fun stem letter payload seen =>
    transportFordList (FordNil.listDerivesPairAcrossSeen stem payload letter seen)
  appendPairAtTwo := fun letters letter repeated =>
    transportFordList (FordNil.listDerivesAppendPairOfCountGeTwo letters letter repeated)
  preservesCounts := listDerives_preserve_caps

/-- All arbitrary nonempty words with equal counts/preS/bL signatures are
connected by actual B25 derivations. -/
theorem derivesOfSameSignature {left right : Word Nat} (same : SameSignature left right) :
    Derives basis left right := by
  obtain ⟨leftLabels, leftDerivation, leftCounts, leftSeen⟩ := rawAssembly left
  obtain ⟨rightLabels, rightDerivation, rightCounts, rightSeen⟩ := rawAssembly right
  have skeletonEq := separatorSkeleton_eq_of_sameSignature same
  rw [← skeletonEq] at rightDerivation rightCounts rightSeen
  have capped : CapTwoGuardedBank.SameCaps
      (separatorSkeleton left ++ S5_254.renderSquareBank leftLabels)
      (separatorSkeleton left ++ S5_254.renderSquareBank rightLabels) := by
    intro tested
    rw [leftCounts tested, rightCounts tested]
    exact same.counts tested
  have middle := CapTwoGuardedBank.align bankRules (separatorSkeleton left)
    leftLabels rightLabels leftSeen rightSeen capped
  have derived := leftDerivation.trans (middle.trans rightDerivation.symm)
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail => exact S5_107.ListDerives.toWord derived

theorem signatureReach : SignatureReach :=
  fun _ _ same => derivesOfSameSignature same

theorem complete (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameSignature (sameSignature_of_valid identity valid)

theorem representative_basis : BasisFor table.semigroup basis :=
  basisFor_iff_signatureReach.mpr signatureReach

theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

theorem derives_iff_signature (left right : Word Nat) :
    Derives basis left right ↔ SameSignature left right :=
  ⟨derives_preserve_signature, derivesOfSameSignature⟩

end SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Completeness
