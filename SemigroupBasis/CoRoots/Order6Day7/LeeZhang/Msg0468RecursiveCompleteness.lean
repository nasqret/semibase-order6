import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0468RecursiveSemantics
import SemigroupBasis.CoRoots.Order6Sunday.RecursiveThirdOccurrenceFinite
import SemigroupBasis.CoRoots.Order6Sunday.RecursiveObservationFinite

/-! Unconditional completeness for the literal S6_9726 table and its opposite.
The four fixed inputs are the exact S3 proofs recorded by carrier 21453303.
The previously proved arbitrary-word layer is reused without modification;
neither a finite screen nor an assumed completeness field is a premise. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Recursive9726

open SemigroupBasis Order6Sunday

theorem thirdTransport9726 : ThirdTransport :=
  RecursiveThirdOccurrenceFinite.thirdOccurrenceTransportFromB8

theorem observationControls9726 : ObservationControls where
  zeroLeft := RecursiveObservationFinite.zeroLeftControl
  nilStep := RecursiveObservationFinite.nilStepControl
  markerStep := RecursiveObservationFinite.markerStepControl

theorem complete9726 (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  complete_of_fixed_interface thirdTransport9726 observationControls9726 identity valid

theorem representative_basis9726 : BasisFor table.semigroup basis :=
  ⟨RecursiveDepth7Delta.S6_9726.tableModels, complete9726⟩

theorem opposite_basis9726 :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis9726.oppositeReversed

theorem valid_iff_signature9726 (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      PrefixCount.SameCapsThree identity.lhs.toList identity.rhs.toList ∧
      PrefixCount.SameBeforeTwo identity.lhs.toList identity.rhs.toList := by
  constructor
  · intro valid
    exact ⟨sameCapsThree_of_valid observationControls9726 identity valid,
      sameBeforeTwo_of_valid observationControls9726 identity valid⟩
  · rintro ⟨counts, prefixes⟩
    exact Derives.sound representative_basis9726.1
      (derivesOfSameSignature thirdTransport9726 counts prefixes)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Recursive9726
