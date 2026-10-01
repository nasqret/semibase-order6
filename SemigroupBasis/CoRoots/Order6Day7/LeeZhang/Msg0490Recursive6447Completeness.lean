import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0484Recursive6447Semantics
import SemigroupBasis.CoRoots.Order6Sunday.Recursive6447Fixed

/-! Unconditional completeness for the actual S6_6447 table and its opposite.
The four exact finite inputs are S3's unchanged proofs from carrier 21572231.
The established arbitrary-word layer is reused without an unproved field
or a bounded screen as a premise. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Recursive6447

open SemigroupBasis Order6Sunday

theorem fixedSwaps6447 : FixedSwaps where
  squareCommute := Recursive6447Fixed.squareCommuteFromB12
  mixedEmptyPrefix := Recursive6447Fixed.mixedEmptyPrefixFromB12

theorem observationControls6447 : ObservationControls where
  highStep := Recursive6447Fixed.highStepControl
  lowStep := Recursive6447Fixed.lowStepControl

theorem complete6447 (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  complete_of_fixed_interface fixedSwaps6447 observationControls6447 identity valid

theorem representative_basis6447 : BasisFor table.semigroup basis :=
  ⟨RecursiveDepth7Delta.S6_6447.tableModels, complete6447⟩

theorem opposite_basis6447 :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis6447.oppositeReversed

theorem valid_iff_signature6447 (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      SimplePrefix.CappedSignature identity.lhs.toList.reverse identity.rhs.toList.reverse := by
  constructor
  · intro valid
    exact signature_of_valid observationControls6447 identity valid
  · intro same
    exact Derives.sound representative_basis6447.1 (derivesOfSameSignature fixedSwaps6447 same)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Recursive6447
