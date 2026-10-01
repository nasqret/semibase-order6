import SemigroupBasis.CoRoots.S5_348Invariant
import SemigroupBasis.CoRoots.S5_381Normalization

namespace SemigroupBasis.CoRoots.S5_348

open SemigroupBasis
open SemigroupBasis.Examples

/-- Unrestricted normalization for the exact seven-law basis. The explicit
first-gap/final signature is converted to the established reversed
last-gap/initial signature, normalized there, reversed back, and finally
transported through the proved seven-law bridge. -/
theorem derives_of_sameSimpleSequenceFirstGapFinalSignature
    {left right : Word Nat}
    (same :
      S5_348Invariant.SameSimpleSequenceFirstGapFinalSignature
        left right) :
    Derives basis left right := by
  have dual :
      S5_381Invariant.SameSimpleSequenceLastGapInitialSignature
        left.reverse right.reverse :=
    SimpleSequenceFirstGap.SameSignature.toDual same
  have dualDerivation :
      Derives SemigroupBasis.CoRoots.S5_381.basis
        left.reverse right.reverse :=
    SemigroupBasis.CoRoots.S5_381.derives_of_sameSimpleSequenceLastGapInitialSignature
      dual
  have reversed :
      Derives (reversedBasis SemigroupBasis.CoRoots.S5_381.basis)
        left right := by
    simpa using dualDerivation.reverse
  exact transportReversedS5_381Derivation reversed

end SemigroupBasis.CoRoots.S5_348
