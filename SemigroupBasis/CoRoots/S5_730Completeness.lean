import SemigroupBasis.CoRoots.S5_730Normalization

namespace SemigroupBasis.CoRoots.S5_730

open SemigroupBasis

/-- Words with the exact `S5_730` semantic signature are derivably
equal in the three-law basis. -/
theorem derivesOfSameSignature
    {left right : Word Nat}
    (same : S5_730Invariant.SameSignature left right) :
    Derives basis left right := by
  have reversedDerivation :
      Derives S5_851.basis left.reverse right.reverse :=
    S5_851.derivesOfHeadSupportFinalSignature
      (sameSignature_reversed same)
  have returned := reversedDerivation.reverse
  have transported :=
    transportReversedS5_851Derivation returned
  simpa using transported

end SemigroupBasis.CoRoots.S5_730
