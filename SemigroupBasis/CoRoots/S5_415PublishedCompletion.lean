import SemigroupBasis.CoRoots.S5_415SchutzenbergerImageCompletion

namespace SemigroupBasis.CoRoots.S5_415

open SemigroupBasis

/-- The paired normalized decomposition exists because the independent
Schutzenberger-image route proves the full derivational boundary. -/
def pairedNormalizedDecompositionCompleteness :
    PairedNormalizedDecompositionCompleteness :=
  pairedNormalizedDecomposition_of_derivationalCompleteness
    brandtDerivationalCompleteness

/-- Trahtman's three identities form a basis for the catalogue representative
`S5_415`. -/
theorem representative_basis :
    BasisFor Generated.Catalogue.S5_415.table.semigroup basis :=
  basis_complete_of_derivationalCompleteness
    brandtDerivationalCompleteness

/-- Reversing every identity gives a basis for the opposite semigroup. -/
theorem opposite_basis :
    BasisFor Generated.Catalogue.S5_415.table.semigroup.opposite
      (reversedBasis basis) :=
  opposite_basis_of_derivationalCompleteness
    brandtDerivationalCompleteness

end SemigroupBasis.CoRoots.S5_415
