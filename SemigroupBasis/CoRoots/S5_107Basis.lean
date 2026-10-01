import SemigroupBasis.CoRoots.S5_107Completeness
import SemigroupBasis.CoRoots.S5_107Normalization
import SemigroupBasis.CoRoots.S5_107SignatureSemantics

namespace SemigroupBasis.CoRoots.S5_107Family

open SemigroupBasis

namespace S5_107

/-- The published `S5_107` identities form an identity basis for the
catalogue semigroup `S5_107`. -/
theorem basisFor :
    BasisFor Generated.Catalogue.S5_107.table.semigroup
      SemigroupBasis.CoRoots.S5_107.basis :=
  SemigroupBasis.CoRoots.S5_107.basis_complete_of_signature
    Generated.Catalogue.S5_107.table.semigroup
    models
    SemigroupBasis.CoRoots.S5_107.valid_sameSimpleAdjacencySignature
    SemigroupBasis.CoRoots.S5_107.derivesCanonicalUnrestricted
    SemigroupBasis.CoRoots.S5_107.SameSimpleAdjacencySignature.canonicalWord_eq

end S5_107

namespace S5_108

/-- The same published identities form an identity basis for the
catalogue semigroup `S5_108`. -/
theorem basisFor :
    BasisFor Generated.Catalogue.S5_108.table.semigroup
      SemigroupBasis.CoRoots.S5_107.basis :=
  SemigroupBasis.CoRoots.S5_107.basis_complete_of_signature
    Generated.Catalogue.S5_108.table.semigroup
    models
    SemigroupBasis.CoRoots.S5_108.valid_sameSimpleAdjacencySignature
    SemigroupBasis.CoRoots.S5_107.derivesCanonicalUnrestricted
    SemigroupBasis.CoRoots.S5_107.SameSimpleAdjacencySignature.canonicalWord_eq

/-- The reversed basis is complete for the opposite orientation of the
non-self-dual catalogue class `S5_108`. -/
theorem oppositeBasisFor :
    BasisFor Generated.Catalogue.S5_108.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_107.basis) :=
  basisFor.oppositeReversed

end S5_108

namespace S5_109

/-- The same published identities form an identity basis for the
catalogue semigroup `S5_109`. -/
theorem basisFor :
    BasisFor Generated.Catalogue.S5_109.table.semigroup
      SemigroupBasis.CoRoots.S5_107.basis :=
  SemigroupBasis.CoRoots.S5_107.basis_complete_of_signature
    Generated.Catalogue.S5_109.table.semigroup
    models
    SemigroupBasis.CoRoots.S5_109.valid_sameSimpleAdjacencySignature
    SemigroupBasis.CoRoots.S5_107.derivesCanonicalUnrestricted
    SemigroupBasis.CoRoots.S5_107.SameSimpleAdjacencySignature.canonicalWord_eq

end S5_109

end SemigroupBasis.CoRoots.S5_107Family
