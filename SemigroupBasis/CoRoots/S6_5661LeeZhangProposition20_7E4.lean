import SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4Completeness
import SemigroupBasis.Transfer

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4

open SemigroupBasis

/-! # Published E4 and catalogue S6_5661 endpoints -/

/-- The direct 64-law expansion of Lee--Zhang Proposition 20.7 is an
unrestricted identity basis for the exact published table E4. -/
theorem published_basis : BasisFor publishedTable.semigroup basis :=
  publishedBasisFor

namespace S6_5661

/-- The exact catalogue representative reached by the audited nontrivial
published-to-catalogue relabelling. -/
abbrev table : FiniteTable := catalogueTable

/-- Catalogue `S6_5661` inherits the published E4 identity theory through
the exact embedding `[0,2,1,3,4,5]`. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  published_basis.inheritAlongEmbedding
    publishedToCatalogueEmbedding catalogueModels

/-- The reversed Proposition 20.7 system is a basis for the opposite
catalogue representative. -/
theorem opposite_representative_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end S6_5661

end SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4
