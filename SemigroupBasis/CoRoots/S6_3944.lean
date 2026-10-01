import SemigroupBasis.CoRoots.S6_3944Completeness

namespace SemigroupBasis.CoRoots.S6_3944

open SemigroupBasis

/-! ## Unconditional catalogue endpoints -/

/-- Lee--Li Proposition 4.3 is a basis for the exact direct Smallsemi
representative `S6_3944`. -/
theorem representative_basis :
    BasisFor table.semigroup basis :=
  basis_complete

/-- Catalogue-facing spelling of the direct representative endpoint. -/
theorem catalogue_basis :
    BasisFor catalogueTable.semigroup basis :=
  representative_basis

/-- The same literal Lee--Li basis for their printed Q1 table, transported
through the certified relabelling `[1,5,4,3,2,6]`. -/
theorem published_basis :
    BasisFor publishedTable.semigroup basis :=
  (basisFor_iff_of_sameIdentityTheoryOver
    sameIdentityTheory_published).mpr representative_basis

/-- The same basis in the campaign route's certified opposite orientation. -/
theorem route_basis :
    BasisFor routeTable.semigroup basis :=
  (basisFor_iff_of_sameIdentityTheoryOver
    sameIdentityTheory_route).mp representative_basis

/-- Reversing every displayed word gives a basis for the opposite of the
direct catalogue representative. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  rw [← reversedBasis_basis]
  exact representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.S6_3944
