import SemigroupBasis.CoRoots.S5_830

namespace SemigroupBasis.Generated.S5_830

open SemigroupBasis

/-- The canonical Smallsemi representative `S5_830`. -/
def table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_830.table

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S5_830.table :=
  rfl

theorem representative_basis :
    BasisFor table.semigroup
      SemigroupBasis.CoRoots.S5_830.basis := by
  simpa [table] using
    SemigroupBasis.CoRoots.S5_830.basis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_830.basis) := by
  simpa [table] using
    SemigroupBasis.CoRoots.S5_830.opposite_basis_complete

end SemigroupBasis.Generated.S5_830
