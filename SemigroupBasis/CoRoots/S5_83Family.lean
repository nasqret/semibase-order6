import SemigroupBasis.CoRoots.S5_83Factors

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_83Family

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_83

namespace S5_83

open SemigroupBasis.CoRoots.S5_83Factors.S5_83

theorem models :
    Models Generated.Catalogue.S5_83.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_83.table (by decide)

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_83.table.semigroup basis :=
  basis_complete_of_terminalUniqueSuffix
    Generated.Catalogue.S5_83.table.semigroup models
    valid_signature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_83.table.semigroup.opposite
      oppositeBasis :=
  basis_complete.oppositeReversed

end S5_83

namespace S5_84

open SemigroupBasis.CoRoots.S5_83Factors.S5_84

theorem models :
    Models Generated.Catalogue.S5_84.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_84.table (by decide)

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_84.table.semigroup basis :=
  basis_complete_of_terminalUniqueSuffix
    Generated.Catalogue.S5_84.table.semigroup models
    valid_signature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_84.table.semigroup.opposite
      oppositeBasis :=
  basis_complete.oppositeReversed

end S5_84

end SemigroupBasis.CoRoots.S5_83Family
