import SemigroupBasis.CoRoots.S5_345Completeness
import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.Generated.CatalogueOrder5Part03
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_345Family

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_345

namespace S5_345

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_345.table.semigroup basis :=
  modelsOfFiniteChecks Generated.Catalogue.S5_345.table (by decide)

theorem valid_signature (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_345.table.semigroup) :
    SameInitialSimpleTerminalSignature
      identity.lhs identity.rhs := by
  refine ⟨
    S5_345Factors.S5_345.valid_firstOccurrenceSequence_eq
      identity valid,
    ?_,
    S5_345Factors.S5_345.valid_simpleFinalVariable_eq
      identity valid⟩
  intro letter
  simpa [SemigroupBasis.CoRoots.S5_107.cappedMultiplicity,
    Nat.min_comm] using
    S5_345Factors.S5_345.valid_capped_count_eq
      identity valid letter

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_345.table.semigroup basis :=
  basis_complete_of_signature
    Generated.Catalogue.S5_345.table.semigroup
    models valid_signature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_345.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_345

namespace S5_374

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_374.table.semigroup basis :=
  modelsOfFiniteChecks Generated.Catalogue.S5_374.table (by decide)

theorem valid_signature (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_374.table.semigroup) :
    SameInitialSimpleTerminalSignature
      identity.lhs identity.rhs := by
  refine ⟨
    S5_345Factors.S5_374.valid_firstOccurrenceSequence_eq
      identity valid,
    ?_,
    S5_345Factors.S5_374.valid_simpleFinalVariable_eq
      identity valid⟩
  intro letter
  simpa [SemigroupBasis.CoRoots.S5_107.cappedMultiplicity,
    Nat.min_comm] using
    S5_345Factors.S5_374.valid_capped_count_eq
      identity valid letter

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_374.table.semigroup basis :=
  basis_complete_of_signature
    Generated.Catalogue.S5_374.table.semigroup
    models valid_signature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_374.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_374

namespace S5_593

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_593.table.semigroup basis :=
  modelsOfFiniteChecks Generated.Catalogue.S5_593.table (by decide)

theorem valid_signature (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_593.table.semigroup) :
    SameInitialSimpleTerminalSignature
      identity.lhs identity.rhs := by
  refine ⟨
    S5_345Factors.S5_593.valid_firstOccurrenceSequence_eq
      identity valid,
    ?_,
    S5_345Factors.S5_593.valid_simpleFinalVariable_eq
      identity valid⟩
  intro letter
  simpa [SemigroupBasis.CoRoots.S5_107.cappedMultiplicity,
    Nat.min_comm] using
    S5_345Factors.S5_593.valid_capped_count_eq
      identity valid letter

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_593.table.semigroup basis :=
  basis_complete_of_signature
    Generated.Catalogue.S5_593.table.semigroup
    models valid_signature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_593.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_593

end SemigroupBasis.CoRoots.S5_345Family
