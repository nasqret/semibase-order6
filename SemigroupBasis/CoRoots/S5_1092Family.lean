import SemigroupBasis.CoRoots.S5_1092Factors

namespace SemigroupBasis.CoRoots.S5_1092Family

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_1092

namespace S5_1092

open SemigroupBasis.CoRoots.S5_1092Factors.S5_1092

set_option maxRecDepth 100000 in
theorem models :
    Models SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup basis :=
  models_of_finite_checks
    SemigroupBasis.Generated.Catalogue.S5_1092.table (by decide)

theorem basis_complete :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup basis :=
  basis_complete_of_occurrence_separation
    SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup models fun e valid =>
    ⟨valid_firstOccurrenceSequence_eq e valid,
      valid_lastOccurrenceSequence_eq e valid⟩

theorem opposite_basis_complete :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup.opposite
      oppositeBasis :=
  basis_complete.oppositeReversed

end S5_1092

namespace S5_1135

open SemigroupBasis.CoRoots.S5_1092Factors.S5_1135

set_option maxRecDepth 100000 in
theorem models :
    Models SemigroupBasis.Generated.Catalogue.S5_1135.table.semigroup basis :=
  models_of_finite_checks
    SemigroupBasis.Generated.Catalogue.S5_1135.table (by decide)

theorem basis_complete :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1135.table.semigroup basis :=
  basis_complete_of_occurrence_separation
    SemigroupBasis.Generated.Catalogue.S5_1135.table.semigroup models fun e valid =>
    ⟨valid_firstOccurrenceSequence_eq e valid,
      valid_lastOccurrenceSequence_eq e valid⟩

theorem opposite_basis_complete :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_1135.table.semigroup.opposite
      oppositeBasis :=
  basis_complete.oppositeReversed

end S5_1135

namespace S5_1144

open SemigroupBasis.CoRoots.S5_1092Factors.S5_1144

set_option maxRecDepth 100000 in
theorem models :
    Models SemigroupBasis.Generated.Catalogue.S5_1144.table.semigroup basis :=
  models_of_finite_checks
    SemigroupBasis.Generated.Catalogue.S5_1144.table (by decide)

theorem basis_complete :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1144.table.semigroup basis :=
  basis_complete_of_occurrence_separation
    SemigroupBasis.Generated.Catalogue.S5_1144.table.semigroup models fun e valid =>
    ⟨valid_firstOccurrenceSequence_eq e valid,
      valid_lastOccurrenceSequence_eq e valid⟩

theorem opposite_basis_complete :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_1144.table.semigroup.opposite
      oppositeBasis :=
  basis_complete.oppositeReversed

def selfDualEmbedding :
    Embedding
      SemigroupBasis.Generated.Catalogue.S5_1144.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_1144.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then (0 : Fin 5)
    else if a.val = 1 then (1 : Fin 5)
    else if a.val = 2 then (3 : Fin 5)
    else if a.val = 3 then (2 : Fin 5)
    else (4 : Fin 5)
  injective := by
    intro a b
    revert a b
    decide
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide

theorem selfDualEmbedding_involution (a : Fin 5) :
    selfDualEmbedding.toFun (selfDualEmbedding.toFun a) = a := by
  apply Fin.ext
  revert a
  decide

end S5_1144

end SemigroupBasis.CoRoots.S5_1092Family
