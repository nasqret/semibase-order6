import SemigroupBasis.CoRoots.S5_441Completeness
import SemigroupBasis.CoRoots.S5_441Invariant
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_441Family

open SemigroupBasis

private def swapThreeFour : Fin 5 → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 3

private theorem swapThreeFour_injective :
    Function.Injective swapThreeFour := by
  intro left right
  revert left right
  decide

private theorem s4_69Models :
    Models Generated.Catalogue.S4_69.table.semigroup
      SemigroupBasis.CoRoots.S5_441.basis := by
  rw [SemigroupBasis.CoRoots.S5_441Invariant.catalogueS4_69_table_eq_uniqueSeparatorFour]
  exact SemigroupBasis.CoRoots.S5_441.basis_models_uniqueSeparatorFour

private theorem s2_2Models :
    Models Generated.Catalogue.S2_2.table.semigroup
      SemigroupBasis.CoRoots.S5_441.basis := by
  rw [SemigroupBasis.CoRoots.S5_441Invariant.catalogueS2_2_table_eq_cyclicTwo]
  exact SemigroupBasis.CoRoots.S5_441.basis_models_cyclicTwo

private theorem s3_11Models :
    Models Generated.Catalogue.S3_11.table.semigroup
      SemigroupBasis.CoRoots.S5_441.basis := by
  rw [SemigroupBasis.CoRoots.S5_441Invariant.catalogueS3_11_table_eq_parityZeroThree]
  exact SemigroupBasis.CoRoots.S5_441.basis_models_parityZeroThree

namespace S5_441

/-- The common 25-law basis models the catalogue semigroup `S5_441`. -/
theorem models :
    Models Generated.Catalogue.S5_441.table.semigroup
      SemigroupBasis.CoRoots.S5_441.basis := by
  intro identity member
  exact
    (SemigroupBasis.CoRoots.S5_441Factors.S5_441.valid_iff_factors
      identity).2
      ⟨s4_69Models identity member, s2_2Models identity member⟩

/-- The common 25 laws form an identity basis for catalogue semigroup
`S5_441`. -/
theorem basisFor :
    BasisFor Generated.Catalogue.S5_441.table.semigroup
      SemigroupBasis.CoRoots.S5_441.basis :=
  SemigroupBasis.CoRoots.S5_441.basis_complete_of_signature
    Generated.Catalogue.S5_441.table.semigroup
    models
    SemigroupBasis.CoRoots.S5_441.valid_sameParitySeparatorSignature

/-- The audited permutation `[1,2,3,5,4]` identifies `S5_441` with its
opposite. -/
def selfDualEmbedding :
    Embedding Generated.Catalogue.S5_441.table.semigroup.opposite
      Generated.Catalogue.S5_441.table.semigroup where
  toFun := swapThreeFour
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := swapThreeFour_injective

theorem selfDualInvolution (value : Fin 5) :
    selfDualEmbedding.toFun (selfDualEmbedding.toFun value) = value := by
  revert value
  decide

end S5_441

namespace S5_464

/-- The common 25-law basis models the catalogue semigroup `S5_464`. -/
theorem models :
    Models Generated.Catalogue.S5_464.table.semigroup
      SemigroupBasis.CoRoots.S5_441.basis := by
  intro identity member
  exact
    (SemigroupBasis.CoRoots.S5_441Factors.S5_464.valid_iff_factors
      identity).2
      ⟨s4_69Models identity member, s2_2Models identity member⟩

/-- The common 25 laws form an identity basis for catalogue semigroup
`S5_464`. -/
theorem basisFor :
    BasisFor Generated.Catalogue.S5_464.table.semigroup
      SemigroupBasis.CoRoots.S5_441.basis :=
  SemigroupBasis.CoRoots.S5_441.basis_complete_of_signature
    Generated.Catalogue.S5_464.table.semigroup
    models
    SemigroupBasis.CoRoots.S5_464.valid_sameParitySeparatorSignature

/-- The audited permutation `[1,2,3,5,4]` identifies `S5_464` with its
opposite. -/
def selfDualEmbedding :
    Embedding Generated.Catalogue.S5_464.table.semigroup.opposite
      Generated.Catalogue.S5_464.table.semigroup where
  toFun := swapThreeFour
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := swapThreeFour_injective

theorem selfDualInvolution (value : Fin 5) :
    selfDualEmbedding.toFun (selfDualEmbedding.toFun value) = value := by
  revert value
  decide

end S5_464

namespace S5_612

/-- The common 25-law basis models the catalogue semigroup `S5_612`. -/
theorem models :
    Models Generated.Catalogue.S5_612.table.semigroup
      SemigroupBasis.CoRoots.S5_441.basis := by
  intro identity member
  exact
    (SemigroupBasis.CoRoots.S5_441Factors.S5_612.valid_iff_factors
      identity).2
      ⟨s4_69Models identity member, s3_11Models identity member⟩

/-- The common 25 laws form an identity basis for catalogue semigroup
`S5_612`. -/
theorem basisFor :
    BasisFor Generated.Catalogue.S5_612.table.semigroup
      SemigroupBasis.CoRoots.S5_441.basis :=
  SemigroupBasis.CoRoots.S5_441.basis_complete_of_signature
    Generated.Catalogue.S5_612.table.semigroup
    models
    SemigroupBasis.CoRoots.S5_612.valid_sameParitySeparatorSignature

/-- The reversed common basis is complete for the opposite orientation of
the non-self-dual catalogue class `S5_612`. -/
theorem oppositeBasisFor :
    BasisFor Generated.Catalogue.S5_612.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_441.basis) :=
  basisFor.oppositeReversed

end S5_612

end SemigroupBasis.CoRoots.S5_441Family
