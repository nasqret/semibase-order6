import SemigroupBasis.CoRoots.Order6FactorPairS2S5348Normal
import SemigroupBasis.CoRoots.Order6FactorPairS3_11Widening
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.Order6OneLocalFordLast.DisplayedSigma
import SemigroupBasis.Order6ResidualReleaseV3.OverlookedExisting63.S6_4053
import SemigroupBasis.Order6ResidualReleaseV3.OverlookedExisting63.S6_4157
import SemigroupBasis.Order6ResidualReleaseV3.OverlookedExisting63.S6_4265

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6OneLocalFordLastSigma5b78

open SemigroupBasis

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLast.DisplayedSigma.Sigma_5b78bf5b916fda2a.basis

/-- The generated displayed Sigma is exactly the already complete
`S2_2`/`S5_348` basis, including its ordering and orientations. -/
theorem basis_eq_s2_s5_348 :
    basis = SemigroupBasis.CoRoots.Order6FactorPairS2S5348.basis := by
  decide

/-- Repackage the existing factor intersection at the generated exact Sigma. -/
def intersectionBasisS2_2S5_348 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_348.table.semigroup
      basis := by
  rw [basis_eq_s2_s5_348]
  exact SemigroupBasis.CoRoots.Order6FactorPairS2S5348.intersectionBasis

/-- Existing unconditional root endpoint, adapted only across exact basis
equality. -/
theorem s6_4053_basis :
    BasisFor
      SemigroupBasis.Generated.Order6FactorPairS2S5348Targets.S6_4053.table.semigroup
      basis := by
  rw [basis_eq_s2_s5_348]
  exact
    SemigroupBasis.Order6ResidualReleaseV3.OverlookedExisting63.S6_4053.representative_basis

/-- Existing unconditional root endpoint, adapted only across exact basis
equality. -/
theorem s6_4157_basis :
    BasisFor
      SemigroupBasis.Generated.Order6FactorPairS2S5348Targets.S6_4157.table.semigroup
      basis := by
  rw [basis_eq_s2_s5_348]
  exact
    SemigroupBasis.Order6ResidualReleaseV3.OverlookedExisting63.S6_4157.representative_basis

/-- Existing unconditional root endpoint, adapted only across exact basis
equality. -/
theorem s6_4265_basis :
    BasisFor
      SemigroupBasis.Generated.Order6FactorPairS2S5348Targets.S6_4265.table.semigroup
      basis := by
  rw [basis_eq_s2_s5_348]
  exact
    SemigroupBasis.Order6ResidualReleaseV3.OverlookedExisting63.S6_4265.representative_basis

def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun identity => identity.map toFinThree

theorem basisRoundTripChecked :
    basis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true := by
  decide

/-- Reflect an exhaustive finite check of this fixed three-variable Sigma back
to its natural-number variable names. -/
theorem modelsOfFiniteChecks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinThree).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp basisRoundTripChecked) identity member
  rw [restored] at finiteValid
  exact finiteValid

/-- The exact Sigma also models `S3_11`; this is the only additional
soundness check needed to widen the existing cyclic-factor intersection. -/
theorem modelsS3_11 :
    Models SemigroupBasis.Generated.S3_11.table.semigroup basis :=
  modelsOfFiniteChecks SemigroupBasis.Generated.S3_11.table (by decide)

/-- Exact joint basis for `S3_11` and direct `S5_348`, obtained by restricting
an `S3_11`-valid identity to its explicit cyclic subsemigroup and applying the
already complete `S2_2`/`S5_348` intersection. -/
def intersectionBasisS3_11S5_348 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_348.table.semigroup
      basis where
  leftModels := modelsS3_11
  rightModels := intersectionBasisS2_2S5_348.rightModels
  complete := by
    intro identity leftValid rightValid
    exact intersectionBasisS2_2S5_348.complete identity
      (SemigroupBasis.CoRoots.Order6FactorPairS3_11Widening.cyclicEmbeddingS3_11.pullback_identity
        identity leftValid)
      rightValid

end SemigroupBasis.CoRoots.Order6OneLocalFordLastSigma5b78
