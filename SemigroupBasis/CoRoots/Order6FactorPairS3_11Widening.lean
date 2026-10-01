import SemigroupBasis.CoRoots.Order6FactorPairS2S5378Normal
import SemigroupBasis.CoRoots.Order6FactorPairS2S5381Normal
import SemigroupBasis.CoRoots.Order6FactorPairS2S5400Normal
import SemigroupBasis.CoRoots.Order6FactorPairS2S583Normal
import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.S3_11

/-!
# Widening cyclic factor-pair bases to `S3_11`

The order-three semigroup `S3_11 = C2^0` contains the cyclic group `C2`.
Consequently, an identity valid in `S3_11` is valid in `C2`.  If a basis is
already complete for `C2` together with a second factor, and its displayed
laws are valid in `S3_11`, the same basis is complete after replacing `C2`
by `S3_11`.

This module applies that argument once to each of the four candidate systems
used by the six `S3_11` factor-pair endpoints.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_11Widening

open SemigroupBasis
open SemigroupBasis.Examples

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def finiteBasis
    (candidate : List (Identity Nat)) : List (Identity (Fin 3)) :=
  candidate.map fun identity => identity.map toFinThree

/-- Lift exhaustive checks of a three-variable candidate system on `S3_11`
back to its original natural-number variable names. -/
private theorem modelsS3_11OfFiniteChecks
    (candidate : List (Identity Nat))
    (roundTripChecked :
      candidate.all (fun identity =>
        decide ((identity.map toFinThree).map Fin.val = identity)) = true)
    (checked :
      (finiteBasis candidate).all
        SemigroupBasis.Generated.S3_11.table.checkIdentity = true) :
    Models SemigroupBasis.Generated.S3_11.table.semigroup candidate := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis candidate :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    SemigroupBasis.Generated.S3_11.table.checkIdentityNat_sound
      (identity.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinThree).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp roundTripChecked) identity member
  rw [restored] at finiteValid
  exact finiteValid

def cyclicIntoS3_11 (value : Fin 2) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else (1 : Fin 3)

theorem cyclicIntoS3_11_values :
    List.ofFn (fun value : Fin 2 => (cyclicIntoS3_11 value).val) = [0, 1] := by
  decide

/-- The nonzero group part of `S3_11` is an explicit copy of `C2`. -/
def cyclicEmbeddingS3_11 :
    Embedding cyclicTwo.semigroup
      SemigroupBasis.Generated.S3_11.table.semigroup where
  toFun := cyclicIntoS3_11
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    revert left right
    decide

/-- Replace the left factor of an intersection basis by a larger semigroup
containing it, once the candidate laws have been checked on the larger
factor. -/
private def widenLeftFactor
    {A : Type u} {B : Type v} {C : Type w} {X : Type z}
    {sourceLeft : Semigroup A} {targetLeft : Semigroup B}
    {rightFactor : Semigroup C}
    {candidate : List (Identity X)}
    (source : IntersectionBasis sourceLeft rightFactor candidate)
    (targetModels : Models targetLeft candidate)
    (into : Embedding sourceLeft targetLeft) :
    IntersectionBasis targetLeft rightFactor candidate where
  leftModels := targetModels
  rightModels := source.rightModels
  complete := by
    intro identity targetValid rightValid
    exact source.complete identity
      (into.pullback_identity identity targetValid) rightValid

private theorem modelsS3_11S5_378Basis :
    Models
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorPairS2S5378.basis :=
  modelsS3_11OfFiniteChecks
    SemigroupBasis.CoRoots.Order6FactorPairS2S5378.basis
    (by decide) (by decide)

private theorem modelsS3_11S5_381Basis :
    Models
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorPairS2S5381.basis :=
  modelsS3_11OfFiniteChecks
    SemigroupBasis.CoRoots.Order6FactorPairS2S5381.basis
    (by decide) (by decide)

private theorem modelsS3_11S5_400Basis :
    Models
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorPairS2S5400Normal.basis :=
  modelsS3_11OfFiniteChecks
    SemigroupBasis.CoRoots.Order6FactorPairS2S5400Normal.basis
    (by decide) (by decide)

/-- The exact eight-law `S2_2`/`S5_83` basis also holds in `S3_11`. -/
private theorem modelsS3_11S5_83Basis :
    Models
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorPairS2S583Normal.basis :=
  modelsS3_11OfFiniteChecks
    SemigroupBasis.CoRoots.Order6FactorPairS2S583Normal.basis
    (by decide) (by decide)

/-- Joint basis for `S3_11` and `S5_83`. -/
def intersectionBasisS5_83 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorPairS2S583Normal.basis :=
  widenLeftFactor
    SemigroupBasis.CoRoots.Order6FactorPairS2S583Normal.factorIntersectionBasis
    modelsS3_11S5_83Basis cyclicEmbeddingS3_11

/-- Joint basis for `S3_11` and `S5_378`. -/
def intersectionBasisS5_378 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_378.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorPairS2S5378.basis :=
  widenLeftFactor
    SemigroupBasis.CoRoots.Order6FactorPairS2S5378.factorIntersectionBasis
    modelsS3_11S5_378Basis cyclicEmbeddingS3_11

/-- Joint basis for `S3_11` and `S5_381`. -/
def intersectionBasisS5_381 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_381.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorPairS2S5381.basis :=
  widenLeftFactor
    SemigroupBasis.CoRoots.Order6FactorPairS2S5381.factorIntersectionBasis
    modelsS3_11S5_381Basis cyclicEmbeddingS3_11

/-- Joint basis for `S3_11` and `S5_610`. -/
def intersectionBasisS5_610 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorPairS2S5381.basis :=
  widenLeftFactor
    SemigroupBasis.CoRoots.Order6FactorPairS2S5381.s5_610FactorIntersectionBasis
    modelsS3_11S5_381Basis cyclicEmbeddingS3_11

/-- Joint basis for `S3_11` and `S5_400`. -/
def intersectionBasisS5_400 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorPairS2S5400Normal.basis :=
  widenLeftFactor
    SemigroupBasis.CoRoots.Order6FactorPairS2S5400Normal.intersectionBasis
    modelsS3_11S5_400Basis cyclicEmbeddingS3_11

/-- Joint basis for `S3_11` and `S5_840`. -/
def intersectionBasisS5_840 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorPairS2S5400Normal.basis :=
  widenLeftFactor
    SemigroupBasis.CoRoots.Order6FactorPairS2S5400Normal.intersectionBasisS5_840
    modelsS3_11S5_400Basis cyclicEmbeddingS3_11

end SemigroupBasis.CoRoots.Order6FactorPairS3_11Widening
