import SemigroupBasis.CoRoots.Order6FactorPairS2S5353Normal
import SemigroupBasis.CoRoots.Order6FactorPairS2S5381Normal
import SemigroupBasis.CoRoots.Order6FactorPairS2S583Normal
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S2_2
import SemigroupBasis.Generated.S3_11
import SemigroupBasis.Subdirect

/-!
# Dualized factor-pair bases with an opposite right factor

Dualizing an unrestricted intersection basis for `S2_2` and `S5_k` gives
one for `S2_2^op` and `S5_k^op`. The cyclic semigroup `S2_2` is
self-opposite, and its opposite also embeds into the nonzero group part of
`S3_11`. After checking the reversed candidate laws on the enlarged left
factor, these embeddings therefore yield the three intersection bases used
by roots `S6_1349`, `S6_4164`, and `S6_7001`.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairOppositeRightWidening

open SemigroupBasis

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

def s2_2OppositeIntoS2_2 (value : Fin 2) : Fin 2 :=
  value

theorem s2_2OppositeIntoS2_2_values :
    List.ofFn
      (fun value : Fin 2 => (s2_2OppositeIntoS2_2 value).val) = [0, 1] := by
  decide

/-- The cyclic order-two semigroup is explicitly self-opposite. -/
def s2_2OppositeEmbeddingS2_2 :
    Embedding
      SemigroupBasis.Generated.S2_2.table.semigroup.opposite
      SemigroupBasis.Generated.S2_2.table.semigroup where
  toFun := s2_2OppositeIntoS2_2
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    revert left right
    decide

def s2_2OppositeIntoS3_11 (value : Fin 2) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else (1 : Fin 3)

theorem s2_2OppositeIntoS3_11_values :
    List.ofFn
      (fun value : Fin 2 => (s2_2OppositeIntoS3_11 value).val) = [0, 1] := by
  decide

/-- The nonzero group part of `S3_11` contains `S2_2^op`. -/
def s2_2OppositeEmbeddingS3_11 :
    Embedding
      SemigroupBasis.Generated.S2_2.table.semigroup.opposite
      SemigroupBasis.Generated.S3_11.table.semigroup where
  toFun := s2_2OppositeIntoS3_11
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    revert left right
    decide

private theorem modelsS2_2ReversedS5_83Basis :
    Models
      SemigroupBasis.Generated.S2_2.table.semigroup
      (reversedBasis
        SemigroupBasis.CoRoots.Order6FactorPairS2S583Normal.basis) :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S2_2.table
    (reversedBasis
      SemigroupBasis.CoRoots.Order6FactorPairS2S583Normal.basis)
    toFinThree
    (by decide)

private theorem modelsS2_2ReversedS5_353Basis :
    Models
      SemigroupBasis.Generated.S2_2.table.semigroup
      (reversedBasis
        SemigroupBasis.CoRoots.Order6FactorPairS2S5353Normal.basis) :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S2_2.table
    (reversedBasis
      SemigroupBasis.CoRoots.Order6FactorPairS2S5353Normal.basis)
    toFinThree
    (by decide)

private theorem modelsS3_11ReversedS5_610Basis :
    Models
      SemigroupBasis.Generated.S3_11.table.semigroup
      (reversedBasis
        SemigroupBasis.CoRoots.Order6FactorPairS2S5381.basis) :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_11.table
    (reversedBasis
      SemigroupBasis.CoRoots.Order6FactorPairS2S5381.basis)
    toFinThree
    (by decide)

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

/-- Reversed joint basis for `S2_2` and `S5_83^op`. -/
def intersectionBasisS2_2S5_83Opposite :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup.opposite
      (reversedBasis
        SemigroupBasis.CoRoots.Order6FactorPairS2S583Normal.basis) :=
  widenLeftFactor
    (SemigroupBasis.IntersectionBasis.oppositeReversed
      SemigroupBasis.CoRoots.Order6FactorPairS2S583Normal.factorIntersectionBasis)
    modelsS2_2ReversedS5_83Basis
    s2_2OppositeEmbeddingS2_2

/-- Reversed joint basis for `S2_2` and `S5_353^op`. -/
def intersectionBasisS2_2S5_353Opposite :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_353.table.semigroup.opposite
      (reversedBasis
        SemigroupBasis.CoRoots.Order6FactorPairS2S5353Normal.basis) :=
  widenLeftFactor
    (SemigroupBasis.IntersectionBasis.oppositeReversed
      SemigroupBasis.CoRoots.Order6FactorPairS2S5353Normal.intersectionBasis)
    modelsS2_2ReversedS5_353Basis
    s2_2OppositeEmbeddingS2_2

/-- Reversed joint basis for `S3_11` and `S5_610^op`. -/
def intersectionBasisS3_11S5_610Opposite :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup.opposite
      (reversedBasis
        SemigroupBasis.CoRoots.Order6FactorPairS2S5381.basis) :=
  widenLeftFactor
    (SemigroupBasis.IntersectionBasis.oppositeReversed
      SemigroupBasis.CoRoots.Order6FactorPairS2S5381.s5_610FactorIntersectionBasis)
    modelsS3_11ReversedS5_610Basis
    s2_2OppositeEmbeddingS3_11

end SemigroupBasis.CoRoots.Order6FactorPairOppositeRightWidening
