import SemigroupBasis.Generated.Order6FactorPairSharedFamilies
import SemigroupBasis.Generated.S3_11
import SemigroupBasis.Nonfinite

/-!
# Reuse of the corrected `S5_94` / `C2` factor-intersection basis

This module closes eight order-six catalogue tables.  The source is the
unrestricted fifteen-law intersection basis (including `xyzt = xzyt`) for
`S5_94` and `C2`.  The first five targets replace `S5_94` by a semigroup with
the same complete lower-order basis.  The last three widen `C2` to `S3_11`;
soundness on `S3_11` is checked and completeness is pulled back along the
explicit embedding `C2 ↪ S3_11`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6FactorPairS2S594ReuseV3

open SemigroupBasis
open SemigroupBasis.Examples

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S594.basis

/-- Two semigroups carrying the same complete basis have the same full
identity theory over the basis variable type. -/
private theorem sameIdentityTheoryOverOfCommonBasis
    {A : Type u} {B : Type v} {X : Type w}
    {G : Semigroup A} {H : Semigroup B}
    {commonBasis : List (Identity X)}
    (basisForG : BasisFor G commonBasis)
    (basisForH : BasisFor H commonBasis) :
    SameIdentityTheoryOver G H X := by
  intro identity
  constructor
  · intro validInG valuation
    exact Derives.sound basisForH.1
      (basisForG.2 identity validInG) valuation
  · intro validInH valuation
    exact Derives.sound basisForG.1
      (basisForH.2 identity validInH) valuation

private theorem s5_94_s5_95_sameTheory :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.Catalogue.S5_94.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_95.table.semigroup Nat :=
  sameIdentityTheoryOverOfCommonBasis
    SemigroupBasis.CoRoots.S5_94Family.S5_94.basis_complete
    SemigroupBasis.CoRoots.S5_94Family.S5_95.basis_complete

private theorem s5_94_s5_104_sameTheory :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.Catalogue.S5_94.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_104.table.semigroup Nat :=
  sameIdentityTheoryOverOfCommonBasis
    SemigroupBasis.CoRoots.S5_94Family.S5_94.basis_complete
    SemigroupBasis.CoRoots.S5_94Family.S5_104.basis_complete

/-- The source endpoint is retained only as the already-authenticated
subdirect presentation of `S5_94` and `C2`; completeness comes directly from
the corrected unrestricted intersection theorem. -/
private theorem sourceBasis :
    BasisFor
      SemigroupBasis.Generated.Order6FactorPairSharedFamilies.S6_1247.table.semigroup
      basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S594.factorIntersectionBasis.basisFor
    SemigroupBasis.Generated.Order6FactorPairSharedFamilies.S6_1247.pair

def cyclicIntoS3_11 (value : Fin 2) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else (1 : Fin 3)

def cyclicIntoS3_11ValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 2 => (cyclicIntoS3_11 value).val + 1

theorem cyclicIntoS3_11ValuesOneBased_certificate :
    cyclicIntoS3_11ValuesOneBased = [1, 2] := by
  decide

/-- The group part of `S3_11 = C2^0` is an explicit copy of `C2`. -/
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

private theorem modelsS3_11 :
    Models SemigroupBasis.Generated.S3_11.table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S594.modelsOfFiniteChecks
    SemigroupBasis.Generated.S3_11.table (by decide)

/-- Widen the second factor from `C2` to `S3_11`.  Validity in the larger
factor pulls back to `C2`, while the fifteen displayed laws are checked on the
larger factor. -/
private theorem s5_94_s3_11IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.Catalogue.S5_94.table.semigroup
      SemigroupBasis.Generated.S3_11.table.semigroup basis where
  leftModels :=
    SemigroupBasis.CoRoots.Order6FactorPairS2S594.factorIntersectionBasis.leftModels
  rightModels := modelsS3_11
  complete := by
    intro identity validS5 validS3
    exact
      SemigroupBasis.CoRoots.Order6FactorPairS2S594.factorIntersectionBasis.complete
        identity validS5
        (cyclicEmbeddingS3_11.pullback_identity identity validS3)

private def valuesOneBased {n m : Nat} (f : Fin n → Fin m) : List Nat :=
  List.ofFn fun value => (f value).val + 1

namespace S6_1248

/-- Exact one-based catalogue table, SHA-256
`3cf8b4a1e1fa08c1ee26825628895650fba36cee5d9ad0ccbf01d28fa19fc298`. -/
def mul (a b : Fin 6) : Fin 6 :=
  match a.val, b.val with
  | 0, 4 => 4
  | 1, 4 => 4
  | 2, 4 => 4
  | 2, 5 => 2
  | 3, 4 => 4
  | 3, 5 => 3
  | 4, 0 => 4
  | 4, 1 => 4
  | 4, 2 => 4
  | 4, 3 => 4
  | 4, 5 => 4
  | 5, 1 => 1
  | 5, 2 => 2
  | 5, 3 => 2
  | 5, 4 => 4
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "3cf8b4a1e1fa08c1ee26825628895650fba36cee5d9ad0ccbf01d28fa19fc298"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 4, 0], [0, 0, 0, 0, 4, 0],
   [0, 0, 0, 0, 4, 2], [0, 0, 0, 0, 4, 3],
   [4, 4, 4, 4, 0, 4], [0, 1, 2, 2, 4, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun a =>
      (List.finRange 6).map fun b => (mul a b).val) = publishedRows := by
  decide

def s5Map (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | _ => 4

def s5Section (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | _ => 5

def ontoS5 : SplitSurjection table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_95.table.semigroup where
  toFun := s5Map
  map_mul := by decide
  preimage := s5Section
  right_inverse := by decide

def cyclicMap (value : Fin 6) : Fin 2 :=
  match value.val with
  | 4 => 1
  | _ => 0

def cyclicSection (value : Fin 2) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else (4 : Fin 6)

def ontoCyclic : SplitSurjection table.semigroup cyclicTwo.semigroup where
  toFun := cyclicMap
  map_mul := by decide
  preimage := cyclicSection
  right_inverse := by decide

def s5MapValuesOneBased := valuesOneBased s5Map
def cyclicMapValuesOneBased := valuesOneBased cyclicMap
def s5SectionValuesOneBased := valuesOneBased s5Section
def cyclicSectionValuesOneBased := valuesOneBased cyclicSection

theorem mapValuesOneBased_certificate :
    s5MapValuesOneBased = [1, 2, 3, 4, 1, 5] ∧
    cyclicMapValuesOneBased = [1, 1, 1, 1, 2, 1] ∧
    s5SectionValuesOneBased = [1, 2, 3, 4, 6] ∧
    cyclicSectionValuesOneBased = [1, 5] := by
  decide

def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_95.table.semigroup
    cyclicTwo.semigroup where
  left := ontoS5
  right := ontoCyclic
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis : BasisFor table.semigroup basis :=
  sourceBasis.transferAcrossSubdirectPairs
    SemigroupBasis.Generated.Order6FactorPairSharedFamilies.S6_1247.pair
    subdirectPair
    s5_94_s5_95_sameTheory (fun _ => Iff.rfl)

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_1248

namespace S6_1256

/-- Exact one-based catalogue table, SHA-256
`056ec5c8a6ae8e581db38540bef4892eb3fd916996f377cce6fea853fc496dd5`. -/
def mul (a b : Fin 6) : Fin 6 :=
  match a.val, b.val with
  | 0, 4 => 4
  | 1, 4 => 4
  | 1, 5 => 1
  | 2, 4 => 4
  | 2, 5 => 1
  | 3, 4 => 4
  | 3, 5 => 3
  | 4, 0 => 4
  | 4, 1 => 4
  | 4, 2 => 4
  | 4, 3 => 4
  | 4, 5 => 4
  | 5, 1 => 1
  | 5, 2 => 2
  | 5, 3 => 1
  | 5, 4 => 4
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "056ec5c8a6ae8e581db38540bef4892eb3fd916996f377cce6fea853fc496dd5"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 4, 0], [0, 0, 0, 0, 4, 1],
   [0, 0, 0, 0, 4, 1], [0, 0, 0, 0, 4, 3],
   [4, 4, 4, 4, 0, 4], [0, 1, 2, 1, 4, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun a =>
      (List.finRange 6).map fun b => (mul a b).val) = publishedRows := by
  decide

def s5Map (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | _ => 4

def s5Section (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | _ => 5

def ontoS5 : SplitSurjection table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_104.table.semigroup where
  toFun := s5Map
  map_mul := by decide
  preimage := s5Section
  right_inverse := by decide

def cyclicMap (value : Fin 6) : Fin 2 :=
  match value.val with
  | 4 => 1
  | _ => 0

def cyclicSection (value : Fin 2) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else (4 : Fin 6)

def ontoCyclic : SplitSurjection table.semigroup cyclicTwo.semigroup where
  toFun := cyclicMap
  map_mul := by decide
  preimage := cyclicSection
  right_inverse := by decide

def s5MapValuesOneBased := valuesOneBased s5Map
def cyclicMapValuesOneBased := valuesOneBased cyclicMap
def s5SectionValuesOneBased := valuesOneBased s5Section
def cyclicSectionValuesOneBased := valuesOneBased cyclicSection

theorem mapValuesOneBased_certificate :
    s5MapValuesOneBased = [1, 2, 3, 4, 1, 5] ∧
    cyclicMapValuesOneBased = [1, 1, 1, 1, 2, 1] ∧
    s5SectionValuesOneBased = [1, 2, 3, 4, 6] ∧
    cyclicSectionValuesOneBased = [1, 5] := by
  decide

def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_104.table.semigroup
    cyclicTwo.semigroup where
  left := ontoS5
  right := ontoCyclic
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis : BasisFor table.semigroup basis :=
  sourceBasis.transferAcrossSubdirectPairs
    SemigroupBasis.Generated.Order6FactorPairSharedFamilies.S6_1247.pair
    subdirectPair
    s5_94_s5_104_sameTheory (fun _ => Iff.rfl)

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_1256

namespace S6_1334

/-- Exact one-based catalogue table, SHA-256
`a32d31b3b04dec8a37d625ff8378146db564a8de56a1bbdc7665d8c92baa5354`. -/
def mul (a b : Fin 6) : Fin 6 :=
  match a.val, b.val with
  | 0, 2 => 2 | 0, 3 => 2 | 0, 4 => 2
  | 1, 2 => 2 | 1, 3 => 2 | 1, 4 => 2
  | 2, 0 => 2 | 2, 1 => 2 | 2, 5 => 2
  | 3, 0 => 2 | 3, 1 => 2 | 3, 5 => 3
  | 4, 0 => 2 | 4, 1 => 2 | 4, 5 => 4
  | 5, 1 => 1 | 5, 2 => 2 | 5, 3 => 3 | 5, 4 => 3 | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a32d31b3b04dec8a37d625ff8378146db564a8de56a1bbdc7665d8c92baa5354"

def publishedRows : List (List Nat) :=
  [[0, 0, 2, 2, 2, 0], [0, 0, 2, 2, 2, 0],
   [2, 2, 0, 0, 0, 2], [2, 2, 0, 0, 0, 3],
   [2, 2, 0, 0, 0, 4], [0, 1, 2, 3, 3, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun a =>
      (List.finRange 6).map fun b => (mul a b).val) = publishedRows := by
  decide

def s5Map (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 3 | _ => 4

def s5Section (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | _ => 5

def ontoS5 : SplitSurjection table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_95.table.semigroup where
  toFun := s5Map
  map_mul := by decide
  preimage := s5Section
  right_inverse := by decide

def cyclicMap (value : Fin 6) : Fin 2 :=
  match value.val with
  | 2 | 3 | 4 => 1
  | _ => 0

def cyclicSection (value : Fin 2) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else (2 : Fin 6)

def ontoCyclic : SplitSurjection table.semigroup cyclicTwo.semigroup where
  toFun := cyclicMap
  map_mul := by decide
  preimage := cyclicSection
  right_inverse := by decide

def s5MapValuesOneBased := valuesOneBased s5Map
def cyclicMapValuesOneBased := valuesOneBased cyclicMap
def s5SectionValuesOneBased := valuesOneBased s5Section
def cyclicSectionValuesOneBased := valuesOneBased cyclicSection

theorem mapValuesOneBased_certificate :
    s5MapValuesOneBased = [1, 2, 1, 3, 4, 5] ∧
    cyclicMapValuesOneBased = [1, 1, 2, 2, 2, 1] ∧
    s5SectionValuesOneBased = [1, 2, 4, 5, 6] ∧
    cyclicSectionValuesOneBased = [1, 3] := by
  decide

def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_95.table.semigroup
    cyclicTwo.semigroup where
  left := ontoS5
  right := ontoCyclic
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis : BasisFor table.semigroup basis :=
  S6_1248.representative_basis.transferAcrossSubdirectPairs
    S6_1248.subdirectPair subdirectPair
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_1334

namespace S6_1388

/-- Exact one-based catalogue table, SHA-256
`8f4ee6cdb8c4abb7d32ca83f535a69d9f6b11a244e285d8ec0971ef7cb771156`. -/
def mul (a b : Fin 6) : Fin 6 :=
  match a.val, b.val with
  | 0, 1 => 1 | 0, 2 => 1 | 0, 3 => 1 | 0, 4 => 1
  | 1, 0 => 1 | 1, 5 => 1
  | 2, 0 => 1 | 2, 5 => 1
  | 3, 0 => 1 | 3, 5 => 3
  | 4, 0 => 1 | 4, 5 => 4
  | 5, 1 => 1 | 5, 2 => 2 | 5, 3 => 3 | 5, 4 => 3 | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "8f4ee6cdb8c4abb7d32ca83f535a69d9f6b11a244e285d8ec0971ef7cb771156"

def publishedRows : List (List Nat) :=
  [[0, 1, 1, 1, 1, 0], [1, 0, 0, 0, 0, 1],
   [1, 0, 0, 0, 0, 1], [1, 0, 0, 0, 0, 3],
   [1, 0, 0, 0, 0, 4], [0, 1, 2, 3, 3, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun a =>
      (List.finRange 6).map fun b => (mul a b).val) = publishedRows := by
  decide

def s5Map (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4

def s5Section (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | _ => 5

def ontoS5 : SplitSurjection table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_95.table.semigroup where
  toFun := s5Map
  map_mul := by decide
  preimage := s5Section
  right_inverse := by decide

def cyclicMap (value : Fin 6) : Fin 2 :=
  match value.val with
  | 1 | 2 | 3 | 4 => 1
  | _ => 0

def cyclicSection (value : Fin 2) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else (1 : Fin 6)

def ontoCyclic : SplitSurjection table.semigroup cyclicTwo.semigroup where
  toFun := cyclicMap
  map_mul := by decide
  preimage := cyclicSection
  right_inverse := by decide

def s5MapValuesOneBased := valuesOneBased s5Map
def cyclicMapValuesOneBased := valuesOneBased cyclicMap
def s5SectionValuesOneBased := valuesOneBased s5Section
def cyclicSectionValuesOneBased := valuesOneBased cyclicSection

theorem mapValuesOneBased_certificate :
    s5MapValuesOneBased = [1, 1, 2, 3, 4, 5] ∧
    cyclicMapValuesOneBased = [1, 2, 2, 2, 2, 1] ∧
    s5SectionValuesOneBased = [1, 3, 4, 5, 6] ∧
    cyclicSectionValuesOneBased = [1, 2] := by
  decide

def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_95.table.semigroup
    cyclicTwo.semigroup where
  left := ontoS5
  right := ontoCyclic
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis : BasisFor table.semigroup basis :=
  S6_1248.representative_basis.transferAcrossSubdirectPairs
    S6_1248.subdirectPair subdirectPair
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_1388

namespace S6_1395

/-- Exact one-based catalogue table, SHA-256
`7aaf93c4cf63744daf9c35e05e0a4e6f109d0c00edaa57a422a47389b35367a0`. -/
def mul (a b : Fin 6) : Fin 6 :=
  match a.val, b.val with
  | 0, 1 => 1 | 0, 2 => 1 | 0, 3 => 1 | 0, 4 => 1
  | 1, 0 => 1 | 1, 5 => 1
  | 2, 0 => 1 | 2, 5 => 2
  | 3, 0 => 1 | 3, 5 => 2
  | 4, 0 => 1 | 4, 5 => 4
  | 5, 1 => 1 | 5, 2 => 2 | 5, 3 => 3 | 5, 4 => 2 | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "7aaf93c4cf63744daf9c35e05e0a4e6f109d0c00edaa57a422a47389b35367a0"

def publishedRows : List (List Nat) :=
  [[0, 1, 1, 1, 1, 0], [1, 0, 0, 0, 0, 1],
   [1, 0, 0, 0, 0, 2], [1, 0, 0, 0, 0, 2],
   [1, 0, 0, 0, 0, 4], [0, 1, 2, 3, 2, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun a =>
      (List.finRange 6).map fun b => (mul a b).val) = publishedRows := by
  decide

def s5Map (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 4

def s5Section (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | _ => 5

def ontoS5 : SplitSurjection table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_104.table.semigroup where
  toFun := s5Map
  map_mul := by decide
  preimage := s5Section
  right_inverse := by decide

def cyclicMap (value : Fin 6) : Fin 2 :=
  match value.val with
  | 1 | 2 | 3 | 4 => 1
  | _ => 0

def cyclicSection (value : Fin 2) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else (1 : Fin 6)

def ontoCyclic : SplitSurjection table.semigroup cyclicTwo.semigroup where
  toFun := cyclicMap
  map_mul := by decide
  preimage := cyclicSection
  right_inverse := by decide

def s5MapValuesOneBased := valuesOneBased s5Map
def cyclicMapValuesOneBased := valuesOneBased cyclicMap
def s5SectionValuesOneBased := valuesOneBased s5Section
def cyclicSectionValuesOneBased := valuesOneBased cyclicSection

theorem mapValuesOneBased_certificate :
    s5MapValuesOneBased = [1, 1, 2, 3, 4, 5] ∧
    cyclicMapValuesOneBased = [1, 2, 2, 2, 2, 1] ∧
    s5SectionValuesOneBased = [1, 3, 4, 5, 6] ∧
    cyclicSectionValuesOneBased = [1, 2] := by
  decide

def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_104.table.semigroup
    cyclicTwo.semigroup where
  left := ontoS5
  right := ontoCyclic
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis : BasisFor table.semigroup basis :=
  S6_1256.representative_basis.transferAcrossSubdirectPairs
    S6_1256.subdirectPair subdirectPair
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_1395

namespace S6_3001

/-- Exact one-based catalogue table, SHA-256
`c3ade6c38984a4c135cbe4ca8e00e5c0e0920e06c84a834b352087063bd3528b`. -/
def mul (a b : Fin 6) : Fin 6 :=
  match a.val, b.val with
  | 2, 4 => 2 | 2, 5 => 2
  | 3, 4 => 3 | 3, 5 => 3
  | 4, 1 => 1 | 4, 3 => 3 | 4, 4 => 4 | 4, 5 => 5
  | 5, 1 => 1 | 5, 3 => 3 | 5, 4 => 5 | 5, 5 => 4
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c3ade6c38984a4c135cbe4ca8e00e5c0e0920e06c84a834b352087063bd3528b"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 3, 3],
   [0, 1, 0, 3, 4, 5], [0, 1, 0, 3, 5, 4]]

theorem mul_matches_published :
    (List.finRange 6).map (fun a =>
      (List.finRange 6).map fun b => (mul a b).val) = publishedRows := by
  decide

def s5Map (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | _ => 4

def s5Section (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | _ => 4

def ontoS5 : SplitSurjection table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_94.table.semigroup where
  toFun := s5Map
  map_mul := by decide
  preimage := s5Section
  right_inverse := by decide

def s3Map (value : Fin 6) : Fin 3 :=
  match value.val with
  | 4 => 0 | 5 => 1 | _ => 2

def s3Section (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => 4 | 1 => 5 | _ => 0

def ontoS3 : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S3_11.table.semigroup where
  toFun := s3Map
  map_mul := by decide
  preimage := s3Section
  right_inverse := by decide

def s5MapValuesOneBased := valuesOneBased s5Map
def s3MapValuesOneBased := valuesOneBased s3Map
def s5SectionValuesOneBased := valuesOneBased s5Section
def s3SectionValuesOneBased := valuesOneBased s3Section

theorem mapValuesOneBased_certificate :
    s5MapValuesOneBased = [1, 2, 3, 4, 5, 5] ∧
    s3MapValuesOneBased = [3, 3, 3, 3, 1, 2] ∧
    s5SectionValuesOneBased = [1, 2, 3, 4, 5] ∧
    s3SectionValuesOneBased = [5, 6, 1] := by
  decide

def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_94.table.semigroup
    SemigroupBasis.Generated.S3_11.table.semigroup where
  left := ontoS5
  right := ontoS3
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis : BasisFor table.semigroup basis :=
  s5_94_s3_11IntersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_3001

namespace S6_3003

/-- Exact one-based catalogue table, SHA-256
`50412cf6215838d9d79464478247944dec189dca3747f0533ddfdbdc29949bea`. -/
def mul (a b : Fin 6) : Fin 6 :=
  match a.val, b.val with
  | 2, 4 => 2 | 2, 5 => 2
  | 3, 4 => 3 | 3, 5 => 3
  | 4, 1 => 1 | 4, 2 => 2 | 4, 3 => 2 | 4, 4 => 4 | 4, 5 => 5
  | 5, 1 => 1 | 5, 2 => 2 | 5, 3 => 2 | 5, 4 => 5 | 5, 5 => 4
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "50412cf6215838d9d79464478247944dec189dca3747f0533ddfdbdc29949bea"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 2, 2], [0, 0, 0, 0, 3, 3],
   [0, 1, 2, 2, 4, 5], [0, 1, 2, 2, 5, 4]]

theorem mul_matches_published :
    (List.finRange 6).map (fun a =>
      (List.finRange 6).map fun b => (mul a b).val) = publishedRows := by
  decide

def s5Map (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | _ => 4

def s5Section (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | _ => 4

def ontoS5 : SplitSurjection table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_95.table.semigroup where
  toFun := s5Map
  map_mul := by decide
  preimage := s5Section
  right_inverse := by decide

def s3Map (value : Fin 6) : Fin 3 :=
  match value.val with
  | 4 => 0 | 5 => 1 | _ => 2

def s3Section (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => 4 | 1 => 5 | _ => 0

def ontoS3 : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S3_11.table.semigroup where
  toFun := s3Map
  map_mul := by decide
  preimage := s3Section
  right_inverse := by decide

def s5MapValuesOneBased := valuesOneBased s5Map
def s3MapValuesOneBased := valuesOneBased s3Map
def s5SectionValuesOneBased := valuesOneBased s5Section
def s3SectionValuesOneBased := valuesOneBased s3Section

theorem mapValuesOneBased_certificate :
    s5MapValuesOneBased = [1, 2, 3, 4, 5, 5] ∧
    s3MapValuesOneBased = [3, 3, 3, 3, 1, 2] ∧
    s5SectionValuesOneBased = [1, 2, 3, 4, 5] ∧
    s3SectionValuesOneBased = [5, 6, 1] := by
  decide

def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_95.table.semigroup
    SemigroupBasis.Generated.S3_11.table.semigroup where
  left := ontoS5
  right := ontoS3
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis : BasisFor table.semigroup basis :=
  S6_3001.representative_basis.transferAcrossSubdirectPairs
    S6_3001.subdirectPair subdirectPair
    s5_94_s5_95_sameTheory (fun _ => Iff.rfl)

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_3003

namespace S6_3037

/-- Exact one-based catalogue table, SHA-256
`ef3da835fb0643cf51bf62be8f45330ac5e08a27e1af80e4e7172ae1d86b0d1e`. -/
def mul (a b : Fin 6) : Fin 6 :=
  match a.val, b.val with
  | 1, 4 => 1 | 1, 5 => 1
  | 2, 4 => 1 | 2, 5 => 1
  | 3, 4 => 3 | 3, 5 => 3
  | 4, 1 => 1 | 4, 2 => 2 | 4, 3 => 1 | 4, 4 => 4 | 4, 5 => 5
  | 5, 1 => 1 | 5, 2 => 2 | 5, 3 => 1 | 5, 4 => 5 | 5, 5 => 4
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "ef3da835fb0643cf51bf62be8f45330ac5e08a27e1af80e4e7172ae1d86b0d1e"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1],
   [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 3, 3],
   [0, 1, 2, 1, 4, 5], [0, 1, 2, 1, 5, 4]]

theorem mul_matches_published :
    (List.finRange 6).map (fun a =>
      (List.finRange 6).map fun b => (mul a b).val) = publishedRows := by
  decide

def s5Map (value : Fin 6) : Fin 5 :=
  match value.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | _ => 4

def s5Section (value : Fin 5) : Fin 6 :=
  match value.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | _ => 4

def ontoS5 : SplitSurjection table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_104.table.semigroup where
  toFun := s5Map
  map_mul := by decide
  preimage := s5Section
  right_inverse := by decide

def s3Map (value : Fin 6) : Fin 3 :=
  match value.val with
  | 4 => 0 | 5 => 1 | _ => 2

def s3Section (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => 4 | 1 => 5 | _ => 0

def ontoS3 : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S3_11.table.semigroup where
  toFun := s3Map
  map_mul := by decide
  preimage := s3Section
  right_inverse := by decide

def s5MapValuesOneBased := valuesOneBased s5Map
def s3MapValuesOneBased := valuesOneBased s3Map
def s5SectionValuesOneBased := valuesOneBased s5Section
def s3SectionValuesOneBased := valuesOneBased s3Section

theorem mapValuesOneBased_certificate :
    s5MapValuesOneBased = [1, 2, 3, 4, 5, 5] ∧
    s3MapValuesOneBased = [3, 3, 3, 3, 1, 2] ∧
    s5SectionValuesOneBased = [1, 2, 3, 4, 5] ∧
    s3SectionValuesOneBased = [5, 6, 1] := by
  decide

def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.Catalogue.S5_104.table.semigroup
    SemigroupBasis.Generated.S3_11.table.semigroup where
  left := ontoS5
  right := ontoS3
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis : BasisFor table.semigroup basis :=
  S6_3001.representative_basis.transferAcrossSubdirectPairs
    S6_3001.subdirectPair subdirectPair
    s5_94_s5_104_sameTheory (fun _ => Iff.rfl)

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_3037

end SemigroupBasis.CoRoots.Order6FactorPairS2S594ReuseV3
