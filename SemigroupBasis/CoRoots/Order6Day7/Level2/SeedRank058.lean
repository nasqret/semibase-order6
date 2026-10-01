import SemigroupBasis.CoRoots.Order6Day7.S2_4.SeedS5_203
import SemigroupBasis.Generated.CatalogueOrder3

/-!
# Workload58: the missing direct S3_15 / S5_203 consumer

This is workload58, class S6_5579, not S1's legacy rank058.
The twelve displayed laws are literally the established Rank044 basis.
The genuine left-zero semigroup embeds in the ACTUAL target left factor
on zero-based elements 1 and 2, so every target-left identity is valid in
the source-left factor.  The right factor is unchanged.  The approved
transportNormalizer therefore reuses the kernel-green Rank044 seed.

Codex-0's older four-pair product replica already proved this widening in
a warm-only module (4c58a48d,20964609), without a class endpoint.  The
S5_203 part was reviewed; this isolated consumer uses the direct first-
coordinate embedding and does not import or re-audit the other three pairs.
No new lower normalizer, finite-projection completeness, or class seal is
claimed.  All unrestricted premises are supplied by existing proofs and
the concrete embedding, not by equality of displayed-basis digests.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.Level2.Rank058

open SemigroupBasis

abbrev leftTable : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S3_15.table

abbrev rightTable : FiniteTable :=
  SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank044.rightTable

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank044.basis

def displayedBasisSHA256 : String :=
  "8f7a6426a00788095ddd18a36a6978d395a98f6861b55a2ad93f49267c333955"

def leftEmbeddingMap (value : Fin 2) : Fin 3 :=
  if value = 0 then 1 else 2

def leftEmbedding :
    Embedding
      SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank044.leftTable.semigroup
      leftTable.semigroup where
  toFun := leftEmbeddingMap
  map_mul := by decide
  injective := by
    intro first second
    exact by decide +revert

theorem leftEmbedding_values :
    List.ofFn (fun value : Fin 2 => (leftEmbedding.toFun value).val) = [1, 2] := by
  decide

/-- Unrestricted implication furnished by the actual embedding. -/
theorem leftTheory (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    identity.SatisfiedBy
      SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank044.leftTable.semigroup :=
  leftEmbedding.pullback_identity identity valid

/-- The actual right factor and its orientation have not changed. -/
theorem rightTheory (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.SatisfiedBy
      SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank044.rightTable.semigroup :=
  valid

theorem seedLawDerives (law : Identity Nat)
    (member : law ∈ SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank044.basis) :
    Derives basis law.lhs law.rhs :=
  Derives.fromBasis member

private def finiteVariable : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

/-- Finite reflection supplies soundness only, not the unrestricted field. -/
theorem leftModels : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis finiteVariable (by decide)

theorem rightModels : Models rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank044.rightModels

/-- The established seed is transported with all three obligations proved. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank044.Seed.transportedNormalizer
    seedLawDerives leftTheory rightTheory

noncomputable def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis :=
  normalizer.toIntersectionBasis leftModels rightModels

/-- All nonempty words, without a rank, length, or unproved owner premise. -/
theorem derives_of_factor_valid (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  intersectionBasis.complete identity leftValid rightValid

end SemigroupBasis.CoRoots.Order6Day7.Level2.Rank058
