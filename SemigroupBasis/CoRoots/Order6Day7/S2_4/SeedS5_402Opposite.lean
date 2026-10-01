import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank021FiniteWitnesses
import SemigroupBasis.CoRoots.Order6LeeZhang23_9Completeness
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer

/-!
# An unrestricted `S2_4 × S5_402ᵒᵖ` family seed

The exact Lee--Zhang Proposition 23.9 derivational obligation was previously
kernel-verified for this same pair and both classes. Its published four-law
basis is literally the first four authenticated rank-021 displayed laws.
The reviewed sharded finite successor preserves that exact B20 list while
dividing the six-variable finite check into twenty-five bounded shards.
Transporting the genuine unrestricted B4 proof into B20 therefore requires
only four independently reviewed finite membership derivations.

Both class shells below are reconstructed literally from lines 891--1119 of
the authenticated frozen rank-021 source. Their namespace is the expressly
approved sharded finite successor; their maps, finite proofs, and conditional
normalizer premises are unchanged. Both factor structures are identified
independently before invoking historical completeness. The reviewed quotient
normalizer is built only after unrestricted factor-pair completeness; reusable
target transport retains all displayed-law witnesses and both unrestricted
theory implications.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank021ShardedFiniteBase

open SemigroupBasis
open SemigroupBasis.Examples

universe u v

namespace S6_11262

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if left = 1 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (1 : Fin 6)
    else (1 : Fin 6)
  else if left = 2 then
    if right = 0 then (2 : Fin 6)
    else if right = 1 then (2 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (2 : Fin 6)
    else if right = 4 then (2 : Fin 6)
    else (2 : Fin 6)
  else if left = 3 then
    if right = 0 then (2 : Fin 6)
    else if right = 1 then (2 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (2 : Fin 6)
    else if right = 4 then (3 : Fin 6)
    else (3 : Fin 6)
  else if left = 4 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (5 : Fin 6)
  else
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (1 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (1 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (value : Fin 6) : Fin 2 :=
  if value = 0 then (0 : Fin 2)
  else if value = 1 then (0 : Fin 2)
  else if value = 2 then (1 : Fin 2)
  else if value = 3 then (1 : Fin 2)
  else if value = 4 then (0 : Fin 2)
  else (0 : Fin 2)

def ontoLeftSection (value : Fin 2) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else (2 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftTable.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5)
  else if value = 1 then (2 : Fin 5)
  else if value = 2 then (0 : Fin 5)
  else if value = 3 then (1 : Fin 5)
  else if value = 4 then (3 : Fin 5)
  else (4 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (3 : Fin 6)
  else if value = 2 then (1 : Fin 6)
  else if value = 3 then (4 : Fin 6)
  else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup rightTable.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftTable.semigroup rightTable.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

/-- Conditional endpoint shell: the unrestricted normalizer remains an explicit input. -/
theorem representative_basis_of_normalizer
    (normalizer : IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis) :
    BasisFor table.semigroup basis :=
  IntersectionNormalizer.basisFor normalizer leftModels rightModels pair

/-- Conditional opposite-orientation shell; it does not assert an unproved normalizer. -/
theorem opposite_basis_of_normalizer
    (normalizer : IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of_normalizer normalizer).oppositeReversed

end S6_11262

namespace S6_8448

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (0 : Fin 6)
    else (0 : Fin 6)
  else if left = 1 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (1 : Fin 6)
    else (1 : Fin 6)
  else if left = 2 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (0 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (2 : Fin 6)
    else (2 : Fin 6)
  else if left = 3 then
    if right = 0 then (3 : Fin 6)
    else if right = 1 then (3 : Fin 6)
    else if right = 2 then (3 : Fin 6)
    else if right = 3 then (3 : Fin 6)
    else if right = 4 then (3 : Fin 6)
    else (3 : Fin 6)
  else if left = 4 then
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (0 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (5 : Fin 6)
  else
    if right = 0 then (0 : Fin 6)
    else if right = 1 then (2 : Fin 6)
    else if right = 2 then (2 : Fin 6)
    else if right = 3 then (0 : Fin 6)
    else if right = 4 then (4 : Fin 6)
    else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def ontoLeftMap (value : Fin 6) : Fin 2 :=
  if value = 0 then (0 : Fin 2)
  else if value = 1 then (0 : Fin 2)
  else if value = 2 then (0 : Fin 2)
  else if value = 3 then (1 : Fin 2)
  else if value = 4 then (0 : Fin 2)
  else (0 : Fin 2)

def ontoLeftSection (value : Fin 2) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else (3 : Fin 6)

def ontoLeft : SplitSurjection table.semigroup leftTable.semigroup where
  toFun := ontoLeftMap
  map_mul := by decide
  preimage := ontoLeftSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoRightMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5)
  else if value = 1 then (1 : Fin 5)
  else if value = 2 then (2 : Fin 5)
  else if value = 3 then (0 : Fin 5)
  else if value = 4 then (3 : Fin 5)
  else (4 : Fin 5)

def ontoRightSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6)
  else if value = 1 then (1 : Fin 6)
  else if value = 2 then (2 : Fin 6)
  else if value = 3 then (4 : Fin 6)
  else (5 : Fin 6)

def ontoRight : SplitSurjection table.semigroup rightTable.semigroup where
  toFun := ontoRightMap
  map_mul := by decide
  preimage := ontoRightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup leftTable.semigroup rightTable.semigroup where
  left := ontoLeft
  right := ontoRight
  jointlyInjective := by
    intro left right
    exact by decide +revert

/-- Conditional endpoint shell: the unrestricted normalizer remains an explicit input. -/
theorem representative_basis_of_normalizer
    (normalizer : IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis) :
    BasisFor table.semigroup basis :=
  IntersectionNormalizer.basisFor normalizer leftModels rightModels pair

/-- Conditional opposite-orientation shell; it does not assert an unproved normalizer. -/
theorem opposite_basis_of_normalizer
    (normalizer : IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis) :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  (representative_basis_of_normalizer normalizer).oppositeReversed

end S6_8448

namespace Seed

/-- The previously kernel-verified B4 system is the literal displayed prefix. -/
theorem publishedBasis_eq_displayedPrefix :
    SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.publishedBasis =
      [law00, law01, law02, law03] := by
  rfl

/-- Every independently complete historical B4 law is present unchanged in
the authenticated twenty-law rank-021 displayed list. -/
theorem publishedAxiomsDeriveDisplayed
    (identity : Identity Nat)
    (member :
      identity ∈
        SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.publishedBasis) :
    Derives basis identity.lhs identity.rhs := by
  rw [publishedBasis_eq_displayedPrefix] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact FiniteWitnesses.law00_derivation
  · exact FiniteWitnesses.law01_derivation
  · exact FiniteWitnesses.law02_derivation
  · exact FiniteWitnesses.law03_derivation

/-- The authenticated staged left factor and the historical product-hull
left factor are the same concrete left-zero semigroup. -/
theorem historicalLeftValidity
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    identity.SatisfiedBy
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.G := by
  change identity.SatisfiedBy leftZeroTwo.semigroup at valid
  change
    identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S2_4.table.semigroup
  rw [SemigroupBasis.CoRoots.S5_793Invariant.catalogueS2_4_table_eq_leftZeroTwo]
  exact valid

/-- The authenticated opposite right factor is definitionally the historical
Lee--Zhang product-hull right factor. -/
theorem historicalRightValidity
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.SatisfiedBy
      SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.H := by
  exact valid

/-- Apply the independently kernel-verified unrestricted B4 obligation,
then transport its genuine derivation into the exact displayed B20 basis. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have historical :=
    SemigroupBasis.CoRoots.Order6LeeZhang23_9Completeness.derivationalObligation
      identity
      (historicalLeftValidity identity leftValid)
      (historicalRightValidity identity rightValid)
  exact historical.transport publishedAxiomsDeriveDisplayed

/-- Assemble the reviewed intersection only after genuine unrestricted
factor-pair completeness. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- Certified reusable rank-021 family seed. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_11262_representative_basis :
    BasisFor S6_11262.table.semigroup basis :=
  S6_11262.representative_basis_of_normalizer normalizer

theorem s6_11262_opposite_basis :
    BasisFor S6_11262.table.semigroup.opposite (reversedBasis basis) :=
  S6_11262.opposite_basis_of_normalizer normalizer

theorem s6_8448_representative_basis :
    BasisFor S6_8448.table.semigroup basis :=
  S6_8448.representative_basis_of_normalizer normalizer

theorem s6_8448_opposite_basis :
    BasisFor S6_8448.table.semigroup.opposite (reversedBasis basis) :=
  S6_8448.opposite_basis_of_normalizer normalizer

/-- Reviewed transport preserves all explicit displayed-law derivations and
independent unrestricted validity implications for both target factors. -/
noncomputable def transportedNormalizer
    {A : Type u} {B : Type v}
    {targetLeft : Semigroup A} {targetRight : Semigroup B}
    {targetBasis : List (Identity Nat)}
    (lawDerivations :
      ∀ law : Identity Nat,
        law ∈ basis → Derives targetBasis law.lhs law.rhs)
    (leftTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetLeft →
          identity.SatisfiedBy leftTable.semigroup)
    (rightTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetRight →
          identity.SatisfiedBy rightTable.semigroup) :
    IntersectionNormalizer targetLeft targetRight targetBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    normalizer lawDerivations leftTheory rightTheory

end Seed

end SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank021ShardedFiniteBase
