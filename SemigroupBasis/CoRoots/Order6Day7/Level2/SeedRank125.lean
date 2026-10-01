import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15opS5_791Transfer
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer

/-!
# Rank125 seed transport for the two missing owned class consumers

The unrestricted eleven-law transfer already exists in the imported Layer-C
module. It is reused, not reproved or inferred from the finite screen.
The two actual class tables have split maps to S5_807, not S5_791. Their
normalizer therefore uses the approved transport API with an explicit
unrestricted S5_807-to-S5_791 theory implication from the certified common
five-law factor basis.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.Level2.Rank125

open SemigroupBasis
open SemigroupBasis.CoRoots

def basis : List (Identity Nat) :=
  [
    ⟨Word.mk 0 [0], Word.mk 0 [0, 0]⟩,
    ⟨Word.mk 0 [0, 1, 0], Word.mk 0 [1, 0]⟩,
    ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 0, 0]⟩,
    ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 0, 1, 0]⟩,
    ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 1, 0]⟩,
    ⟨Word.mk 0 [1, 0, 1, 2], Word.mk 0 [1, 0, 2]⟩,
    ⟨Word.mk 0 [1, 0, 2, 0], Word.mk 0 [1, 2, 0]⟩,
    ⟨Word.mk 0 [1, 0, 2, 1], Word.mk 0 [1, 2, 0, 1]⟩,
    ⟨Word.mk 0 [1, 1, 2, 0], Word.mk 0 [1, 2, 0]⟩,
    ⟨Word.mk 0 [1, 2, 0], Word.mk 0 [1, 2, 1, 0]⟩,
    ⟨Word.mk 0 [1, 2, 0], Word.mk 0 [1, 2, 2, 0]⟩
  ]

theorem basis_eq_existing :
    basis = Order6L3HeavyRank2.basisS3_15opS5_791 := rfl

abbrev leftTable : FiniteTable := Order6L3HeavyRank2.s3_15OppositeTable
abbrev originalRightTable : FiniteTable := Generated.Catalogue.S5_791.table
abbrev rightTable : FiniteTable := Generated.Catalogue.S5_807.table

/-- The already complete Layer-C intersection, refined through the common
quotient interface. No new unrestricted assumption is introduced. -/
noncomputable def originalNormalizer :
    IntersectionNormalizer leftTable.semigroup originalRightTable.semigroup basis := by
  simpa only [basis_eq_existing] using
    Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
      Order6L3HeavyRank2.S3_15opS5_791.intersectionBasisS5_791

/-- Actual factor-theory transport, not an isomorphism or self-duality claim. -/
theorem rightTheoryFrom807 (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.SatisfiedBy originalRightTable.semigroup := by
  have derivation := S5_791Family.S5_807.basis_complete.2 identity valid
  intro valuation
  exact derivation.sound S5_791Family.S5_791.models valuation

theorem leftModels : Models leftTable.semigroup basis := by
  simpa only [basis_eq_existing] using Order6L3HeavyRank2.S3_15opS5_791.modelsLeft

theorem rightModels : Models rightTable.semigroup basis := by
  intro identity member valuation
  rw [basis_eq_existing] at member
  have originalValid := Order6L3HeavyRank2.S3_15opS5_791.modelsRight identity member
  have derivation := S5_791Family.S5_791.basis_complete.2 identity originalValid
  exact derivation.sound S5_791Family.S5_807.models valuation

noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  Order6L3HeavyRank2.LayerCCommon.transportNormalizer originalNormalizer
    (fun _ member => Derives.fromBasis member) (fun _ valid => valid) rightTheoryFrom807

theorem derives_of_factor_valid (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  rw [basis_eq_existing]
  exact Order6L3HeavyRank2.S3_15opS5_791.derivesOfFactorValid
    identity leftValid (rightTheoryFrom807 identity rightValid)

def intersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

end SemigroupBasis.CoRoots.Order6Day7.Level2.Rank125
