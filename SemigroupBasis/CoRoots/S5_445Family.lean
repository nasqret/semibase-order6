import SemigroupBasis.CoRoots.S5_445Factors
import SemigroupBasis.Examples.HeadSortedPeriodTwoFromTwo
import SemigroupBasis.Examples.LeftZeroTwo
import SemigroupBasis.Generated.S3_15
import SemigroupBasis.Generated.S4_28
import SemigroupBasis.Generated.S4_48
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_445

open SemigroupBasis
open SemigroupBasis.Examples

/-- The common exact basis for the `S5_445`, `S5_467`, and `S5_633`
identity classes:
`xx = xxxx`, `xxy = xyx`, and `xyz = xzy`. -/
def basis : List (Identity Nat) :=
  headSortedPeriodTwoFromTwoBasis

end SemigroupBasis.CoRoots.S5_445

namespace SemigroupBasis.CoRoots.S5_445Family

open SemigroupBasis
open SemigroupBasis.Examples

private theorem catalogueS2_4_table_eq_leftZeroTwo :
    Generated.Catalogue.S2_4.table = leftZeroTwo := by
  unfold Generated.Catalogue.S2_4.table
    Generated.Catalogue.S2_4.mul leftZeroTwo
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

private theorem leftZeroValid_head_eq
    (e : Identity Nat)
    (valid : e.SatisfiedBy leftZeroTwo.semigroup) :
    e.lhs.head = e.rhs.head := by
  apply Decidable.byContradiction
  intro headsNe
  let valuation : Nat → Fin 2 :=
    fun z => if z = e.lhs.head then 0 else 1
  have evaluated := valid valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm headsNe] at evaluated

namespace S5_445

theorem models :
    Models Generated.Catalogue.S5_445.table.semigroup
      SemigroupBasis.CoRoots.S5_445.basis := by
  simpa only [SemigroupBasis.CoRoots.S5_445.basis] using
    SemigroupBasis.CoRoots.S5_445Factors.S5_445.models

theorem valid_head
    (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_445.table.semigroup) :
    e.lhs.head = e.rhs.head := by
  have factorValid :=
    SemigroupBasis.CoRoots.S5_445Factors.S5_445.valid_s3_15 e valid
  rw [← Generated.S3_15.table_eq_canonical_catalogue,
    Generated.S3_15.table_eq_catalogue_model] at factorValid
  exact leftNormalBandFifteenValid_head_eq e factorValid

theorem valid_exponent
    (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_445.table.semigroup) :
    ∀ z,
      periodTwoFromTwoExponent (e.lhs.toList.count z) =
        periodTwoFromTwoExponent (e.rhs.toList.count z) := by
  have factorValid :=
    SemigroupBasis.CoRoots.S5_445Factors.S5_445.valid_s4_28 e valid
  rw [← Generated.S4_28.table_eq_canonical_catalogue] at factorValid
  exact Generated.S4_28.representative_separates e factorValid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_445.table.semigroup
      SemigroupBasis.CoRoots.S5_445.basis := by
  simpa only [SemigroupBasis.CoRoots.S5_445.basis] using
    headSortedPeriodTwoFromTwoBasis_complete_of_separates
      Generated.Catalogue.S5_445.table models valid_head valid_exponent

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_445.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_445.basis) :=
  basis_complete.oppositeReversed

end S5_445

namespace S5_633

theorem models :
    Models Generated.Catalogue.S5_633.table.semigroup
      SemigroupBasis.CoRoots.S5_445.basis := by
  simpa only [SemigroupBasis.CoRoots.S5_445.basis] using
    SemigroupBasis.CoRoots.S5_445Factors.S5_633.models

theorem valid_head
    (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_633.table.semigroup) :
    e.lhs.head = e.rhs.head := by
  have factorValid :=
    SemigroupBasis.CoRoots.S5_445Factors.S5_633.valid_s2_4 e valid
  rw [catalogueS2_4_table_eq_leftZeroTwo] at factorValid
  exact leftZeroValid_head_eq e factorValid

theorem valid_exponent
    (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_633.table.semigroup) :
    ∀ z,
      periodTwoFromTwoExponent (e.lhs.toList.count z) =
        periodTwoFromTwoExponent (e.rhs.toList.count z) := by
  have factorValid :=
    SemigroupBasis.CoRoots.S5_445Factors.S5_633.valid_s4_48 e valid
  rw [← Generated.S4_48.table_eq_canonical_catalogue] at factorValid
  exact Generated.S4_48.representative_separates e factorValid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_633.table.semigroup
      SemigroupBasis.CoRoots.S5_445.basis := by
  simpa only [SemigroupBasis.CoRoots.S5_445.basis] using
    headSortedPeriodTwoFromTwoBasis_complete_of_separates
      Generated.Catalogue.S5_633.table models valid_head valid_exponent

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_633.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_445.basis) :=
  basis_complete.oppositeReversed

end S5_633

end SemigroupBasis.CoRoots.S5_445Family
