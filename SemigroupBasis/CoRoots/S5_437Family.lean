import SemigroupBasis.CoRoots.S5_437Factors
import SemigroupBasis.CoRoots.S5_437Normalization

namespace SemigroupBasis.CoRoots.S5_437Family

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_437

namespace S5_437

theorem valid_head_eq (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_437.table.semigroup) :
    e.lhs.head = e.rhs.head :=
  SemigroupBasis.CoRoots.S4_90.valid_head_eq e <|
    SemigroupBasis.CoRoots.S5_437Factors.S5_437.valid_suffixParity
      e valid

theorem valid_support (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_437.table.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList :=
  SemigroupBasis.CoRoots.S4_90.valid_support e <|
    SemigroupBasis.CoRoots.S5_437Factors.S5_437.valid_suffixParity
      e valid

theorem valid_parity (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_437.table.semigroup) :
    ∀ z, e.lhs.toList.count z % 2 =
      e.rhs.toList.count z % 2 :=
  SemigroupBasis.CoRoots.S4_90.valid_parity e <|
    SemigroupBasis.CoRoots.S5_437Factors.S5_437.valid_suffixParity
      e valid

theorem valid_simpleFinal (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_437.table.semigroup) :
    ∀ z,
      ((splitPrefixFinal e.lhs).2 = z ∧
          z ∉ (splitPrefixFinal e.lhs).1) ↔
        ((splitPrefixFinal e.rhs).2 = z ∧
          z ∉ (splitPrefixFinal e.rhs).1) := by
  have markerValid :=
    SemigroupBasis.CoRoots.S5_437Factors.S5_437.valid_finalMarker
      e valid
  rw [
    SemigroupBasis.CoRoots.S5_437Factors.s3_6_catalogue_eq_finalMarkerThree
  ] at markerValid
  exact finalMarkerValid_splitSimpleFinal_iff e markerValid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_437.table.semigroup basis :=
  basis_complete_of_parity_first_final
    Generated.Catalogue.S5_437.table.semigroup
    SemigroupBasis.CoRoots.S5_437Factors.S5_437.models
    valid_head_eq valid_support valid_parity valid_simpleFinal

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_437.table.semigroup.opposite
      oppositeBasis := by
  simpa [oppositeBasis] using basis_complete.oppositeReversed

end S5_437

namespace S5_460

theorem valid_head_eq (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_460.table.semigroup) :
    e.lhs.head = e.rhs.head :=
  SemigroupBasis.CoRoots.S4_90.valid_head_eq e <|
    SemigroupBasis.CoRoots.S5_437Factors.S5_460.valid_suffixParity
      e valid

theorem valid_support (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_460.table.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList :=
  SemigroupBasis.CoRoots.S4_90.valid_support e <|
    SemigroupBasis.CoRoots.S5_437Factors.S5_460.valid_suffixParity
      e valid

theorem valid_parity (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_460.table.semigroup) :
    ∀ z, e.lhs.toList.count z % 2 =
      e.rhs.toList.count z % 2 :=
  SemigroupBasis.CoRoots.S4_90.valid_parity e <|
    SemigroupBasis.CoRoots.S5_437Factors.S5_460.valid_suffixParity
      e valid

theorem valid_simpleFinal (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_460.table.semigroup) :
    ∀ z,
      ((splitPrefixFinal e.lhs).2 = z ∧
          z ∉ (splitPrefixFinal e.lhs).1) ↔
        ((splitPrefixFinal e.rhs).2 = z ∧
          z ∉ (splitPrefixFinal e.rhs).1) := by
  have markerValid :=
    SemigroupBasis.CoRoots.S5_437Factors.S5_460.valid_finalMarker
      e valid
  rw [
    SemigroupBasis.CoRoots.S5_437Factors.s3_6_catalogue_eq_finalMarkerThree
  ] at markerValid
  exact finalMarkerValid_splitSimpleFinal_iff e markerValid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_460.table.semigroup basis :=
  basis_complete_of_parity_first_final
    Generated.Catalogue.S5_460.table.semigroup
    SemigroupBasis.CoRoots.S5_437Factors.S5_460.models
    valid_head_eq valid_support valid_parity valid_simpleFinal

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_460.table.semigroup.opposite
      oppositeBasis := by
  simpa [oppositeBasis] using basis_complete.oppositeReversed

end S5_460

namespace S5_575

theorem valid_head_eq (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_575.table.semigroup) :
    e.lhs.head = e.rhs.head :=
  SemigroupBasis.CoRoots.S4_90Family.valid_head_eq e <|
    SemigroupBasis.CoRoots.S5_437Factors.S5_575.valid_suffixParity
      e valid

theorem valid_support (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_575.table.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList :=
  SemigroupBasis.CoRoots.S4_90Family.valid_support e <|
    SemigroupBasis.CoRoots.S5_437Factors.S5_575.valid_suffixParity
      e valid

theorem valid_parity (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_575.table.semigroup) :
    ∀ z, e.lhs.toList.count z % 2 =
      e.rhs.toList.count z % 2 :=
  SemigroupBasis.CoRoots.S4_90Family.valid_parity e <|
    SemigroupBasis.CoRoots.S5_437Factors.S5_575.valid_suffixParity
      e valid

theorem valid_simpleFinal (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_575.table.semigroup) :
    ∀ z,
      ((splitPrefixFinal e.lhs).2 = z ∧
          z ∉ (splitPrefixFinal e.lhs).1) ↔
        ((splitPrefixFinal e.rhs).2 = z ∧
          z ∉ (splitPrefixFinal e.rhs).1) := by
  have markerValid :=
    SemigroupBasis.CoRoots.S5_437Factors.S5_575.valid_finalMarker
      e valid
  rw [
    SemigroupBasis.CoRoots.S5_437Factors.s3_6_catalogue_eq_finalMarkerThree
  ] at markerValid
  exact finalMarkerValid_splitSimpleFinal_iff e markerValid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_575.table.semigroup basis :=
  basis_complete_of_parity_first_final
    Generated.Catalogue.S5_575.table.semigroup
    SemigroupBasis.CoRoots.S5_437Factors.S5_575.models
    valid_head_eq valid_support valid_parity valid_simpleFinal

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_575.table.semigroup.opposite
      oppositeBasis := by
  simpa [oppositeBasis] using basis_complete.oppositeReversed

end S5_575

end SemigroupBasis.CoRoots.S5_437Family
