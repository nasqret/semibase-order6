import SemigroupBasis.CoRoots.S5_344
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder5Part03
import SemigroupBasis.Generated.CatalogueOrder5Part04
import SemigroupBasis.Generated.Order4RootTransfersLayer1
import SemigroupBasis.Generated.S4_74
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_344Family

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_344

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

private def finiteBasis : List (Identity (Fin 4)) :=
  basis.map fun e => e.map toFinFour

private theorem basis_roundTrip_checked :
    basis.all (fun e =>
      decide ((e.map toFinFour).map Fin.val = e)) = true := by
  decide

private theorem basis_roundTrip
    (e : Identity Nat) (member : e ∈ basis) :
    (e.map toFinFour).map Fin.val = e := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) e member

private theorem models_of_finite_checks
    (T : FiniteTable)
    (checked : finiteBasis.all T.checkIdentity = true) :
    Models T.semigroup basis := by
  intro e member
  have finiteMember : e.map toFinFour ∈ finiteBasis :=
    List.mem_map.mpr ⟨e, member, rfl⟩
  have finiteValid :=
    T.checkIdentityNat_sound (e.map toFinFour)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip e member] at finiteValid
  exact finiteValid

private theorem s3_6_catalogue_eq_finalMarkerThree :
    Generated.Catalogue.S3_6.table = finalMarkerThree := by
  unfold Generated.Catalogue.S3_6.table finalMarkerThree
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

private theorem s4_74_catalogue_eq_firstCappedMultiplicityFour :
    Generated.Catalogue.S4_74.table =
      firstCappedMultiplicityFour := by
  rw [← Generated.S4_74.table_eq_canonical_catalogue]
  exact Generated.S4_74.table_eq_catalogue_model

private theorem valid_firstCapped_of_s4_79
    (e : Identity Nat)
    (valid :
      e.SatisfiedBy
        Generated.Catalogue.S4_79.table.semigroup) :
    e.SatisfiedBy firstCappedMultiplicityFour.semigroup := by
  have derivation :=
    Generated.Order4RootTransfers.S4_79.representative_basis.2 e valid
  intro valuation
  exact derivation.sound firstCappedMultiplicityFourBasis_models valuation

namespace S5_344

private def finalMarkerQuotient :
    SplitSurjection Generated.Catalogue.S5_344.table.semigroup
      Generated.Catalogue.S3_6.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨0, by decide⟩ else
          if a.val = 3 then ⟨0, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨1, by decide⟩ else ⟨4, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

private def firstCappedQuotient :
    SplitSurjection Generated.Catalogue.S5_344.table.semigroup
      Generated.Catalogue.S4_74.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨0, by decide⟩ else
        if a.val = 2 then ⟨1, by decide⟩ else
          if a.val = 3 then ⟨2, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨2, by decide⟩ else
        if b.val = 2 then ⟨3, by decide⟩ else ⟨4, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_344.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_344.table (by decide)

theorem valid_firstCappedMultiplicityFour (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_344.table.semigroup) :
    e.SatisfiedBy firstCappedMultiplicityFour.semigroup := by
  rw [← s4_74_catalogue_eq_firstCappedMultiplicityFour]
  exact firstCappedQuotient.pushforwardIdentity e valid

theorem valid_finalMarkerThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_344.table.semigroup) :
    e.SatisfiedBy finalMarkerThree.semigroup := by
  rw [← s3_6_catalogue_eq_finalMarkerThree]
  exact finalMarkerQuotient.pushforwardIdentity e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_344.table.semigroup basis :=
  basis_complete_of_factors Generated.Catalogue.S5_344.table
    models valid_firstCappedMultiplicityFour valid_finalMarkerThree

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_344.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_344

namespace S5_356

private def finalMarkerQuotient :
    SplitSurjection Generated.Catalogue.S5_356.table.semigroup
      Generated.Catalogue.S3_6.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨0, by decide⟩ else
          if a.val = 3 then ⟨2, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨1, by decide⟩ else ⟨3, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

private def firstCappedQuotient :
    SplitSurjection Generated.Catalogue.S5_356.table.semigroup
      Generated.Catalogue.S4_79.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨0, by decide⟩ else
        if a.val = 2 then ⟨1, by decide⟩ else
          if a.val = 3 then ⟨2, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨2, by decide⟩ else
        if b.val = 2 then ⟨3, by decide⟩ else ⟨4, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_356.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_356.table (by decide)

theorem valid_firstCappedMultiplicityFour (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_356.table.semigroup) :
    e.SatisfiedBy firstCappedMultiplicityFour.semigroup :=
  valid_firstCapped_of_s4_79 e
    (firstCappedQuotient.pushforwardIdentity e valid)

theorem valid_finalMarkerThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_356.table.semigroup) :
    e.SatisfiedBy finalMarkerThree.semigroup := by
  rw [← s3_6_catalogue_eq_finalMarkerThree]
  exact finalMarkerQuotient.pushforwardIdentity e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_356.table.semigroup basis :=
  basis_complete_of_factors Generated.Catalogue.S5_356.table
    models valid_firstCappedMultiplicityFour valid_finalMarkerThree

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_356.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_356

namespace S5_373

private def finalMarkerQuotient :
    SplitSurjection Generated.Catalogue.S5_373.table.semigroup
      Generated.Catalogue.S3_6.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨0, by decide⟩ else
        if a.val = 2 then ⟨1, by decide⟩ else
          if a.val = 3 then ⟨0, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨2, by decide⟩ else ⟨4, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

private def firstCappedQuotient :
    SplitSurjection Generated.Catalogue.S5_373.table.semigroup
      Generated.Catalogue.S4_74.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨1, by decide⟩ else
          if a.val = 3 then ⟨2, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨1, by decide⟩ else
        if b.val = 2 then ⟨3, by decide⟩ else ⟨4, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_373.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_373.table (by decide)

theorem valid_firstCappedMultiplicityFour (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_373.table.semigroup) :
    e.SatisfiedBy firstCappedMultiplicityFour.semigroup := by
  rw [← s4_74_catalogue_eq_firstCappedMultiplicityFour]
  exact firstCappedQuotient.pushforwardIdentity e valid

theorem valid_finalMarkerThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_373.table.semigroup) :
    e.SatisfiedBy finalMarkerThree.semigroup := by
  rw [← s3_6_catalogue_eq_finalMarkerThree]
  exact finalMarkerQuotient.pushforwardIdentity e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_373.table.semigroup basis :=
  basis_complete_of_factors Generated.Catalogue.S5_373.table
    models valid_firstCappedMultiplicityFour valid_finalMarkerThree

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_373.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_373

namespace S5_408

private def finalMarkerQuotient :
    SplitSurjection Generated.Catalogue.S5_408.table.semigroup
      Generated.Catalogue.S3_6.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨0, by decide⟩ else
        if a.val = 2 then ⟨1, by decide⟩ else
          if a.val = 3 then ⟨2, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨2, by decide⟩ else ⟨3, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

private def firstCappedQuotient :
    SplitSurjection Generated.Catalogue.S5_408.table.semigroup
      Generated.Catalogue.S4_79.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨1, by decide⟩ else
          if a.val = 3 then ⟨2, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨1, by decide⟩ else
        if b.val = 2 then ⟨3, by decide⟩ else ⟨4, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_408.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_408.table (by decide)

theorem valid_firstCappedMultiplicityFour (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_408.table.semigroup) :
    e.SatisfiedBy firstCappedMultiplicityFour.semigroup :=
  valid_firstCapped_of_s4_79 e
    (firstCappedQuotient.pushforwardIdentity e valid)

theorem valid_finalMarkerThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_408.table.semigroup) :
    e.SatisfiedBy finalMarkerThree.semigroup := by
  rw [← s3_6_catalogue_eq_finalMarkerThree]
  exact finalMarkerQuotient.pushforwardIdentity e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_408.table.semigroup basis :=
  basis_complete_of_factors Generated.Catalogue.S5_408.table
    models valid_firstCappedMultiplicityFour valid_finalMarkerThree

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_408.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_408

end SemigroupBasis.CoRoots.S5_344Family
