import SemigroupBasis.CoRoots.S5_342
import SemigroupBasis.Generated.CatalogueOrder5Part03
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.Generated.S4_76
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_342Family

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_342

namespace S5_342

private def firstRepeatedQuotient :
    SplitSurjection Generated.Catalogue.S5_342.table.semigroup
      firstRepeatedMarkerFour.semigroup where
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

private def finalMarkerQuotient :
    SplitSurjection Generated.Catalogue.S5_342.table.semigroup
      finalMarkerThree.semigroup where
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

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_342.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_342.table (by decide)

theorem valid_firstRepeatedMarkerFour (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_342.table.semigroup) :
    e.SatisfiedBy firstRepeatedMarkerFour.semigroup :=
  firstRepeatedQuotient.pushforwardIdentity e valid

theorem valid_finalMarkerThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_342.table.semigroup) :
    e.SatisfiedBy finalMarkerThree.semigroup :=
  finalMarkerQuotient.pushforwardIdentity e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_342.table.semigroup basis :=
  basis_complete_of_factors Generated.Catalogue.S5_342.table
    models valid_firstRepeatedMarkerFour valid_finalMarkerThree

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_342.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_342

namespace S5_353

private def firstRepeatedPowerEmbedding :
    Embedding firstRepeatedMarkerFour.semigroup
      (Generated.Catalogue.S5_353.table.semigroup.pi (Fin 2)) where
  toFun := fun a i =>
    if i.val = 0 then
      if a.val = 0 then ⟨0, by decide⟩ else
        if a.val = 1 then ⟨2, by decide⟩ else
          if a.val = 2 then ⟨0, by decide⟩ else ⟨3, by decide⟩
    else
      if a.val = 0 then ⟨3, by decide⟩ else
        if a.val = 1 then ⟨3, by decide⟩ else
          if a.val = 2 then ⟨4, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    funext i
    exact by decide +revert
  injective := by
    intro a b h
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    clear h
    exact by decide +revert

private def finalMarkerQuotient :
    SplitSurjection Generated.Catalogue.S5_353.table.semigroup
      finalMarkerThree.semigroup where
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

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_353.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_353.table (by decide)

theorem valid_firstRepeatedMarkerFour (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_353.table.semigroup) :
    e.SatisfiedBy firstRepeatedMarkerFour.semigroup := by
  have powerValid :=
    e.satisfiedByPi Generated.Catalogue.S5_353.table.semigroup
      (Fin 2) valid
  exact firstRepeatedPowerEmbedding.pullback_identity e powerValid

theorem valid_finalMarkerThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_353.table.semigroup) :
    e.SatisfiedBy finalMarkerThree.semigroup :=
  finalMarkerQuotient.pushforwardIdentity e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_353.table.semigroup basis :=
  basis_complete_of_factors Generated.Catalogue.S5_353.table
    models valid_firstRepeatedMarkerFour valid_finalMarkerThree

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_353.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_353

namespace S5_591

private def firstRepeatedQuotient :
    SplitSurjection Generated.Catalogue.S5_591.table.semigroup
      Generated.S4_76.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨2, by decide⟩ else
      if a.val = 1 then ⟨2, by decide⟩ else
        if a.val = 2 then ⟨0, by decide⟩ else
          if a.val = 3 then ⟨1, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨2, by decide⟩ else
      if b.val = 1 then ⟨3, by decide⟩ else
        if b.val = 2 then ⟨0, by decide⟩ else ⟨4, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

private def finalMarkerQuotient :
    SplitSurjection Generated.Catalogue.S5_591.table.semigroup
      finalMarkerThree.semigroup where
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

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_591.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_591.table (by decide)

theorem valid_firstRepeatedMarkerFour (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_591.table.semigroup) :
    e.SatisfiedBy firstRepeatedMarkerFour.semigroup := by
  have validS4_76 := firstRepeatedQuotient.pushforwardIdentity e valid
  have derivation :=
    Generated.S4_76.representative_basis.2 e validS4_76
  intro valuation
  exact derivation.sound firstRepeatedMarkerFourBasis_models valuation

theorem valid_finalMarkerThree (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_591.table.semigroup) :
    e.SatisfiedBy finalMarkerThree.semigroup :=
  finalMarkerQuotient.pushforwardIdentity e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_591.table.semigroup basis :=
  basis_complete_of_factors Generated.Catalogue.S5_591.table
    models valid_firstRepeatedMarkerFour valid_finalMarkerThree

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_591.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_591

end SemigroupBasis.CoRoots.S5_342Family
