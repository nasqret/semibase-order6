import SemigroupBasis.CoRoots.S5_120
import SemigroupBasis.Generated.CatalogueOrder5Part01
import SemigroupBasis.Generated.CatalogueOrder5Part02
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_120Family

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_120

namespace S5_120

private def cyclicEmbedding :
    Embedding cyclicTwo.semigroup
      Generated.Catalogue.S5_120.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

private def simpleEndpointsQuotient :
    SplitSurjection Generated.Catalogue.S5_120.table.semigroup
      simpleEndpointsFour.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨2, by decide⟩ else
          if a.val = 3 then ⟨0, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨1, by decide⟩ else
        if b.val = 2 then ⟨2, by decide⟩ else ⟨4, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_120.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_120.table (by decide)

theorem valid_simpleEndpoints (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_120.table.semigroup) :
    e.SatisfiedBy simpleEndpointsFour.semigroup :=
  simpleEndpointsQuotient.pushforwardIdentity e valid

theorem valid_cyclicTwo (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_120.table.semigroup) :
    e.SatisfiedBy cyclicTwo.semigroup :=
  cyclicEmbedding.pullback_identity e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_120.table.semigroup basis :=
  basis_complete_of_factors Generated.Catalogue.S5_120.table
    models valid_simpleEndpoints valid_cyclicTwo

end S5_120

namespace S5_131

private def cyclicEmbedding :
    Embedding cyclicTwo.semigroup
      Generated.Catalogue.S5_131.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

private def simpleEndpointsQuotient :
    SplitSurjection Generated.Catalogue.S5_131.table.semigroup
      simpleEndpointsFour.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨0, by decide⟩ else
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
    Models Generated.Catalogue.S5_131.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_131.table (by decide)

theorem valid_simpleEndpoints (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_131.table.semigroup) :
    e.SatisfiedBy simpleEndpointsFour.semigroup :=
  simpleEndpointsQuotient.pushforwardIdentity e valid

theorem valid_cyclicTwo (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_131.table.semigroup) :
    e.SatisfiedBy cyclicTwo.semigroup :=
  cyclicEmbedding.pullback_identity e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_131.table.semigroup basis :=
  basis_complete_of_factors Generated.Catalogue.S5_131.table
    models valid_simpleEndpoints valid_cyclicTwo

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_131.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_131

namespace S5_142

private def cyclicEmbedding :
    Embedding cyclicTwo.semigroup
      Generated.Catalogue.S5_142.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

private def simpleEndpointsQuotient :
    SplitSurjection Generated.Catalogue.S5_142.table.semigroup
      simpleEndpointsFour.semigroup where
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
    Models Generated.Catalogue.S5_142.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_142.table (by decide)

theorem valid_simpleEndpoints (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_142.table.semigroup) :
    e.SatisfiedBy simpleEndpointsFour.semigroup :=
  simpleEndpointsQuotient.pushforwardIdentity e valid

theorem valid_cyclicTwo (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_142.table.semigroup) :
    e.SatisfiedBy cyclicTwo.semigroup :=
  cyclicEmbedding.pullback_identity e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_142.table.semigroup basis :=
  basis_complete_of_factors Generated.Catalogue.S5_142.table
    models valid_simpleEndpoints valid_cyclicTwo

end S5_142

namespace S5_245

private def cyclicEmbedding :
    Embedding cyclicTwo.semigroup
      Generated.Catalogue.S5_245.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨3, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

private def simpleEndpointsQuotient :
    SplitSurjection Generated.Catalogue.S5_245.table.semigroup
      simpleEndpointsFour.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨2, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨1, by decide⟩ else
        if b.val = 2 then ⟨2, by decide⟩ else ⟨3, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_245.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_245.table (by decide)

theorem valid_simpleEndpoints (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_245.table.semigroup) :
    e.SatisfiedBy simpleEndpointsFour.semigroup :=
  simpleEndpointsQuotient.pushforwardIdentity e valid

theorem valid_cyclicTwo (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_245.table.semigroup) :
    e.SatisfiedBy cyclicTwo.semigroup :=
  cyclicEmbedding.pullback_identity e valid

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_245.table.semigroup basis :=
  basis_complete_of_factors Generated.Catalogue.S5_245.table
    models valid_simpleEndpoints valid_cyclicTwo

end S5_245

end SemigroupBasis.CoRoots.S5_120Family
