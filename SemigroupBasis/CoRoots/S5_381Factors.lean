import SemigroupBasis.CoRoots.S5_381
import SemigroupBasis.Examples.FinalMarkerThree
import SemigroupBasis.Generated.CatalogueOrder5Part03
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.Generated.S4_71
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_381Factors

open SemigroupBasis
open SemigroupBasis.Examples

private theorem satisfiedBy_of_joint_homs
    {A : Type u} {B : Type v} {C : Type w} {α : Type z}
    {G : Semigroup A} {H : Semigroup B} {K : Semigroup C}
    (left : Hom G H) (right : Hom G K)
    (joint :
      Function.Injective fun value =>
        (left.toFun value, right.toFun value))
    (identity : Identity α)
    (leftValid : identity.SatisfiedBy H)
    (rightValid : identity.SatisfiedBy K) :
    identity.SatisfiedBy G := by
  intro valuation
  apply joint
  apply Prod.ext
  · change
      left.toFun (G.eval valuation identity.lhs) =
        left.toFun (G.eval valuation identity.rhs)
    rw [left.map_eval, left.map_eval]
    exact leftValid (fun x => left.toFun (valuation x))
  · change
      right.toFun (G.eval valuation identity.lhs) =
        right.toFun (G.eval valuation identity.rhs)
    rw [right.map_eval, right.map_eval]
    exact rightValid (fun x => right.toFun (valuation x))

namespace S5_381

/-- The exact one-based `S4_71` quotient `[1,2,2,3,4]`. -/
def blockQuotient :
    SplitSurjection Generated.Catalogue.S5_381.table.semigroup
      Generated.S4_71.table.semigroup where
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

/-- The exact one-based `finalMarkerThree.opposite` quotient
`[1,1,2,1,3]`. -/
def initialMarkerQuotient :
    SplitSurjection Generated.Catalogue.S5_381.table.semigroup
      finalMarkerThree.semigroup.opposite where
  toFun := fun a =>
    if a.val = 2 then ⟨1, by decide⟩ else
      if a.val = 4 then ⟨2, by decide⟩ else ⟨0, by decide⟩
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

theorem factorPair_injective :
    Function.Injective fun a =>
      (blockQuotient.toFun a, initialMarkerQuotient.toFun a) := by
  intro a b
  revert a b
  decide

theorem valid_s4_71 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_381.table.semigroup) :
    identity.SatisfiedBy Generated.S4_71.table.semigroup :=
  blockQuotient.pushforwardIdentity identity valid

theorem valid_initialMarker (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_381.table.semigroup) :
    identity.SatisfiedBy finalMarkerThree.semigroup.opposite :=
  initialMarkerQuotient.pushforwardIdentity identity valid

theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy
        Generated.Catalogue.S5_381.table.semigroup ↔
      identity.SatisfiedBy Generated.S4_71.table.semigroup ∧
        identity.SatisfiedBy finalMarkerThree.semigroup.opposite := by
  constructor
  · intro valid
    exact ⟨valid_s4_71 identity valid,
      valid_initialMarker identity valid⟩
  · rintro ⟨blockValid, markerValid⟩
    exact satisfiedBy_of_joint_homs
      blockQuotient.toHom initialMarkerQuotient.toHom
      factorPair_injective identity blockValid markerValid

end S5_381

namespace S5_610

/-- The exact one-based `S4_71` quotient `[1,2,3,3,4]`. -/
def blockQuotient :
    SplitSurjection Generated.Catalogue.S5_610.table.semigroup
      Generated.S4_71.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨2, by decide⟩ else
          if a.val = 3 then ⟨2, by decide⟩ else ⟨3, by decide⟩
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

/-- The exact one-based `finalMarkerThree.opposite` quotient
`[1,1,1,2,3]`. -/
def initialMarkerQuotient :
    SplitSurjection Generated.Catalogue.S5_610.table.semigroup
      finalMarkerThree.semigroup.opposite where
  toFun := fun a =>
    if a.val = 3 then ⟨1, by decide⟩ else
      if a.val = 4 then ⟨2, by decide⟩ else ⟨0, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨3, by decide⟩ else ⟨4, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem factorPair_injective :
    Function.Injective fun a =>
      (blockQuotient.toFun a, initialMarkerQuotient.toFun a) := by
  intro a b
  revert a b
  decide

theorem valid_s4_71 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_610.table.semigroup) :
    identity.SatisfiedBy Generated.S4_71.table.semigroup :=
  blockQuotient.pushforwardIdentity identity valid

theorem valid_initialMarker (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_610.table.semigroup) :
    identity.SatisfiedBy finalMarkerThree.semigroup.opposite :=
  initialMarkerQuotient.pushforwardIdentity identity valid

theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy
        Generated.Catalogue.S5_610.table.semigroup ↔
      identity.SatisfiedBy Generated.S4_71.table.semigroup ∧
        identity.SatisfiedBy finalMarkerThree.semigroup.opposite := by
  constructor
  · intro valid
    exact ⟨valid_s4_71 identity valid,
      valid_initialMarker identity valid⟩
  · rintro ⟨blockValid, markerValid⟩
    exact satisfiedBy_of_joint_homs
      blockQuotient.toHom initialMarkerQuotient.toHom
      factorPair_injective identity blockValid markerValid

end S5_610

end SemigroupBasis.CoRoots.S5_381Factors
