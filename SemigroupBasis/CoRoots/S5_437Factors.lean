import SemigroupBasis.CoRoots.S4_90
import SemigroupBasis.CoRoots.S4_90Family
import SemigroupBasis.CoRoots.S5_437
import SemigroupBasis.Examples.FinalMarkerThree
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder5Part04
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_437Factors

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_437

theorem s3_6_catalogue_eq_finalMarkerThree :
    Generated.Catalogue.S3_6.table = finalMarkerThree := by
  unfold Generated.Catalogue.S3_6.table finalMarkerThree
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

private theorem satisfiedBy_of_joint_homs
    {A : Type u} {B : Type v} {C : Type w} {α : Type z}
    {G : Semigroup A} {H : Semigroup B} {K : Semigroup C}
    (left : Hom G H) (right : Hom G K)
    (joint :
      Function.Injective fun value =>
        (left.toFun value, right.toFun value))
    (e : Identity α)
    (leftValid : e.SatisfiedBy H)
    (rightValid : e.SatisfiedBy K) :
    e.SatisfiedBy G := by
  intro valuation
  apply joint
  apply Prod.ext
  · change
      left.toFun (G.eval valuation e.lhs) =
        left.toFun (G.eval valuation e.rhs)
    rw [left.map_eval, left.map_eval]
    exact leftValid (fun x => left.toFun (valuation x))
  · change
      right.toFun (G.eval valuation e.lhs) =
        right.toFun (G.eval valuation e.rhs)
    rw [right.map_eval, right.map_eval]
    exact rightValid (fun x => right.toFun (valuation x))

namespace S5_437

def suffixParityQuotient :
    SplitSurjection Generated.Catalogue.S5_437.table.semigroup
      Generated.Catalogue.S4_90.table.semigroup where
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

def finalMarkerQuotient :
    SplitSurjection Generated.Catalogue.S5_437.table.semigroup
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

theorem factorPair_injective :
    Function.Injective fun a =>
      (suffixParityQuotient.toFun a, finalMarkerQuotient.toFun a) := by
  intro a b
  revert a b
  decide

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_437.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_437.table (by decide)

theorem valid_suffixParity (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_437.table.semigroup) :
    e.SatisfiedBy Generated.Catalogue.S4_90.table.semigroup :=
  suffixParityQuotient.pushforwardIdentity e valid

theorem valid_finalMarker (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_437.table.semigroup) :
    e.SatisfiedBy Generated.Catalogue.S3_6.table.semigroup :=
  finalMarkerQuotient.pushforwardIdentity e valid

theorem valid_iff_factors (e : Identity Nat) :
    e.SatisfiedBy Generated.Catalogue.S5_437.table.semigroup ↔
      e.SatisfiedBy Generated.Catalogue.S4_90.table.semigroup ∧
        e.SatisfiedBy Generated.Catalogue.S3_6.table.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_suffixParity e valid, valid_finalMarker e valid⟩
  · rintro ⟨suffixValid, finalValid⟩
    exact satisfiedBy_of_joint_homs
      suffixParityQuotient.toHom finalMarkerQuotient.toHom
      factorPair_injective e suffixValid finalValid

end S5_437

namespace S5_460

def suffixParityQuotient :
    SplitSurjection Generated.Catalogue.S5_460.table.semigroup
      Generated.Catalogue.S4_90.table.semigroup where
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

def finalMarkerQuotient :
    SplitSurjection Generated.Catalogue.S5_460.table.semigroup
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

theorem factorPair_injective :
    Function.Injective fun a =>
      (suffixParityQuotient.toFun a, finalMarkerQuotient.toFun a) := by
  intro a b
  revert a b
  decide

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_460.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_460.table (by decide)

theorem valid_suffixParity (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_460.table.semigroup) :
    e.SatisfiedBy Generated.Catalogue.S4_90.table.semigroup :=
  suffixParityQuotient.pushforwardIdentity e valid

theorem valid_finalMarker (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_460.table.semigroup) :
    e.SatisfiedBy Generated.Catalogue.S3_6.table.semigroup :=
  finalMarkerQuotient.pushforwardIdentity e valid

theorem valid_iff_factors (e : Identity Nat) :
    e.SatisfiedBy Generated.Catalogue.S5_460.table.semigroup ↔
      e.SatisfiedBy Generated.Catalogue.S4_90.table.semigroup ∧
        e.SatisfiedBy Generated.Catalogue.S3_6.table.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_suffixParity e valid, valid_finalMarker e valid⟩
  · rintro ⟨suffixValid, finalValid⟩
    exact satisfiedBy_of_joint_homs
      suffixParityQuotient.toHom finalMarkerQuotient.toHom
      factorPair_injective e suffixValid finalValid

end S5_460

namespace S5_575

def suffixParityQuotient :
    SplitSurjection Generated.Catalogue.S5_575.table.semigroup
      Generated.Catalogue.S4_93.table.semigroup where
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

def finalMarkerQuotient :
    SplitSurjection Generated.Catalogue.S5_575.table.semigroup
      Generated.Catalogue.S3_6.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨2, by decide⟩ else
          if a.val = 3 then ⟨2, by decide⟩ else ⟨0, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨1, by decide⟩ else ⟨2, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem factorPair_injective :
    Function.Injective fun a =>
      (suffixParityQuotient.toFun a, finalMarkerQuotient.toFun a) := by
  intro a b
  revert a b
  decide

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_575.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_575.table (by decide)

theorem valid_suffixParity (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_575.table.semigroup) :
    e.SatisfiedBy Generated.Catalogue.S4_93.table.semigroup :=
  suffixParityQuotient.pushforwardIdentity e valid

theorem valid_finalMarker (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_575.table.semigroup) :
    e.SatisfiedBy Generated.Catalogue.S3_6.table.semigroup :=
  finalMarkerQuotient.pushforwardIdentity e valid

theorem valid_iff_factors (e : Identity Nat) :
    e.SatisfiedBy Generated.Catalogue.S5_575.table.semigroup ↔
      e.SatisfiedBy Generated.Catalogue.S4_93.table.semigroup ∧
        e.SatisfiedBy Generated.Catalogue.S3_6.table.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_suffixParity e valid, valid_finalMarker e valid⟩
  · rintro ⟨suffixValid, finalValid⟩
    exact satisfiedBy_of_joint_homs
      suffixParityQuotient.toHom finalMarkerQuotient.toHom
      factorPair_injective e suffixValid finalValid

end S5_575

end SemigroupBasis.CoRoots.S5_437Factors
