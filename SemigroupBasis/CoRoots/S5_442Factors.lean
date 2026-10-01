import SemigroupBasis.Generated.CatalogueOrder2
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.Generated.CatalogueOrder5Part04
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_442Factors

open SemigroupBasis

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

namespace S5_442

/-- The quotient `[1,2,1,3,4]` from `S5_442` onto `S4_70`. -/
def s4_70Quotient :
    SplitSurjection Generated.Catalogue.S5_442.table.semigroup
      Generated.Catalogue.S4_70.table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨1, by decide⟩ else
        if value.val = 2 then ⟨0, by decide⟩ else
          if value.val = 3 then ⟨2, by decide⟩ else
            ⟨3, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨1, by decide⟩ else
        if value.val = 2 then ⟨3, by decide⟩ else
          ⟨4, by decide⟩
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

/-- The quotient `[1,1,2,1,1]` from `S5_442` onto `S2_2`. -/
def s2_2Quotient :
    SplitSurjection Generated.Catalogue.S5_442.table.semigroup
      Generated.Catalogue.S2_2.table.semigroup where
  toFun := fun value =>
    if value.val = 2 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else ⟨2, by decide⟩
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

def s4_70QuotientOneBased : List Nat :=
  [(s4_70Quotient.toFun (0 : Fin 5)).val + 1,
    (s4_70Quotient.toFun (1 : Fin 5)).val + 1,
    (s4_70Quotient.toFun (2 : Fin 5)).val + 1,
    (s4_70Quotient.toFun (3 : Fin 5)).val + 1,
    (s4_70Quotient.toFun (4 : Fin 5)).val + 1]

def s2_2QuotientOneBased : List Nat :=
  [(s2_2Quotient.toFun (0 : Fin 5)).val + 1,
    (s2_2Quotient.toFun (1 : Fin 5)).val + 1,
    (s2_2Quotient.toFun (2 : Fin 5)).val + 1,
    (s2_2Quotient.toFun (3 : Fin 5)).val + 1,
    (s2_2Quotient.toFun (4 : Fin 5)).val + 1]

theorem s4_70QuotientOneBased_certificate :
    s4_70QuotientOneBased = [1, 2, 1, 3, 4] := by
  decide

theorem s2_2QuotientOneBased_certificate :
    s2_2QuotientOneBased = [1, 1, 2, 1, 1] := by
  decide

theorem factorPair_injective :
    Function.Injective fun value =>
      (s4_70Quotient.toFun value, s2_2Quotient.toFun value) := by
  intro left right
  revert left right
  decide

theorem valid_s4_70 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_442.table.semigroup) :
    identity.SatisfiedBy
      Generated.Catalogue.S4_70.table.semigroup :=
  s4_70Quotient.pushforwardIdentity identity valid

theorem valid_s2_2 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_442.table.semigroup) :
    identity.SatisfiedBy
      Generated.Catalogue.S2_2.table.semigroup :=
  s2_2Quotient.pushforwardIdentity identity valid

theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy
        Generated.Catalogue.S5_442.table.semigroup ↔
      identity.SatisfiedBy
          Generated.Catalogue.S4_70.table.semigroup ∧
        identity.SatisfiedBy
          Generated.Catalogue.S2_2.table.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_s4_70 identity valid, valid_s2_2 identity valid⟩
  · rintro ⟨componentValid, parityValid⟩
    exact satisfiedBy_of_joint_homs
      s4_70Quotient.toHom s2_2Quotient.toHom
      factorPair_injective identity componentValid parityValid

end S5_442

namespace S5_613

/-- The quotient `[1,2,3,3,4]` from `S5_613` onto `S4_70`. -/
def s4_70Quotient :
    SplitSurjection Generated.Catalogue.S5_613.table.semigroup
      Generated.Catalogue.S4_70.table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨1, by decide⟩ else
        if value.val = 2 then ⟨2, by decide⟩ else
          if value.val = 3 then ⟨2, by decide⟩ else
            ⟨3, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨1, by decide⟩ else
        if value.val = 2 then ⟨2, by decide⟩ else
          ⟨4, by decide⟩
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

/-- The quotient `[3,3,1,2,3]` from `S5_613` onto `S3_11`. -/
def s3_11Quotient :
    SplitSurjection Generated.Catalogue.S5_613.table.semigroup
      Generated.Catalogue.S3_11.table.semigroup where
  toFun := fun value =>
    if value.val = 2 then ⟨0, by decide⟩ else
      if value.val = 3 then ⟨1, by decide⟩ else
        ⟨2, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := fun value =>
    if value.val = 0 then ⟨2, by decide⟩ else
      if value.val = 1 then ⟨3, by decide⟩ else
        ⟨0, by decide⟩
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

def s4_70QuotientOneBased : List Nat :=
  [(s4_70Quotient.toFun (0 : Fin 5)).val + 1,
    (s4_70Quotient.toFun (1 : Fin 5)).val + 1,
    (s4_70Quotient.toFun (2 : Fin 5)).val + 1,
    (s4_70Quotient.toFun (3 : Fin 5)).val + 1,
    (s4_70Quotient.toFun (4 : Fin 5)).val + 1]

def s3_11QuotientOneBased : List Nat :=
  [(s3_11Quotient.toFun (0 : Fin 5)).val + 1,
    (s3_11Quotient.toFun (1 : Fin 5)).val + 1,
    (s3_11Quotient.toFun (2 : Fin 5)).val + 1,
    (s3_11Quotient.toFun (3 : Fin 5)).val + 1,
    (s3_11Quotient.toFun (4 : Fin 5)).val + 1]

theorem s4_70QuotientOneBased_certificate :
    s4_70QuotientOneBased = [1, 2, 3, 3, 4] := by
  decide

theorem s3_11QuotientOneBased_certificate :
    s3_11QuotientOneBased = [3, 3, 1, 2, 3] := by
  decide

theorem factorPair_injective :
    Function.Injective fun value =>
      (s4_70Quotient.toFun value, s3_11Quotient.toFun value) := by
  intro left right
  revert left right
  decide

theorem valid_s4_70 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_613.table.semigroup) :
    identity.SatisfiedBy
      Generated.Catalogue.S4_70.table.semigroup :=
  s4_70Quotient.pushforwardIdentity identity valid

theorem valid_s3_11 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_613.table.semigroup) :
    identity.SatisfiedBy
      Generated.Catalogue.S3_11.table.semigroup :=
  s3_11Quotient.pushforwardIdentity identity valid

theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy
        Generated.Catalogue.S5_613.table.semigroup ↔
      identity.SatisfiedBy
          Generated.Catalogue.S4_70.table.semigroup ∧
        identity.SatisfiedBy
          Generated.Catalogue.S3_11.table.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_s4_70 identity valid, valid_s3_11 identity valid⟩
  · rintro ⟨componentValid, parityValid⟩
    exact satisfiedBy_of_joint_homs
      s4_70Quotient.toHom s3_11Quotient.toHom
      factorPair_injective identity componentValid parityValid

end S5_613

end SemigroupBasis.CoRoots.S5_442Factors
