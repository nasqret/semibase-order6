import SemigroupBasis.CoRoots.S5_791
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Generated.S3_16
import SemigroupBasis.Generated.S4_70
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_791Factors

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

namespace S5_791

/-- The recorded homomorphic copy `[1,2,3,5]` of `S4_70`. -/
def componentEmbedding :
    Embedding Generated.S4_70.table.semigroup
      Generated.Catalogue.S5_791.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨2, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The connected-component quotient `[1,2,3,1,4]`. -/
def componentQuotient :
    SplitSurjection Generated.Catalogue.S5_791.table.semigroup
      Generated.S4_70.table.semigroup where
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
  preimage := componentEmbedding.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

/-- The recorded homomorphic copy `[1,5,4]` of `S3_16`. -/
def initialEmbedding :
    Embedding Generated.S3_16.table.semigroup
      Generated.Catalogue.S5_791.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨4, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The first-occurrence quotient `[1,1,1,3,2]`. -/
def initialQuotient :
    SplitSurjection Generated.Catalogue.S5_791.table.semigroup
      Generated.S3_16.table.semigroup where
  toFun := fun a =>
    if a.val = 3 then ⟨2, by decide⟩ else
      if a.val = 4 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := initialEmbedding.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem factorPair_injective :
    Function.Injective fun a =>
      (componentQuotient.toFun a, initialQuotient.toFun a) := by
  intro a b
  revert a b
  decide

theorem valid_s4_70 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_791.table.semigroup) :
    identity.SatisfiedBy Generated.S4_70.table.semigroup :=
  componentQuotient.pushforwardIdentity identity valid

theorem valid_s3_16 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_791.table.semigroup) :
    identity.SatisfiedBy Generated.S3_16.table.semigroup :=
  initialQuotient.pushforwardIdentity identity valid

theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy
        Generated.Catalogue.S5_791.table.semigroup ↔
      identity.SatisfiedBy Generated.S4_70.table.semigroup ∧
        identity.SatisfiedBy Generated.S3_16.table.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_s4_70 identity valid, valid_s3_16 identity valid⟩
  · rintro ⟨componentValid, initialValid⟩
    exact satisfiedBy_of_joint_homs
      componentQuotient.toHom initialQuotient.toHom
      factorPair_injective identity componentValid initialValid

end S5_791

namespace S5_807

/-- The recorded homomorphic copy `[1,2,3,5]` of `S4_70`. -/
def componentEmbedding :
    Embedding Generated.S4_70.table.semigroup
      Generated.Catalogue.S5_807.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨2, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The connected-component quotient `[1,2,3,1,4]`. -/
def componentQuotient :
    SplitSurjection Generated.Catalogue.S5_807.table.semigroup
      Generated.S4_70.table.semigroup where
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
  preimage := componentEmbedding.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

/-- The recorded homomorphic copy `[1,3,4]` of `S3_16`. -/
def initialEmbedding :
    Embedding Generated.S3_16.table.semigroup
      Generated.Catalogue.S5_807.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨2, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The first-occurrence quotient `[1,1,2,3,1]`. -/
def initialQuotient :
    SplitSurjection Generated.Catalogue.S5_807.table.semigroup
      Generated.S3_16.table.semigroup where
  toFun := fun a =>
    if a.val = 2 then ⟨1, by decide⟩ else
      if a.val = 3 then ⟨2, by decide⟩ else ⟨0, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := initialEmbedding.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem factorPair_injective :
    Function.Injective fun a =>
      (componentQuotient.toFun a, initialQuotient.toFun a) := by
  intro a b
  revert a b
  decide

theorem valid_s4_70 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_807.table.semigroup) :
    identity.SatisfiedBy Generated.S4_70.table.semigroup :=
  componentQuotient.pushforwardIdentity identity valid

theorem valid_s3_16 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_807.table.semigroup) :
    identity.SatisfiedBy Generated.S3_16.table.semigroup :=
  initialQuotient.pushforwardIdentity identity valid

theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy
        Generated.Catalogue.S5_807.table.semigroup ↔
      identity.SatisfiedBy Generated.S4_70.table.semigroup ∧
        identity.SatisfiedBy Generated.S3_16.table.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_s4_70 identity valid, valid_s3_16 identity valid⟩
  · rintro ⟨componentValid, initialValid⟩
    exact satisfiedBy_of_joint_homs
      componentQuotient.toHom initialQuotient.toHom
      factorPair_injective identity componentValid initialValid

end S5_807

end SemigroupBasis.CoRoots.S5_791Factors
