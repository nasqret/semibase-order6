import SemigroupBasis.CoRoots.S5_793
import SemigroupBasis.Generated.CatalogueOrder2
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Generated.S4_71
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_793Factors

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

namespace S5_793

/-- The embedded copy `[1,2,3,5]` of `S4_71`. -/
def blockEmbedding :
    Embedding Generated.S4_71.table.semigroup
      Generated.Catalogue.S5_793.table.semigroup where
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

/-- The `S4_71` quotient `[1,2,3,1,4]`. -/
def blockQuotient :
    SplitSurjection Generated.Catalogue.S5_793.table.semigroup
      Generated.S4_71.table.semigroup where
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
  preimage := blockEmbedding.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

/-- The embedded left-zero marker `[1,4]`. -/
def markerEmbedding :
    Embedding Generated.Catalogue.S2_4.table.semigroup
      Generated.Catalogue.S5_793.table.semigroup where
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

/-- The first-variable quotient `[1,1,1,2,1]`. -/
def markerQuotient :
    SplitSurjection Generated.Catalogue.S5_793.table.semigroup
      Generated.Catalogue.S2_4.table.semigroup where
  toFun := fun a =>
    if a.val = 3 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := markerEmbedding.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem factorPair_injective :
    Function.Injective fun a =>
      (blockQuotient.toFun a, markerQuotient.toFun a) := by
  intro a b
  revert a b
  decide

theorem valid_s4_71 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_793.table.semigroup) :
    identity.SatisfiedBy Generated.S4_71.table.semigroup :=
  blockQuotient.pushforwardIdentity identity valid

theorem valid_s2_4 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_793.table.semigroup) :
    identity.SatisfiedBy
      Generated.Catalogue.S2_4.table.semigroup :=
  markerQuotient.pushforwardIdentity identity valid

/-- Exact table separation: the term functions of `S5_793` are separated
jointly by the `S4_71` block quotient and the left-zero first marker. -/
theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy
        Generated.Catalogue.S5_793.table.semigroup ↔
      identity.SatisfiedBy Generated.S4_71.table.semigroup ∧
        identity.SatisfiedBy
          Generated.Catalogue.S2_4.table.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_s4_71 identity valid, valid_s2_4 identity valid⟩
  · rintro ⟨blockValid, markerValid⟩
    exact satisfiedBy_of_joint_homs
      blockQuotient.toHom markerQuotient.toHom
      factorPair_injective identity blockValid markerValid

end S5_793

namespace S5_801

/-- The embedded copy `[1,2,3,5]` of `S4_71`. -/
def blockEmbedding :
    Embedding Generated.S4_71.table.semigroup
      Generated.Catalogue.S5_801.table.semigroup where
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

/-- The `S4_71` quotient `[1,2,3,3,4]`. -/
def blockQuotient :
    SplitSurjection Generated.Catalogue.S5_801.table.semigroup
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
  preimage := blockEmbedding.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

/-- The embedded left-normal-band marker `[1,3,4]`. -/
def markerEmbedding :
    Embedding Generated.Catalogue.S3_15.table.semigroup
      Generated.Catalogue.S5_801.table.semigroup where
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

/-- The first-variable quotient `[1,1,2,3,2]`. -/
def markerQuotient :
    SplitSurjection Generated.Catalogue.S5_801.table.semigroup
      Generated.Catalogue.S3_15.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨0, by decide⟩ else
        if a.val = 2 then ⟨1, by decide⟩ else
          if a.val = 3 then ⟨2, by decide⟩ else ⟨1, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := markerEmbedding.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem factorPair_injective :
    Function.Injective fun a =>
      (blockQuotient.toFun a, markerQuotient.toFun a) := by
  intro a b
  revert a b
  decide

theorem valid_s4_71 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_801.table.semigroup) :
    identity.SatisfiedBy Generated.S4_71.table.semigroup :=
  blockQuotient.pushforwardIdentity identity valid

theorem valid_s3_15 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_801.table.semigroup) :
    identity.SatisfiedBy
      Generated.Catalogue.S3_15.table.semigroup :=
  markerQuotient.pushforwardIdentity identity valid

/-- Exact table separation for `S5_801`. -/
theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy
        Generated.Catalogue.S5_801.table.semigroup ↔
      identity.SatisfiedBy Generated.S4_71.table.semigroup ∧
        identity.SatisfiedBy
          Generated.Catalogue.S3_15.table.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_s4_71 identity valid, valid_s3_15 identity valid⟩
  · rintro ⟨blockValid, markerValid⟩
    exact satisfiedBy_of_joint_homs
      blockQuotient.toHom markerQuotient.toHom
      factorPair_injective identity blockValid markerValid

end S5_801

namespace S5_843

/-- The embedded copy `[1,2,3,4]` of `S4_71`. -/
def blockEmbedding :
    Embedding Generated.S4_71.table.semigroup
      Generated.Catalogue.S5_843.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨2, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The `S4_71` quotient `[1,2,3,4,4]`. -/
def blockQuotient :
    SplitSurjection Generated.Catalogue.S5_843.table.semigroup
      Generated.S4_71.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨2, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := blockEmbedding.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

/-- The embedded left-normal-band marker `[1,4,5]`. -/
def markerEmbedding :
    Embedding Generated.Catalogue.S3_15.table.semigroup
      Generated.Catalogue.S5_843.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨3, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The first-variable quotient `[1,1,1,2,3]`. -/
def markerQuotient :
    SplitSurjection Generated.Catalogue.S5_843.table.semigroup
      Generated.Catalogue.S3_15.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨0, by decide⟩ else
        if a.val = 2 then ⟨0, by decide⟩ else
          if a.val = 3 then ⟨1, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := markerEmbedding.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem factorPair_injective :
    Function.Injective fun a =>
      (blockQuotient.toFun a, markerQuotient.toFun a) := by
  intro a b
  revert a b
  decide

theorem valid_s4_71 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_843.table.semigroup) :
    identity.SatisfiedBy Generated.S4_71.table.semigroup :=
  blockQuotient.pushforwardIdentity identity valid

theorem valid_s3_15 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_843.table.semigroup) :
    identity.SatisfiedBy
      Generated.Catalogue.S3_15.table.semigroup :=
  markerQuotient.pushforwardIdentity identity valid

/-- Exact table separation for `S5_843`. -/
theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy
        Generated.Catalogue.S5_843.table.semigroup ↔
      identity.SatisfiedBy Generated.S4_71.table.semigroup ∧
        identity.SatisfiedBy
          Generated.Catalogue.S3_15.table.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_s4_71 identity valid, valid_s3_15 identity valid⟩
  · rintro ⟨blockValid, markerValid⟩
    exact satisfiedBy_of_joint_homs
      blockQuotient.toHom markerQuotient.toHom
      factorPair_injective identity blockValid markerValid

end S5_843

end SemigroupBasis.CoRoots.S5_793Factors
