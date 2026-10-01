import SemigroupBasis.CoRoots.S5_787
import SemigroupBasis.Generated.CatalogueOrder2
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_787Factors

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

namespace S5_787

/-- The recorded homomorphic copy `[1,2,3,5]` of `S4_69`. -/
def separatorEmbedding :
    Embedding Generated.Catalogue.S4_69.table.semigroup
      Generated.Catalogue.S5_787.table.semigroup where
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

/-- The separator quotient `[1,2,3,1,4]`. -/
def separatorQuotient :
    SplitSurjection Generated.Catalogue.S5_787.table.semigroup
      Generated.Catalogue.S4_69.table.semigroup where
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
  preimage := separatorEmbedding.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

/-- The recorded homomorphic copy `[1,4]` of the left-zero marker `S2_4`. -/
def markerEmbedding :
    Embedding Generated.Catalogue.S2_4.table.semigroup
      Generated.Catalogue.S5_787.table.semigroup where
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

/-- The first-variable marker quotient `[1,1,1,2,1]`. -/
def markerQuotient :
    SplitSurjection Generated.Catalogue.S5_787.table.semigroup
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
      (separatorQuotient.toFun a, markerQuotient.toFun a) := by
  intro a b
  revert a b
  decide

theorem valid_s4_69 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_787.table.semigroup) :
    identity.SatisfiedBy
      Generated.Catalogue.S4_69.table.semigroup :=
  separatorQuotient.pushforwardIdentity identity valid

theorem valid_s2_4 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_787.table.semigroup) :
    identity.SatisfiedBy
      Generated.Catalogue.S2_4.table.semigroup :=
  markerQuotient.pushforwardIdentity identity valid

theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy
        Generated.Catalogue.S5_787.table.semigroup ↔
      identity.SatisfiedBy
          Generated.Catalogue.S4_69.table.semigroup ∧
        identity.SatisfiedBy
          Generated.Catalogue.S2_4.table.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_s4_69 identity valid, valid_s2_4 identity valid⟩
  · rintro ⟨separatorValid, markerValid⟩
    exact satisfiedBy_of_joint_homs
      separatorQuotient.toHom markerQuotient.toHom
      factorPair_injective identity separatorValid markerValid

end S5_787

namespace S5_789

/-- The separator quotient `[1,2,3,1,4]`. Its displayed set-theoretic
section is not asserted to be a semigroup embedding. -/
def separatorQuotient :
    SplitSurjection Generated.Catalogue.S5_789.table.semigroup
      Generated.Catalogue.S4_69.table.semigroup where
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
  preimage := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨2, by decide⟩ else ⟨4, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

/-- The recorded homomorphic copy `[1,4]` of the left-zero marker `S2_4`. -/
def markerEmbedding :
    Embedding Generated.Catalogue.S2_4.table.semigroup
      Generated.Catalogue.S5_789.table.semigroup where
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

/-- The first-variable marker quotient `[1,1,1,2,2]`. -/
def markerQuotient :
    SplitSurjection Generated.Catalogue.S5_789.table.semigroup
      Generated.Catalogue.S2_4.table.semigroup where
  toFun := fun a =>
    if a.val = 3 then ⟨1, by decide⟩ else
      if a.val = 4 then ⟨1, by decide⟩ else ⟨0, by decide⟩
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
      (separatorQuotient.toFun a, markerQuotient.toFun a) := by
  intro a b
  revert a b
  decide

theorem valid_s4_69 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_789.table.semigroup) :
    identity.SatisfiedBy
      Generated.Catalogue.S4_69.table.semigroup :=
  separatorQuotient.pushforwardIdentity identity valid

theorem valid_s2_4 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_789.table.semigroup) :
    identity.SatisfiedBy
      Generated.Catalogue.S2_4.table.semigroup :=
  markerQuotient.pushforwardIdentity identity valid

theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy
        Generated.Catalogue.S5_789.table.semigroup ↔
      identity.SatisfiedBy
          Generated.Catalogue.S4_69.table.semigroup ∧
        identity.SatisfiedBy
          Generated.Catalogue.S2_4.table.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_s4_69 identity valid, valid_s2_4 identity valid⟩
  · rintro ⟨separatorValid, markerValid⟩
    exact satisfiedBy_of_joint_homs
      separatorQuotient.toHom markerQuotient.toHom
      factorPair_injective identity separatorValid markerValid

end S5_789

namespace S5_796

/-- The recorded homomorphic copy `[1,2,3,5]` of `S4_69`. -/
def separatorEmbedding :
    Embedding Generated.Catalogue.S4_69.table.semigroup
      Generated.Catalogue.S5_796.table.semigroup where
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

/-- The separator quotient `[1,2,3,3,4]`. -/
def separatorQuotient :
    SplitSurjection Generated.Catalogue.S5_796.table.semigroup
      Generated.Catalogue.S4_69.table.semigroup where
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
  preimage := separatorEmbedding.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

/-- The recorded homomorphic copy `[1,3,4]` of the left-normal marker
`S3_15`. -/
def markerEmbedding :
    Embedding Generated.Catalogue.S3_15.table.semigroup
      Generated.Catalogue.S5_796.table.semigroup where
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

/-- The marker quotient `[1,1,2,3,1]`. -/
def markerQuotient :
    SplitSurjection Generated.Catalogue.S5_796.table.semigroup
      Generated.Catalogue.S3_15.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨0, by decide⟩ else
        if a.val = 2 then ⟨1, by decide⟩ else
          if a.val = 3 then ⟨2, by decide⟩ else ⟨0, by decide⟩
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
      (separatorQuotient.toFun a, markerQuotient.toFun a) := by
  intro a b
  revert a b
  decide

theorem valid_s4_69 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_796.table.semigroup) :
    identity.SatisfiedBy
      Generated.Catalogue.S4_69.table.semigroup :=
  separatorQuotient.pushforwardIdentity identity valid

theorem valid_s3_15 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_796.table.semigroup) :
    identity.SatisfiedBy
      Generated.Catalogue.S3_15.table.semigroup :=
  markerQuotient.pushforwardIdentity identity valid

theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy
        Generated.Catalogue.S5_796.table.semigroup ↔
      identity.SatisfiedBy
          Generated.Catalogue.S4_69.table.semigroup ∧
        identity.SatisfiedBy
          Generated.Catalogue.S3_15.table.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_s4_69 identity valid, valid_s3_15 identity valid⟩
  · rintro ⟨separatorValid, markerValid⟩
    exact satisfiedBy_of_joint_homs
      separatorQuotient.toHom markerQuotient.toHom
      factorPair_injective identity separatorValid markerValid

end S5_796

end SemigroupBasis.CoRoots.S5_787Factors
