import SemigroupBasis.Examples.HeadSortedPeriodTwoFromTwo
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder2
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.Generated.CatalogueOrder5Part04
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_445Factors

open SemigroupBasis
open SemigroupBasis.Examples

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def finiteBasis : List (Identity (Fin 3)) :=
  headSortedPeriodTwoFromTwoBasis.map fun identity =>
    identity.map toFinThree

private theorem basis_roundTrip_checked :
    headSortedPeriodTwoFromTwoBasis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat)
    (member : identity ∈ headSortedPeriodTwoFromTwoBasis) :
    (identity.map toFinThree).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

private theorem models_of_finite_checks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup headSortedPeriodTwoFromTwoBasis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

private theorem s2_4_models :
    Models Generated.Catalogue.S2_4.table.semigroup
      headSortedPeriodTwoFromTwoBasis :=
  models_of_finite_checks Generated.Catalogue.S2_4.table (by decide)

private theorem s3_15_models :
    Models Generated.Catalogue.S3_15.table.semigroup
      headSortedPeriodTwoFromTwoBasis :=
  models_of_finite_checks Generated.Catalogue.S3_15.table (by decide)

private theorem s4_28_models :
    Models Generated.Catalogue.S4_28.table.semigroup
      headSortedPeriodTwoFromTwoBasis :=
  models_of_finite_checks Generated.Catalogue.S4_28.table (by decide)

private theorem s4_48_models :
    Models Generated.Catalogue.S4_48.table.semigroup
      headSortedPeriodTwoFromTwoBasis :=
  models_of_finite_checks Generated.Catalogue.S4_48.table (by decide)

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

namespace S5_445

/-- The homomorphic section `[1,4,5]` of the `S3_15` quotient,
in one-based notation. -/
def s3_15Section :
    Embedding Generated.Catalogue.S3_15.table.semigroup
      Generated.Catalogue.S5_445.table.semigroup where
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

/-- The quotient `[1,1,1,2,3]` from `S5_445` onto `S3_15`,
in one-based notation. -/
def s3_15Quotient :
    SplitSurjection Generated.Catalogue.S5_445.table.semigroup
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
  preimage := s3_15Section.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem s3_15_section_right_inverse :
    Function.RightInverse s3_15Section.toFun s3_15Quotient.toFun :=
  s3_15Quotient.right_inverse

theorem s3_15_quotient_surjective :
    Function.Surjective s3_15Quotient.toFun := by
  intro b
  exact ⟨s3_15Section.toFun b, s3_15_section_right_inverse b⟩

/-- The homomorphic section `[1,2,3,4]` of the `S4_28` quotient,
in one-based notation. -/
def s4_28Section :
    Embedding Generated.Catalogue.S4_28.table.semigroup
      Generated.Catalogue.S5_445.table.semigroup where
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

/-- The quotient `[1,2,3,4,4]` from `S5_445` onto `S4_28`,
in one-based notation. -/
def s4_28Quotient :
    SplitSurjection Generated.Catalogue.S5_445.table.semigroup
      Generated.Catalogue.S4_28.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨2, by decide⟩ else
          if a.val = 3 then ⟨3, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := s4_28Section.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem s4_28_section_right_inverse :
    Function.RightInverse s4_28Section.toFun s4_28Quotient.toFun :=
  s4_28Quotient.right_inverse

theorem s4_28_quotient_surjective :
    Function.Surjective s4_28Quotient.toFun := by
  intro b
  exact ⟨s4_28Section.toFun b, s4_28_section_right_inverse b⟩

theorem factorPair_injective :
    Function.Injective fun a =>
      (s3_15Quotient.toFun a, s4_28Quotient.toFun a) := by
  intro a b
  revert a b
  decide

theorem valid_s3_15 (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_445.table.semigroup) :
    e.SatisfiedBy Generated.Catalogue.S3_15.table.semigroup :=
  s3_15Quotient.pushforwardIdentity e valid

theorem valid_s4_28 (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_445.table.semigroup) :
    e.SatisfiedBy Generated.Catalogue.S4_28.table.semigroup :=
  s4_28Quotient.pushforwardIdentity e valid

theorem valid_iff_factors (e : Identity Nat) :
    e.SatisfiedBy Generated.Catalogue.S5_445.table.semigroup ↔
      e.SatisfiedBy Generated.Catalogue.S3_15.table.semigroup ∧
        e.SatisfiedBy Generated.Catalogue.S4_28.table.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_s3_15 e valid, valid_s4_28 e valid⟩
  · rintro ⟨s3Valid, s4Valid⟩
    exact satisfiedBy_of_joint_homs
      s3_15Quotient.toHom s4_28Quotient.toHom
      factorPair_injective e s3Valid s4Valid

/-- The fixed-head, commutative-suffix basis models `S5_445`. -/
theorem models :
    Models Generated.Catalogue.S5_445.table.semigroup
      headSortedPeriodTwoFromTwoBasis := by
  intro identity member
  exact (valid_iff_factors identity).2
    ⟨s3_15_models identity member, s4_28_models identity member⟩

end S5_445

namespace S5_633

/-- The homomorphic section `[1,5]` of the `S2_4` quotient,
in one-based notation. -/
def s2_4Section :
    Embedding Generated.Catalogue.S2_4.table.semigroup
      Generated.Catalogue.S5_633.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The quotient `[1,1,1,1,2]` from `S5_633` onto `S2_4`,
in one-based notation. -/
def s2_4Quotient :
    SplitSurjection Generated.Catalogue.S5_633.table.semigroup
      Generated.Catalogue.S2_4.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨0, by decide⟩ else
        if a.val = 2 then ⟨0, by decide⟩ else
          if a.val = 3 then ⟨0, by decide⟩ else ⟨1, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := s2_4Section.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem s2_4_section_right_inverse :
    Function.RightInverse s2_4Section.toFun s2_4Quotient.toFun :=
  s2_4Quotient.right_inverse

theorem s2_4_quotient_surjective :
    Function.Surjective s2_4Quotient.toFun := by
  intro b
  exact ⟨s2_4Section.toFun b, s2_4_section_right_inverse b⟩

/-- The homomorphic section `[1,2,3,4]` of the `S4_48` quotient,
in one-based notation. -/
def s4_48Section :
    Embedding Generated.Catalogue.S4_48.table.semigroup
      Generated.Catalogue.S5_633.table.semigroup where
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

/-- The quotient `[1,2,3,4,1]` from `S5_633` onto `S4_48`,
in one-based notation. -/
def s4_48Quotient :
    SplitSurjection Generated.Catalogue.S5_633.table.semigroup
      Generated.Catalogue.S4_48.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨2, by decide⟩ else
          if a.val = 3 then ⟨3, by decide⟩ else ⟨0, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := s4_48Section.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem s4_48_section_right_inverse :
    Function.RightInverse s4_48Section.toFun s4_48Quotient.toFun :=
  s4_48Quotient.right_inverse

theorem s4_48_quotient_surjective :
    Function.Surjective s4_48Quotient.toFun := by
  intro b
  exact ⟨s4_48Section.toFun b, s4_48_section_right_inverse b⟩

theorem factorPair_injective :
    Function.Injective fun a =>
      (s2_4Quotient.toFun a, s4_48Quotient.toFun a) := by
  intro a b
  revert a b
  decide

theorem valid_s2_4 (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_633.table.semigroup) :
    e.SatisfiedBy Generated.Catalogue.S2_4.table.semigroup :=
  s2_4Quotient.pushforwardIdentity e valid

theorem valid_s4_48 (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_633.table.semigroup) :
    e.SatisfiedBy Generated.Catalogue.S4_48.table.semigroup :=
  s4_48Quotient.pushforwardIdentity e valid

theorem valid_iff_factors (e : Identity Nat) :
    e.SatisfiedBy Generated.Catalogue.S5_633.table.semigroup ↔
      e.SatisfiedBy Generated.Catalogue.S2_4.table.semigroup ∧
        e.SatisfiedBy Generated.Catalogue.S4_48.table.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_s2_4 e valid, valid_s4_48 e valid⟩
  · rintro ⟨s2Valid, s4Valid⟩
    exact satisfiedBy_of_joint_homs
      s2_4Quotient.toHom s4_48Quotient.toHom
      factorPair_injective e s2Valid s4Valid

/-- The fixed-head, commutative-suffix basis models `S5_633`. -/
theorem models :
    Models Generated.Catalogue.S5_633.table.semigroup
      headSortedPeriodTwoFromTwoBasis := by
  intro identity member
  exact (valid_iff_factors identity).2
    ⟨s2_4_models identity member, s4_48_models identity member⟩

end S5_633

end SemigroupBasis.CoRoots.S5_445Factors
