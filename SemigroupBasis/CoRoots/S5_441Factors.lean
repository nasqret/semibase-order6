import SemigroupBasis.Generated.CatalogueOrder2
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.Generated.CatalogueOrder5Part04
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_441Factors

open SemigroupBasis

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

namespace S5_441

/-- The homomorphic section `[1,2,4,5]` of the `S4_69` quotient,
in one-based notation. -/
def s4_69Section :
    Embedding Generated.Catalogue.S4_69.table.semigroup
      Generated.Catalogue.S5_441.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨3, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The quotient `[1,2,1,3,4]` from `S5_441` onto `S4_69`,
in one-based notation. -/
def s4_69Quotient :
    SplitSurjection Generated.Catalogue.S5_441.table.semigroup
      Generated.Catalogue.S4_69.table.semigroup where
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
  preimage := s4_69Section.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem s4_69_section_right_inverse :
    Function.RightInverse s4_69Section.toFun s4_69Quotient.toFun :=
  s4_69Quotient.right_inverse

/-- The homomorphic section `[1,3]` of the `S2_2` quotient,
in one-based notation. -/
def s2_2Section :
    Embedding Generated.Catalogue.S2_2.table.semigroup
      Generated.Catalogue.S5_441.table.semigroup where
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

/-- The quotient `[1,1,2,1,1]` from `S5_441` onto `S2_2`,
in one-based notation. -/
def s2_2Quotient :
    SplitSurjection Generated.Catalogue.S5_441.table.semigroup
      Generated.Catalogue.S2_2.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨0, by decide⟩ else
        if a.val = 2 then ⟨1, by decide⟩ else
          if a.val = 3 then ⟨0, by decide⟩ else ⟨0, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := s2_2Section.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem s2_2_section_right_inverse :
    Function.RightInverse s2_2Section.toFun s2_2Quotient.toFun :=
  s2_2Quotient.right_inverse

theorem factorPair_injective :
    Function.Injective fun a =>
      (s4_69Quotient.toFun a, s2_2Quotient.toFun a) := by
  intro a b
  revert a b
  decide

theorem valid_s4_69 (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_441.table.semigroup) :
    e.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup :=
  s4_69Quotient.pushforwardIdentity e valid

theorem valid_s2_2 (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_441.table.semigroup) :
    e.SatisfiedBy Generated.Catalogue.S2_2.table.semigroup :=
  s2_2Quotient.pushforwardIdentity e valid

theorem valid_iff_factors (e : Identity Nat) :
    e.SatisfiedBy Generated.Catalogue.S5_441.table.semigroup ↔
      e.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup ∧
        e.SatisfiedBy Generated.Catalogue.S2_2.table.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_s4_69 e valid, valid_s2_2 e valid⟩
  · rintro ⟨s4Valid, s2Valid⟩
    exact satisfiedBy_of_joint_homs
      s4_69Quotient.toHom s2_2Quotient.toHom
      factorPair_injective e s4Valid s2Valid

end S5_441

namespace S5_464

/-- The quotient `[1,1,2,3,4]` from `S5_464` onto `S4_69`,
with the set-theoretic section `[1,3,4,5]`, in one-based notation.
This chosen section is not a semigroup homomorphism. -/
def s4_69Quotient :
    SplitSurjection Generated.Catalogue.S5_464.table.semigroup
      Generated.Catalogue.S4_69.table.semigroup where
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

/-- The homomorphic section `[1,2]` of the `S2_2` quotient,
in one-based notation. -/
def s2_2Section :
    Embedding Generated.Catalogue.S2_2.table.semigroup
      Generated.Catalogue.S5_464.table.semigroup where
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

/-- The quotient `[1,2,2,1,1]` from `S5_464` onto `S2_2`,
in one-based notation. -/
def s2_2Quotient :
    SplitSurjection Generated.Catalogue.S5_464.table.semigroup
      Generated.Catalogue.S2_2.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨1, by decide⟩ else
          if a.val = 3 then ⟨0, by decide⟩ else ⟨0, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := s2_2Section.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem s2_2_section_right_inverse :
    Function.RightInverse s2_2Section.toFun s2_2Quotient.toFun :=
  s2_2Quotient.right_inverse

theorem factorPair_injective :
    Function.Injective fun a =>
      (s4_69Quotient.toFun a, s2_2Quotient.toFun a) := by
  intro a b
  revert a b
  decide

theorem valid_s4_69 (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_464.table.semigroup) :
    e.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup :=
  s4_69Quotient.pushforwardIdentity e valid

theorem valid_s2_2 (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_464.table.semigroup) :
    e.SatisfiedBy Generated.Catalogue.S2_2.table.semigroup :=
  s2_2Quotient.pushforwardIdentity e valid

theorem valid_iff_factors (e : Identity Nat) :
    e.SatisfiedBy Generated.Catalogue.S5_464.table.semigroup ↔
      e.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup ∧
        e.SatisfiedBy Generated.Catalogue.S2_2.table.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_s4_69 e valid, valid_s2_2 e valid⟩
  · rintro ⟨s4Valid, s2Valid⟩
    exact satisfiedBy_of_joint_homs
      s4_69Quotient.toHom s2_2Quotient.toHom
      factorPair_injective e s4Valid s2Valid

end S5_464

namespace S5_612

/-- The homomorphic section `[1,2,3,5]` of the `S4_69` quotient,
in one-based notation. -/
def s4_69Section :
    Embedding Generated.Catalogue.S4_69.table.semigroup
      Generated.Catalogue.S5_612.table.semigroup where
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

/-- The quotient `[1,2,3,3,4]` from `S5_612` onto `S4_69`,
in one-based notation. -/
def s4_69Quotient :
    SplitSurjection Generated.Catalogue.S5_612.table.semigroup
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
  preimage := s4_69Section.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem s4_69_section_right_inverse :
    Function.RightInverse s4_69Section.toFun s4_69Quotient.toFun :=
  s4_69Quotient.right_inverse

/-- The homomorphic section `[3,4,1]` of the `S3_11` quotient,
in one-based notation. -/
def s3_11Section :
    Embedding Generated.Catalogue.S3_11.table.semigroup
      Generated.Catalogue.S5_612.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨2, by decide⟩ else
      if a.val = 1 then ⟨3, by decide⟩ else ⟨0, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The quotient `[3,3,1,2,3]` from `S5_612` onto `S3_11`,
in one-based notation. -/
def s3_11Quotient :
    SplitSurjection Generated.Catalogue.S5_612.table.semigroup
      Generated.Catalogue.S3_11.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨2, by decide⟩ else
      if a.val = 1 then ⟨2, by decide⟩ else
        if a.val = 2 then ⟨0, by decide⟩ else
          if a.val = 3 then ⟨1, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := s3_11Section.toFun
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

theorem s3_11_section_right_inverse :
    Function.RightInverse s3_11Section.toFun s3_11Quotient.toFun :=
  s3_11Quotient.right_inverse

theorem factorPair_injective :
    Function.Injective fun a =>
      (s4_69Quotient.toFun a, s3_11Quotient.toFun a) := by
  intro a b
  revert a b
  decide

theorem valid_s4_69 (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_612.table.semigroup) :
    e.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup :=
  s4_69Quotient.pushforwardIdentity e valid

theorem valid_s3_11 (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_612.table.semigroup) :
    e.SatisfiedBy Generated.Catalogue.S3_11.table.semigroup :=
  s3_11Quotient.pushforwardIdentity e valid

theorem valid_iff_factors (e : Identity Nat) :
    e.SatisfiedBy Generated.Catalogue.S5_612.table.semigroup ↔
      e.SatisfiedBy Generated.Catalogue.S4_69.table.semigroup ∧
        e.SatisfiedBy Generated.Catalogue.S3_11.table.semigroup := by
  constructor
  · intro valid
    exact ⟨valid_s4_69 e valid, valid_s3_11 e valid⟩
  · rintro ⟨s4Valid, s3Valid⟩
    exact satisfiedBy_of_joint_homs
      s4_69Quotient.toHom s3_11Quotient.toHom
      factorPair_injective e s4Valid s3Valid

end S5_612

end SemigroupBasis.CoRoots.S5_441Factors
