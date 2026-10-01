import SemigroupBasis.CoRoots.S5_848Normalization
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_848

open SemigroupBasis
open SemigroupBasis.Examples

/-- The exact stored Smallsemi representative `S5_848`. -/
abbrev table : FiniteTable :=
  Generated.Catalogue.S5_848.table

theorem table_eq_canonical_catalogue :
    table = Generated.Catalogue.S5_848.table := rfl

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def finiteTailSquarePromotionLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2, 2]⟩, ⟨0, [2, 1, 1, 2]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = powerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val = gatherLaw := rfl

theorem finiteTailSquarePromotionLaw_map :
    finiteTailSquarePromotionLaw.map Fin.val =
      tailSquarePromotionLaw := rfl

/-- The exact catalogue table satisfies all three recorded identities. -/
theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact table.checkIdentityNat_sound finiteGatherLaw (by decide)
  · rw [← finiteTailSquarePromotionLaw_map]
    exact table.checkIdentityNat_sound
      finiteTailSquarePromotionLaw (by decide)

/-- The quotient `[1,2,1,3,4]` onto opposite `S4_71`. It records the
global first-occurrence square-block theory. -/
def blockQuotient :
    SplitSurjection table.semigroup
      Generated.S4_71.table.semigroup.opposite where
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

/-- The quotient `[1,1,3,2,2]` onto the three-element left normal band.
Only its first-letter separator is required by the normalization proof. -/
def headQuotient :
    SplitSurjection table.semigroup
      leftNormalBandThree.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨0, by decide⟩ else
        if value.val = 2 then ⟨2, by decide⟩ else
          ⟨1, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨3, by decide⟩ else
        ⟨2, by decide⟩
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

/-- The two quotient coordinates distinguish all five elements, so the
catalogue representative is a subdirect product of the two factors. -/
theorem factorPair_injective :
    Function.Injective fun value =>
      (blockQuotient.toFun value, headQuotient.toFun value) := by
  intro left right
  revert left right
  decide

private theorem satisfiedBy_of_factor_pair
    (identity : Identity Nat)
    (blockValid :
      identity.SatisfiedBy
        Generated.S4_71.table.semigroup.opposite)
    (headValid :
      identity.SatisfiedBy leftNormalBandThree.semigroup) :
    identity.SatisfiedBy table.semigroup := by
  intro valuation
  apply factorPair_injective
  apply Prod.ext
  · change
      blockQuotient.toFun
          (table.semigroup.eval valuation identity.lhs) =
        blockQuotient.toFun
          (table.semigroup.eval valuation identity.rhs)
    rw [blockQuotient.toHom.map_eval,
      blockQuotient.toHom.map_eval]
    exact blockValid
      (fun letter => blockQuotient.toFun (valuation letter))
  · change
      headQuotient.toFun
          (table.semigroup.eval valuation identity.lhs) =
        headQuotient.toFun
          (table.semigroup.eval valuation identity.rhs)
    rw [headQuotient.toHom.map_eval,
      headQuotient.toHom.map_eval]
    exact headValid
      (fun letter => headQuotient.toFun (valuation letter))

/-- Exact semantic decomposition of the catalogue table into the two
jointly faithful quotient factors. -/
theorem valid_iff_factor_pair (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      identity.SatisfiedBy
          Generated.S4_71.table.semigroup.opposite ∧
        identity.SatisfiedBy leftNormalBandThree.semigroup := by
  constructor
  · intro valid
    exact
      ⟨blockQuotient.pushforwardIdentity identity valid,
        headQuotient.pushforwardIdentity identity valid⟩
  · rintro ⟨blockValid, headValid⟩
    exact satisfiedBy_of_factor_pair identity blockValid headValid

/-- Every valid identity of `S5_848` has the exact tail-square signature. -/
theorem valid_sameSignature
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SameTailSquareSignature identity.lhs identity.rhs := by
  have blockValid :=
    blockQuotient.pushforwardIdentity identity valid
  have headValid :=
    headQuotient.pushforwardIdentity identity valid
  exact sameSignature_of_block_valid_head_eq identity blockValid
    (leftNormalBandValid_head_eq identity headValid)

/-- Every derivation from the exact basis preserves the complete signature. -/
theorem derives_sameSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameTailSquareSignature left right :=
  valid_sameSignature ⟨left, right⟩
    (fun valuation => derivation.sound models valuation)

/-- Unrestricted completeness for the stored representative. -/
theorem basis_complete :
    BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derives_of_sameTailSquareSignature
    (valid_sameSignature identity valid)

theorem representative_basis :
    BasisFor table.semigroup basis :=
  basis_complete

/-- Unrestricted completeness for the opposite semigroup, with the
literal reversed basis. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.S5_848
