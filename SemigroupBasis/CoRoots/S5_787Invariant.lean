import SemigroupBasis.CoRoots.S5_441Invariant
import SemigroupBasis.CoRoots.S5_787Factors
import SemigroupBasis.Examples.LeftNormalBandFifteen
import SemigroupBasis.Examples.LeftZeroTwo
import SemigroupBasis.Generated.S3_15

namespace SemigroupBasis.CoRoots

open SemigroupBasis
open SemigroupBasis.Examples

namespace S5_787Invariant

/-- The semantic invariant of the `S5_787` family: support, all exact
unique-separator cuts with their side supports, and the first variable of
the whole word. -/
structure SameSeparatorFirstSignature
    (left right : Word Nat) : Prop where
  support : S5_441Invariant.SameSupport left right
  exactCuts : S5_441Invariant.SameExactCutSignature left right
  first : left.head = right.head

abbrev sameSignature (left right : Word Nat) : Prop :=
  SameSeparatorFirstSignature left right

namespace SameSeparatorFirstSignature

theorem refl (word : Word Nat) :
    SameSeparatorFirstSignature word word :=
  ⟨S5_441Invariant.SameSupport.refl word,
    S5_441Invariant.SameExactCutSignature.refl word, rfl⟩

theorem symm {left right : Word Nat}
    (same : SameSeparatorFirstSignature left right) :
    SameSeparatorFirstSignature right left :=
  ⟨S5_441Invariant.SameSupport.symm same.support,
    S5_441Invariant.SameExactCutSignature.symm same.exactCuts,
    same.first.symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameSeparatorFirstSignature left middle)
    (second : SameSeparatorFirstSignature middle right) :
    SameSeparatorFirstSignature left right :=
  ⟨S5_441Invariant.SameSupport.trans first.support second.support,
    S5_441Invariant.SameExactCutSignature.trans
      first.exactCuts second.exactCuts,
    first.first.trans second.first⟩

end SameSeparatorFirstSignature

private theorem catalogueS2_4_table_eq_leftZeroTwo :
    Generated.Catalogue.S2_4.table = leftZeroTwo := by
  unfold Generated.Catalogue.S2_4.table
    Generated.Catalogue.S2_4.mul leftZeroTwo
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

theorem leftZeroValid_head_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftZeroTwo.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  apply Decidable.byContradiction
  intro headsNe
  let valuation : Nat → Fin 2 :=
    fun z => if z = identity.lhs.head then 0 else 1
  have evaluated := valid valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm headsNe] at evaluated

theorem sameSignature_of_s4_69_s2_4_valid
    (identity : Identity Nat)
    (separatorValid :
      identity.SatisfiedBy
        Generated.Catalogue.S4_69.table.semigroup)
    (firstValid :
      identity.SatisfiedBy
        Generated.Catalogue.S2_4.table.semigroup) :
    SameSeparatorFirstSignature identity.lhs identity.rhs := by
  have markerValid :
      identity.SatisfiedBy leftZeroTwo.semigroup := by
    rw [← catalogueS2_4_table_eq_leftZeroTwo]
    exact firstValid
  exact
    ⟨S5_441Invariant.sameSupport_of_s4_69_valid
        identity separatorValid,
      S5_441Invariant.sameExactCutSignature_of_s4_69_valid
        identity separatorValid,
      leftZeroValid_head_eq identity markerValid⟩

theorem sameSignature_of_s4_69_s3_15_valid
    (identity : Identity Nat)
    (separatorValid :
      identity.SatisfiedBy
        Generated.Catalogue.S4_69.table.semigroup)
    (firstValid :
      identity.SatisfiedBy
        Generated.Catalogue.S3_15.table.semigroup) :
    SameSeparatorFirstSignature identity.lhs identity.rhs := by
  have markerValid :
      identity.SatisfiedBy leftNormalBandFifteen.semigroup := by
    rw [← Generated.S3_15.table_eq_canonical_catalogue,
      Generated.S3_15.table_eq_catalogue_model] at firstValid
    exact firstValid
  exact
    ⟨S5_441Invariant.sameSupport_of_s4_69_valid
        identity separatorValid,
      S5_441Invariant.sameExactCutSignature_of_s4_69_valid
        identity separatorValid,
      leftNormalBandFifteenValid_head_eq identity markerValid⟩

end S5_787Invariant

namespace S5_787

/-- Every derivation from the five-law basis preserves the intended
separator/first signature. -/
theorem derives_sameSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    S5_787Invariant.SameSeparatorFirstSignature left right := by
  have separatorModels :
      Models uniqueSeparatorFour.semigroup basis :=
    models_of_finite_checks uniqueSeparatorFour (by decide)
  have markerModels :
      Models leftZeroTwo.semigroup basis :=
    models_of_finite_checks leftZeroTwo (by decide)
  exact
    ⟨S5_441Invariant.sameSupport_of_uniqueSeparatorFour_equalEval
        left right
        (fun valuation => derivation.sound separatorModels valuation),
      S5_441Invariant.sameExactCutSignature_of_uniqueSeparatorFour_equalEval
        left right
        (fun valuation => derivation.sound separatorModels valuation),
      S5_787Invariant.leftZeroValid_head_eq
        (⟨left, right⟩ : Identity Nat)
        (fun valuation => derivation.sound markerModels valuation)⟩

end S5_787

namespace S5_787FamilyInvariant

namespace S5_787

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_787.table.semigroup) :
    S5_787Invariant.SameSeparatorFirstSignature
      identity.lhs identity.rhs :=
  S5_787Invariant.sameSignature_of_s4_69_s2_4_valid identity
    (S5_787Factors.S5_787.valid_s4_69 identity valid)
    (S5_787Factors.S5_787.valid_s2_4 identity valid)

end S5_787

namespace S5_789

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_789.table.semigroup) :
    S5_787Invariant.SameSeparatorFirstSignature
      identity.lhs identity.rhs :=
  S5_787Invariant.sameSignature_of_s4_69_s2_4_valid identity
    (S5_787Factors.S5_789.valid_s4_69 identity valid)
    (S5_787Factors.S5_789.valid_s2_4 identity valid)

end S5_789

namespace S5_796

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_796.table.semigroup) :
    S5_787Invariant.SameSeparatorFirstSignature
      identity.lhs identity.rhs :=
  S5_787Invariant.sameSignature_of_s4_69_s3_15_valid identity
    (S5_787Factors.S5_796.valid_s4_69 identity valid)
    (S5_787Factors.S5_796.valid_s3_15 identity valid)

end S5_796

end S5_787FamilyInvariant

end SemigroupBasis.CoRoots
