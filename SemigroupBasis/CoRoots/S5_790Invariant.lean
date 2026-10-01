import SemigroupBasis.CoRoots.S5_790Factors

namespace SemigroupBasis.CoRoots

open SemigroupBasis
open SemigroupBasis.Examples

namespace S5_790Invariant

/-- The exact semantic invariant of the family: the ordered `S4_70`
component signatures and the global first letter. -/
structure SameComponentFirstSignature
    (left right : Word Nat) : Prop where
  components :
    connectedComponentSignaturesWord left =
      connectedComponentSignaturesWord right
  first : left.head = right.head

abbrev sameSignature (left right : Word Nat) : Prop :=
  SameComponentFirstSignature left right

namespace SameComponentFirstSignature

theorem refl (word : Word Nat) :
    SameComponentFirstSignature word word :=
  ⟨rfl, rfl⟩

theorem symm {left right : Word Nat}
    (same : SameComponentFirstSignature left right) :
    SameComponentFirstSignature right left :=
  ⟨same.components.symm, same.first.symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameComponentFirstSignature left middle)
    (second : SameComponentFirstSignature middle right) :
    SameComponentFirstSignature left right :=
  ⟨first.components.trans second.components,
    first.first.trans second.first⟩

end SameComponentFirstSignature

/-- Equal term functions in `S4_70` have the same ordered component
signature. This packages the semantic injectivity theorem used in the root
completeness proof. -/
theorem sameComponents_of_s4_70_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.S4_70.table.semigroup) :
    connectedComponentSignaturesWord identity.lhs =
      connectedComponentSignaturesWord identity.rhs := by
  have rootValid :
      identity.SatisfiedBy connectedComponentFour.semigroup := by
    simpa [Generated.S4_70.table] using valid
  have lhsDerivation :=
    connectedComponentFour_derivesCanonical identity.lhs
  have rhsDerivation :=
    connectedComponentFour_derivesCanonical identity.rhs
  have normalizedEval :
      ∀ valuation : Nat → Fin 4,
        connectedComponentFour.semigroup.eval valuation
            (connectedComponentCanonicalRender identity.lhs) =
          connectedComponentFour.semigroup.eval valuation
            (connectedComponentCanonicalRender identity.rhs) := by
    intro valuation
    have lhsSound :=
      lhsDerivation.sound connectedComponentFourBasis_models valuation
    have rhsSound :=
      rhsDerivation.sound connectedComponentFourBasis_models valuation
    exact lhsSound.symm.trans <|
      (rootValid valuation).trans rhsSound
  exact
    connectedComponentCanonical_eq_of_equalEval
      (connectedComponentFourSignaturesWord_canonical identity.lhs)
      (connectedComponentFourSignaturesWord_canonical identity.rhs)
      (connectedComponentCanonicalRender identity.lhs)
      (connectedComponentCanonicalRender identity.rhs)
      (connectedComponentCanonicalRender_toList identity.lhs)
      (connectedComponentCanonicalRender_toList identity.rhs)
      normalizedEval

/-- The two-element left-zero marker detects the first letter. -/
theorem leftZeroValid_head_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftZeroTwo.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  apply Decidable.byContradiction
  intro headsNe
  let valuation : Nat → Fin 2 := fun letter =>
    if letter = identity.lhs.head then 0 else 1
  have evaluated := valid valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm headsNe] at evaluated

theorem sameSignature_of_s4_70_s2_4_valid
    (identity : Identity Nat)
    (componentValid :
      identity.SatisfiedBy Generated.S4_70.table.semigroup)
    (markerValid :
      identity.SatisfiedBy leftZeroTwo.semigroup) :
    SameComponentFirstSignature identity.lhs identity.rhs :=
  ⟨sameComponents_of_s4_70_valid identity componentValid,
    leftZeroValid_head_eq identity markerValid⟩

theorem sameSignature_of_s4_70_s3_15_valid
    (identity : Identity Nat)
    (componentValid :
      identity.SatisfiedBy Generated.S4_70.table.semigroup)
    (markerValid :
      identity.SatisfiedBy leftNormalBandFifteen.semigroup) :
    SameComponentFirstSignature identity.lhs identity.rhs :=
  ⟨sameComponents_of_s4_70_valid identity componentValid,
    leftNormalBandFifteenValid_head_eq identity markerValid⟩

end S5_790Invariant

namespace S5_790

/-- Every derivation from the six-law basis preserves the component/first
signature. -/
theorem derives_sameSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    S5_790Invariant.SameComponentFirstSignature left right := by
  have componentModels :
      Models Generated.S4_70.table.semigroup basis :=
    models_of_finite_checks Generated.S4_70.table (by decide)
  have markerModels :
      Models leftZeroTwo.semigroup basis :=
    models_of_finite_checks leftZeroTwo (by decide)
  let identity : Identity Nat := ⟨left, right⟩
  exact S5_790Invariant.sameSignature_of_s4_70_s2_4_valid
    identity
    (fun valuation => derivation.sound componentModels valuation)
    (fun valuation => derivation.sound markerModels valuation)

end S5_790

namespace S5_790FamilyInvariant

namespace S5_790

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_790.table.semigroup) :
    S5_790Invariant.SameComponentFirstSignature
      identity.lhs identity.rhs := by
  exact S5_790Invariant.sameSignature_of_s4_70_s2_4_valid identity
    (S5_790Factors.S5_790.valid_s4_70 identity valid)
    (S5_790Factors.S5_790.valid_s2_4 identity valid)

end S5_790

namespace S5_792

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_792.table.semigroup) :
    S5_790Invariant.SameComponentFirstSignature
      identity.lhs identity.rhs := by
  exact S5_790Invariant.sameSignature_of_s4_70_s2_4_valid identity
    (S5_790Factors.S5_792.valid_s4_70 identity valid)
    (S5_790Factors.S5_792.valid_s2_4 identity valid)

end S5_792

namespace S5_798

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_798.table.semigroup) :
    S5_790Invariant.SameComponentFirstSignature
      identity.lhs identity.rhs := by
  exact S5_790Invariant.sameSignature_of_s4_70_s3_15_valid identity
    (S5_790Factors.S5_798.valid_s4_70 identity valid)
    (S5_790Factors.S5_798.valid_s3_15 identity valid)

end S5_798

end S5_790FamilyInvariant

end SemigroupBasis.CoRoots
