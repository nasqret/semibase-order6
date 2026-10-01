import SemigroupBasis.CoRoots.S5_441
import SemigroupBasis.CoRoots.S5_441Factors
import SemigroupBasis.Examples.UniqueSeparatorFourInvariant
import SemigroupBasis.Generated.S2_2
import SemigroupBasis.Generated.S3_11
import SemigroupBasis.Generated.S4_69

namespace SemigroupBasis.CoRoots

open SemigroupBasis

namespace S5_441Invariant

open SemigroupBasis.Examples

private theorem equalEval_of_table_eq
    {source target : FiniteTable}
    (tableEq : source = target)
    (left right : Word Nat)
    (equalEval :
      ∀ valuation : Nat → Fin source.order,
        source.semigroup.eval valuation left =
          source.semigroup.eval valuation right) :
    ∀ valuation : Nat → Fin target.order,
      target.semigroup.eval valuation left =
        target.semigroup.eval valuation right := by
  cases tableEq
  exact equalEval

/-- Two words have the same support when every variable occurs in one
exactly when it occurs in the other. -/
def SameSupport (left right : Word Nat) : Prop :=
  ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList

/-- The exact-cut signature at one separator and two prescribed side
supports. The support lists are compared extensionally, so their order and
multiplicity are irrelevant. -/
def ExactCutSignature
    (word : Word Nat) (separator : Nat)
    (leftSupport rightSupport : List Nat) : Prop :=
  ∃ left right,
    UniqueSeparatorFourExactCut
        word.toList left separator right ∧
      (∀ letter, letter ∈ left ↔ letter ∈ leftSupport) ∧
      (∀ letter, letter ∈ right ↔ letter ∈ rightSupport)

/-- Two words have the same exact unique-separator cuts, including the
support on each side of every cut. -/
def SameExactCutSignature (left right : Word Nat) : Prop :=
  ∀ separator leftSupport rightSupport,
    ExactCutSignature left separator leftSupport rightSupport ↔
      ExactCutSignature right separator leftSupport rightSupport

/-- Two words have the same occurrence-count parity for every variable. -/
def SameOccurrenceParity (left right : Word Nat) : Prop :=
  ∀ letter,
    left.toList.count letter % 2 =
      right.toList.count letter % 2

/-- The semantic invariant used by the `S5_441` family: support, every exact
unique-separator cut with its two side supports, and pointwise occurrence
parity. -/
structure SameParitySeparatorSignature
    (left right : Word Nat) : Prop where
  support : SameSupport left right
  exactCuts : SameExactCutSignature left right
  parity : SameOccurrenceParity left right

/-- Compatibility name for downstream normalization modules. -/
abbrev ParitySeparatorSignature
    (left right : Word Nat) : Prop :=
  SameParitySeparatorSignature left right

/-- Short compatibility name for the full semantic relation. -/
abbrev sameSignature
    (left right : Word Nat) : Prop :=
  SameParitySeparatorSignature left right

namespace SameSupport

theorem refl (word : Word Nat) :
    SameSupport word word :=
  fun _ => Iff.rfl

theorem symm {left right : Word Nat}
    (same : SameSupport left right) :
    SameSupport right left :=
  fun letter => (same letter).symm

theorem trans {left middle right : Word Nat}
    (first : SameSupport left middle)
    (second : SameSupport middle right) :
    SameSupport left right :=
  fun letter => (first letter).trans (second letter)

end SameSupport

namespace SameExactCutSignature

theorem refl (word : Word Nat) :
    SameExactCutSignature word word :=
  fun _ _ _ => Iff.rfl

theorem symm {left right : Word Nat}
    (same : SameExactCutSignature left right) :
    SameExactCutSignature right left :=
  fun separator leftSupport rightSupport =>
    (same separator leftSupport rightSupport).symm

theorem trans {left middle right : Word Nat}
    (first : SameExactCutSignature left middle)
    (second : SameExactCutSignature middle right) :
    SameExactCutSignature left right :=
  fun separator leftSupport rightSupport =>
    (first separator leftSupport rightSupport).trans
      (second separator leftSupport rightSupport)

/-- Transport a concrete exact cut to the other word while preserving both
side supports. -/
theorem transport {source target : Word Nat}
    (same : SameExactCutSignature source target)
    {left right : List Nat} {separator : Nat}
    (cut :
      UniqueSeparatorFourExactCut
        source.toList left separator right) :
    ∃ targetLeft targetRight,
      UniqueSeparatorFourExactCut
          target.toList targetLeft separator targetRight ∧
        (∀ letter, letter ∈ targetLeft ↔ letter ∈ left) ∧
        (∀ letter, letter ∈ targetRight ↔ letter ∈ right) := by
  have sourceSignature :
      ExactCutSignature source separator left right :=
    ⟨left, right, cut, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  simpa only [ExactCutSignature] using
    (same separator left right).mp sourceSignature

end SameExactCutSignature

namespace SameOccurrenceParity

theorem refl (word : Word Nat) :
    SameOccurrenceParity word word :=
  fun _ => rfl

theorem symm {left right : Word Nat}
    (same : SameOccurrenceParity left right) :
    SameOccurrenceParity right left :=
  fun letter => (same letter).symm

theorem trans {left middle right : Word Nat}
    (first : SameOccurrenceParity left middle)
    (second : SameOccurrenceParity middle right) :
    SameOccurrenceParity left right :=
  fun letter => (first letter).trans (second letter)

end SameOccurrenceParity

namespace SameParitySeparatorSignature

theorem refl (word : Word Nat) :
    SameParitySeparatorSignature word word :=
  ⟨SameSupport.refl word,
    SameExactCutSignature.refl word,
    SameOccurrenceParity.refl word⟩

theorem symm {left right : Word Nat}
    (same : SameParitySeparatorSignature left right) :
    SameParitySeparatorSignature right left :=
  ⟨SameSupport.symm same.support,
    SameExactCutSignature.symm same.exactCuts,
    SameOccurrenceParity.symm same.parity⟩

theorem trans {left middle right : Word Nat}
    (first : SameParitySeparatorSignature left middle)
    (second : SameParitySeparatorSignature middle right) :
    SameParitySeparatorSignature left right :=
  ⟨SameSupport.trans first.support second.support,
    SameExactCutSignature.trans first.exactCuts second.exactCuts,
    SameOccurrenceParity.trans first.parity second.parity⟩

end SameParitySeparatorSignature

/-- Equal term functions in the example presentation of `S4_69` preserve
support. -/
theorem sameSupport_of_uniqueSeparatorFour_equalEval
    (left right : Word Nat)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        uniqueSeparatorFour.semigroup.eval valuation left =
          uniqueSeparatorFour.semigroup.eval valuation right) :
    SameSupport left right :=
  fun letter =>
    uniqueSeparatorFourEqualEval_support_iff
      left right equalEval letter

/-- Equal term functions in the example presentation of `S4_69` preserve
every exact-cut signature. -/
theorem sameExactCutSignature_of_uniqueSeparatorFour_equalEval
    (left right : Word Nat)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        uniqueSeparatorFour.semigroup.eval valuation left =
          uniqueSeparatorFour.semigroup.eval valuation right) :
    SameExactCutSignature left right := by
  intro separator leftSupport rightSupport
  simpa only [ExactCutSignature] using
    uniqueSeparatorFourEqualEval_exactCut_iff
      left right equalEval separator leftSupport rightSupport

theorem sameSupport_of_uniqueSeparatorFour_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy uniqueSeparatorFour.semigroup) :
    SameSupport identity.lhs identity.rhs :=
  sameSupport_of_uniqueSeparatorFour_equalEval
    identity.lhs identity.rhs valid

theorem sameExactCutSignature_of_uniqueSeparatorFour_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy uniqueSeparatorFour.semigroup) :
    SameExactCutSignature identity.lhs identity.rhs :=
  sameExactCutSignature_of_uniqueSeparatorFour_equalEval
    identity.lhs identity.rhs valid

/-- Equal term functions in the example presentation of `S2_2` preserve
pointwise occurrence parity. -/
theorem sameOccurrenceParity_of_cyclicTwo_equalEval
    (left right : Word Nat)
    (equalEval :
      ∀ valuation : Nat → Fin 2,
        cyclicTwo.semigroup.eval valuation left =
          cyclicTwo.semigroup.eval valuation right) :
    SameOccurrenceParity left right := by
  intro letter
  exact
    cyclicValid_parity_eq
      (⟨left, right⟩ : Identity Nat) equalEval letter

theorem sameOccurrenceParity_of_cyclicTwo_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy cyclicTwo.semigroup) :
    SameOccurrenceParity identity.lhs identity.rhs :=
  sameOccurrenceParity_of_cyclicTwo_equalEval
    identity.lhs identity.rhs valid

/-- Equal term functions in the example presentation of `S3_11` preserve
pointwise occurrence parity. -/
theorem sameOccurrenceParity_of_parityZeroThree_equalEval
    (left right : Word Nat)
    (equalEval :
      ∀ valuation : Nat → Fin 3,
        parityZeroThree.semigroup.eval valuation left =
          parityZeroThree.semigroup.eval valuation right) :
    SameOccurrenceParity left right := by
  intro letter
  exact
    parityZeroValid_parity
      (⟨left, right⟩ : Identity Nat) equalEval letter

theorem sameOccurrenceParity_of_parityZeroThree_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy parityZeroThree.semigroup) :
    SameOccurrenceParity identity.lhs identity.rhs :=
  sameOccurrenceParity_of_parityZeroThree_equalEval
    identity.lhs identity.rhs valid

/-- The raw catalogue table used by the factor maps is the semantic
`S4_69` example table. -/
theorem catalogueS4_69_table_eq_uniqueSeparatorFour :
    Generated.Catalogue.S4_69.table = uniqueSeparatorFour := by
  rw [← Generated.S4_69.table_eq_canonical_catalogue]
  exact Generated.S4_69.table_eq_catalogue_model

/-- The generated `S2_2` bridge identifies the raw catalogue table with the
cyclic group example. -/
theorem catalogueS2_2_table_eq_cyclicTwo :
    Generated.Catalogue.S2_2.table = cyclicTwo := by
  rw [← Generated.S2_2.table_eq_catalogue_model]
  unfold Generated.Catalogue.S2_2.table
    Generated.Catalogue.S2_2.mul Generated.S2_2.table cyclicTwoMul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

/-- The raw catalogue table used by the factor maps is the semantic
`S3_11` example table. -/
theorem catalogueS3_11_table_eq_parityZeroThree :
    Generated.Catalogue.S3_11.table = parityZeroThree := by
  rw [← Generated.S3_11.table_eq_canonical_catalogue]
  exact Generated.S3_11.table_eq_catalogue_model

theorem sameSupport_of_s4_69_equalEval
    (left right : Word Nat)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        Generated.Catalogue.S4_69.table.semigroup.eval
            valuation left =
          Generated.Catalogue.S4_69.table.semigroup.eval
            valuation right) :
    SameSupport left right := by
  have semanticEqual :
      ∀ valuation : Nat → Fin 4,
        uniqueSeparatorFour.semigroup.eval valuation left =
          uniqueSeparatorFour.semigroup.eval valuation right := by
    exact
      equalEval_of_table_eq
        catalogueS4_69_table_eq_uniqueSeparatorFour
        left right equalEval
  exact
    sameSupport_of_uniqueSeparatorFour_equalEval
      left right semanticEqual

theorem sameExactCutSignature_of_s4_69_equalEval
    (left right : Word Nat)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        Generated.Catalogue.S4_69.table.semigroup.eval
            valuation left =
          Generated.Catalogue.S4_69.table.semigroup.eval
            valuation right) :
    SameExactCutSignature left right := by
  have semanticEqual :
      ∀ valuation : Nat → Fin 4,
        uniqueSeparatorFour.semigroup.eval valuation left =
          uniqueSeparatorFour.semigroup.eval valuation right := by
    exact
      equalEval_of_table_eq
        catalogueS4_69_table_eq_uniqueSeparatorFour
        left right equalEval
  exact
    sameExactCutSignature_of_uniqueSeparatorFour_equalEval
      left right semanticEqual

theorem sameSupport_of_s4_69_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S4_69.table.semigroup) :
    SameSupport identity.lhs identity.rhs :=
  sameSupport_of_s4_69_equalEval
    identity.lhs identity.rhs valid

theorem sameExactCutSignature_of_s4_69_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S4_69.table.semigroup) :
    SameExactCutSignature identity.lhs identity.rhs :=
  sameExactCutSignature_of_s4_69_equalEval
    identity.lhs identity.rhs valid

theorem sameOccurrenceParity_of_s2_2_equalEval
    (left right : Word Nat)
    (equalEval :
      ∀ valuation : Nat → Fin 2,
        Generated.Catalogue.S2_2.table.semigroup.eval
            valuation left =
          Generated.Catalogue.S2_2.table.semigroup.eval
            valuation right) :
    SameOccurrenceParity left right := by
  have semanticEqual :
      ∀ valuation : Nat → Fin 2,
        cyclicTwo.semigroup.eval valuation left =
          cyclicTwo.semigroup.eval valuation right := by
    exact
      equalEval_of_table_eq
        catalogueS2_2_table_eq_cyclicTwo left right equalEval
  exact
    sameOccurrenceParity_of_cyclicTwo_equalEval
      left right semanticEqual

theorem sameOccurrenceParity_of_s2_2_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S2_2.table.semigroup) :
    SameOccurrenceParity identity.lhs identity.rhs :=
  sameOccurrenceParity_of_s2_2_equalEval
    identity.lhs identity.rhs valid

theorem sameOccurrenceParity_of_s3_11_equalEval
    (left right : Word Nat)
    (equalEval :
      ∀ valuation : Nat → Fin 3,
        Generated.Catalogue.S3_11.table.semigroup.eval
            valuation left =
          Generated.Catalogue.S3_11.table.semigroup.eval
            valuation right) :
    SameOccurrenceParity left right := by
  have semanticEqual :
      ∀ valuation : Nat → Fin 3,
        parityZeroThree.semigroup.eval valuation left =
          parityZeroThree.semigroup.eval valuation right := by
    exact
      equalEval_of_table_eq
        catalogueS3_11_table_eq_parityZeroThree
        left right equalEval
  exact
    sameOccurrenceParity_of_parityZeroThree_equalEval
      left right semanticEqual

theorem sameOccurrenceParity_of_s3_11_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S3_11.table.semigroup) :
    SameOccurrenceParity identity.lhs identity.rhs :=
  sameOccurrenceParity_of_s3_11_equalEval
    identity.lhs identity.rhs valid

/-- Equality in the `S4_69` and `S2_2` factors determines the complete
parity-separator signature. -/
theorem sameSignature_of_s4_69_s2_2_equalEval
    (left right : Word Nat)
    (separatorEqual :
      ∀ valuation : Nat → Fin 4,
        Generated.Catalogue.S4_69.table.semigroup.eval
            valuation left =
          Generated.Catalogue.S4_69.table.semigroup.eval
            valuation right)
    (parityEqual :
      ∀ valuation : Nat → Fin 2,
        Generated.Catalogue.S2_2.table.semigroup.eval
            valuation left =
          Generated.Catalogue.S2_2.table.semigroup.eval
            valuation right) :
    SameParitySeparatorSignature left right :=
  ⟨sameSupport_of_s4_69_equalEval left right separatorEqual,
    sameExactCutSignature_of_s4_69_equalEval
      left right separatorEqual,
    sameOccurrenceParity_of_s2_2_equalEval
      left right parityEqual⟩

/-- Equality in the `S4_69` and `S3_11` factors determines the complete
parity-separator signature. -/
theorem sameSignature_of_s4_69_s3_11_equalEval
    (left right : Word Nat)
    (separatorEqual :
      ∀ valuation : Nat → Fin 4,
        Generated.Catalogue.S4_69.table.semigroup.eval
            valuation left =
          Generated.Catalogue.S4_69.table.semigroup.eval
            valuation right)
    (parityEqual :
      ∀ valuation : Nat → Fin 3,
        Generated.Catalogue.S3_11.table.semigroup.eval
            valuation left =
          Generated.Catalogue.S3_11.table.semigroup.eval
            valuation right) :
    SameParitySeparatorSignature left right :=
  ⟨sameSupport_of_s4_69_equalEval left right separatorEqual,
    sameExactCutSignature_of_s4_69_equalEval
      left right separatorEqual,
    sameOccurrenceParity_of_s3_11_equalEval
      left right parityEqual⟩

theorem valid_sameSignature_of_s2_2
    (identity : Identity Nat)
    (separatorValid :
      identity.SatisfiedBy
        Generated.Catalogue.S4_69.table.semigroup)
    (parityValid :
      identity.SatisfiedBy
        Generated.Catalogue.S2_2.table.semigroup) :
    SameParitySeparatorSignature identity.lhs identity.rhs :=
  sameSignature_of_s4_69_s2_2_equalEval
    identity.lhs identity.rhs separatorValid parityValid

theorem valid_sameSignature_of_s3_11
    (identity : Identity Nat)
    (separatorValid :
      identity.SatisfiedBy
        Generated.Catalogue.S4_69.table.semigroup)
    (parityValid :
      identity.SatisfiedBy
        Generated.Catalogue.S3_11.table.semigroup) :
    SameParitySeparatorSignature identity.lhs identity.rhs :=
  sameSignature_of_s4_69_s3_11_equalEval
    identity.lhs identity.rhs separatorValid parityValid

/-- Equality in the two semantic example factors is the same combined
invariant used by the raw catalogue factor theorems. -/
theorem sameSignature_of_uniqueSeparatorFour_cyclicTwo_equalEval
    (left right : Word Nat)
    (separatorEqual :
      ∀ valuation : Nat → Fin 4,
        uniqueSeparatorFour.semigroup.eval valuation left =
          uniqueSeparatorFour.semigroup.eval valuation right)
    (parityEqual :
      ∀ valuation : Nat → Fin 2,
        cyclicTwo.semigroup.eval valuation left =
          cyclicTwo.semigroup.eval valuation right) :
    SameParitySeparatorSignature left right :=
  ⟨sameSupport_of_uniqueSeparatorFour_equalEval
      left right separatorEqual,
    sameExactCutSignature_of_uniqueSeparatorFour_equalEval
      left right separatorEqual,
    sameOccurrenceParity_of_cyclicTwo_equalEval
      left right parityEqual⟩

end S5_441Invariant

namespace S5_441

/-- Every derivation from the common 25-law basis preserves the full
parity-separator signature. -/
theorem derives_sameParitySeparatorSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    S5_441Invariant.SameParitySeparatorSignature left right :=
  S5_441Invariant.sameSignature_of_uniqueSeparatorFour_cyclicTwo_equalEval
    left right
    (fun valuation =>
      derivation.sound basis_models_uniqueSeparatorFour valuation)
    (fun valuation =>
      derivation.sound basis_models_cyclicTwo valuation)

theorem derives_sameSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    S5_441Invariant.sameSignature left right :=
  derives_sameParitySeparatorSignature derivation

/-- Every identity valid in the raw catalogue representative `S5_441`
preserves the full parity-separator signature. -/
theorem valid_sameParitySeparatorSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_441.table.semigroup) :
    S5_441Invariant.SameParitySeparatorSignature
      identity.lhs identity.rhs :=
  S5_441Invariant.valid_sameSignature_of_s2_2 identity
    (S5_441Factors.S5_441.valid_s4_69 identity valid)
    (S5_441Factors.S5_441.valid_s2_2 identity valid)

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_441.table.semigroup) :
    S5_441Invariant.sameSignature identity.lhs identity.rhs :=
  valid_sameParitySeparatorSignature identity valid

end S5_441

namespace S5_464

/-- Every identity valid in the raw catalogue representative `S5_464`
preserves the full parity-separator signature. -/
theorem valid_sameParitySeparatorSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_464.table.semigroup) :
    S5_441Invariant.SameParitySeparatorSignature
      identity.lhs identity.rhs :=
  S5_441Invariant.valid_sameSignature_of_s2_2 identity
    (S5_441Factors.S5_464.valid_s4_69 identity valid)
    (S5_441Factors.S5_464.valid_s2_2 identity valid)

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_464.table.semigroup) :
    S5_441Invariant.sameSignature identity.lhs identity.rhs :=
  valid_sameParitySeparatorSignature identity valid

end S5_464

namespace S5_612

/-- Every identity valid in the raw catalogue representative `S5_612`
preserves the full parity-separator signature. -/
theorem valid_sameParitySeparatorSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_612.table.semigroup) :
    S5_441Invariant.SameParitySeparatorSignature
      identity.lhs identity.rhs :=
  S5_441Invariant.valid_sameSignature_of_s3_11 identity
    (S5_441Factors.S5_612.valid_s4_69 identity valid)
    (S5_441Factors.S5_612.valid_s3_11 identity valid)

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_612.table.semigroup) :
    S5_441Invariant.sameSignature identity.lhs identity.rhs :=
  valid_sameParitySeparatorSignature identity valid

end S5_612

end SemigroupBasis.CoRoots
