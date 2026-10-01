import SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16Basis
import SemigroupBasis.CoRoots.S5_442Invariant

/-!
# Exact component/count-mod-three semantics for d029

The direct product `S4_124 x S4_70` recognizes exactly the ordered connected
component signature together with every variable count modulo three.  This
module proves both semantic directions and records that every literal B16
derivation preserves that exact invariant.  It does not prove B16
completeness; the unconditional normalizer is a downstream kernel gate.
-/

namespace SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16

open SemigroupBasis
open SemigroupBasis.Examples

/-- Equality of the exact ordered `S4_70` component signatures. -/
def SameComponentSignature (left right : Word Nat) : Prop :=
  connectedComponentSignaturesWord left =
    connectedComponentSignaturesWord right

/-- Pointwise equality of all occurrence counts modulo three. -/
def SameOccurrenceModThree (left right : Word Nat) : Prop :=
  ∀ letter,
    left.toList.count letter % 3 =
      right.toList.count letter % 3

/-- The exact direct-product invariant for the d029 anchor pair. -/
structure SameModThreeComponentSignature
    (left right : Word Nat) : Prop where
  components : SameComponentSignature left right
  modThree : SameOccurrenceModThree left right

abbrev sameSignature (left right : Word Nat) : Prop :=
  SameModThreeComponentSignature left right

namespace SameModThreeComponentSignature

theorem refl (word : Word Nat) :
    SameModThreeComponentSignature word word :=
  ⟨rfl, fun _ => rfl⟩

theorem symm {left right : Word Nat}
    (same : SameModThreeComponentSignature left right) :
    SameModThreeComponentSignature right left :=
  ⟨same.components.symm,
    fun letter => (same.modThree letter).symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameModThreeComponentSignature left middle)
    (second : SameModThreeComponentSignature middle right) :
    SameModThreeComponentSignature left right :=
  ⟨first.components.trans second.components,
    fun letter =>
      (first.modThree letter).trans (second.modThree letter)⟩

end SameModThreeComponentSignature

/-- Equal component signatures already imply equal support, so the exact
invariant needs no redundant support field. -/
theorem sameSupport_of_sameComponentSignature
    {left right : Word Nat}
    (same : SameComponentSignature left right) :
    ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList :=
  S5_442Invariant.sameSupport_of_sameComponentSignature same

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

/-! ## Necessity from the two direct factors -/

/-- Equality of `S4_124` term functions determines every occurrence count
modulo three. -/
theorem sameOccurrenceModThree_of_s4_124_equalEval
    (left right : Word Nat)
    (equalEval :
      ∀ valuation : Nat → Fin
          SemigroupBasis.Generated.S4_124.table.order,
        SemigroupBasis.Generated.S4_124.table.semigroup.eval
            valuation left =
          SemigroupBasis.Generated.S4_124.table.semigroup.eval
            valuation right) :
    SameOccurrenceModThree left right :=
  positiveModThreeValid_count_mod_three
    (Identity.mk left right)
    (equalEval_of_table_eq
      SemigroupBasis.Generated.S4_124.table_eq_catalogue_model
      left right equalEval)

/-- Equality of `S4_70` term functions determines the exact ordered
component signature. -/
theorem sameComponentSignature_of_s4_70_equalEval
    (left right : Word Nat)
    (equalEval :
      ∀ valuation : Nat → Fin
          SemigroupBasis.Generated.S4_70.table.order,
        SemigroupBasis.Generated.S4_70.table.semigroup.eval
            valuation left =
          SemigroupBasis.Generated.S4_70.table.semigroup.eval
            valuation right) :
    SameComponentSignature left right :=
  S5_442Invariant.sameComponentSignature_of_connectedComponentFour_equalEval
    left right
    (equalEval_of_table_eq
      SemigroupBasis.Generated.S4_70.table_eq_catalogue_model
      left right equalEval)

/-! ## Sufficiency for the two direct factors -/

/-- Equal support and positive multiplicities modulo three give a direct
derivation in the complete `S4_124` two-law basis. -/
theorem commutativePositiveModThreeDerives_of_sameSupportModThree
    (left right : Word Nat)
    (support :
      ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList)
    (modThree : SameOccurrenceModThree left right) :
    Derives commutativePositiveModThreeBasis left right := by
  have reducedPerm :
      (positiveModThreeReduce left.toList).Perm
        (positiveModThreeReduce right.toList) :=
    positiveModThreeReduce_perm support modThree
  have leftNormal := positiveModThreeDerivesNormal left
  have rightNormal := positiveModThreeDerivesNormal right
  cases leftReduction : positiveModThreeReduce left.toList with
  | nil =>
      have present :
          left.head ∈ positiveModThreeReduce left.toList :=
        (mem_positiveModThreeReduce_iff _ _).mpr <| by
          simp [Word.toList]
      simp [leftReduction] at present
  | cons leftHead leftTail =>
      cases rightReduction : positiveModThreeReduce right.toList with
      | nil =>
          rw [leftReduction, rightReduction] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons rightHead rightTail =>
          rw [leftReduction] at leftNormal
          rw [rightReduction] at rightNormal
          rw [leftReduction, rightReduction] at reducedPerm
          exact leftNormal.trans <|
            (positiveModThreeDerivesPermutation
              (Word.mk leftHead leftTail)
              (Word.mk rightHead rightTail)
              reducedPerm).trans rightNormal.symm

/-- The exact invariant is sufficient for equality of direct `S4_124` term
functions. -/
theorem s4_124_equalEval_of_sameModThreeComponentSignature
    (left right : Word Nat)
    (same : SameModThreeComponentSignature left right) :
    ∀ valuation : Nat → Fin
        SemigroupBasis.Generated.S4_124.table.order,
      SemigroupBasis.Generated.S4_124.table.semigroup.eval
          valuation left =
        SemigroupBasis.Generated.S4_124.table.semigroup.eval
          valuation right :=
  (commutativePositiveModThreeDerives_of_sameSupportModThree
      left right
      (sameSupport_of_sameComponentSignature same.components)
      same.modThree).sound
    SemigroupBasis.Generated.S4_124.representative_basis.1

/-- The exact invariant is sufficient for equality of direct `S4_70` term
functions. -/
theorem s4_70_equalEval_of_sameModThreeComponentSignature
    (left right : Word Nat)
    (same : SameModThreeComponentSignature left right) :
    ∀ valuation : Nat → Fin
        SemigroupBasis.Generated.S4_70.table.order,
      SemigroupBasis.Generated.S4_70.table.semigroup.eval
          valuation left =
        SemigroupBasis.Generated.S4_70.table.semigroup.eval
          valuation right :=
  equalEval_of_table_eq
    SemigroupBasis.Generated.S4_70.table_eq_catalogue_model.symm
    left right
    (S5_442Invariant.connectedComponentFour_equalEval_of_sameComponentSignature
      left right same.components)

/-! ## Exact product-semantic bridge -/

/-- Validity in both selected direct factors implies the exact d029
signature. -/
theorem sameModThreeComponentSignature_of_factorValidity
    (identity : Identity Nat)
    (modThreeValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_124.table.semigroup)
    (componentValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_70.table.semigroup) :
    SameModThreeComponentSignature identity.lhs identity.rhs :=
  ⟨sameComponentSignature_of_s4_70_equalEval
      identity.lhs identity.rhs componentValid,
    sameOccurrenceModThree_of_s4_124_equalEval
      identity.lhs identity.rhs modThreeValid⟩

/-- The exact d029 signature implies validity in both selected direct
factors. -/
theorem factorValidity_of_sameModThreeComponentSignature
    (identity : Identity Nat)
    (same :
      SameModThreeComponentSignature identity.lhs identity.rhs) :
    identity.SatisfiedBy
          SemigroupBasis.Generated.S4_124.table.semigroup ∧
      identity.SatisfiedBy
          SemigroupBasis.Generated.S4_70.table.semigroup :=
  ⟨s4_124_equalEval_of_sameModThreeComponentSignature
      identity.lhs identity.rhs same,
    s4_70_equalEval_of_sameModThreeComponentSignature
      identity.lhs identity.rhs same⟩

/-- The exact semantic iff for the selected direct-product factors. -/
theorem factorValidity_iff_sameModThreeComponentSignature
    (identity : Identity Nat) :
    (identity.SatisfiedBy
          SemigroupBasis.Generated.S4_124.table.semigroup ∧
      identity.SatisfiedBy
          SemigroupBasis.Generated.S4_70.table.semigroup) ↔
      SameModThreeComponentSignature identity.lhs identity.rhs :=
  ⟨fun valid =>
      sameModThreeComponentSignature_of_factorValidity
        identity valid.1 valid.2,
    factorValidity_of_sameModThreeComponentSignature identity⟩

/-- Every literal B16 derivation preserves the exact d029 signature. -/
theorem derives_sameModThreeComponentSignature
    {left right : Word Nat}
    (derivation : Derives B16 left right) :
    SameModThreeComponentSignature left right :=
  sameModThreeComponentSignature_of_factorValidity
    (Identity.mk left right)
    (derivation.sound s4_124_models)
    (derivation.sound s4_70_models)

end SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16
