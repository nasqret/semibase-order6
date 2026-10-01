import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank049
import SemigroupBasis.CoRoots.Order6FactorPairS2S5353Normal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S5_120Family

/-!
# An unrestricted `S2_4 × S5_245` family seed

The authenticated rank-049 basis is definitionally the previously reviewed
seventeen-law `S2_2 × S5_353` endpoint calculus.  Its normal-form proof only
needs a common initial variable, unrestricted validity in the simple-endpoints
semigroup, and unrestricted validity in the cyclic-two semigroup.  The actual
`S2_4` factor supplies the initial-variable equality, while the independently
certified quotient and embedding of `S5_245` supply the remaining invariants.

The constant simple-endpoints valuation separates singleton words from all
longer words.  After that honest semantic split, the reviewed shared endpoint
normalizer proves unrestricted completeness for the exact displayed laws.  No
validity implication between `S5_245` and `S5_353` is assumed.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank049.Seed

open SemigroupBasis
open SemigroupBasis.Examples

universe u v

/-- The authenticated staged basis is exactly the reviewed historic calculus. -/
theorem displayedBasis_eq_legacy :
    basis = SemigroupBasis.CoRoots.Order6FactorPairS2S5353Normal.basis := by
  rfl

/-- Validity in the actual left-zero factor fixes the initial variable. -/
theorem leftValid_head
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  change identity.SatisfiedBy leftZeroTwo.semigroup at valid
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 :=
    fun letter => if letter = identity.lhs.head then 0 else 1
  have evaluated := valid valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm different] at evaluated

/-- The genuine simple-endpoints quotient detects singleton words exactly. -/
theorem simpleValid_tail_nil_iff
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy simpleEndpointsFour.semigroup) :
    identity.lhs.tail = [] ↔ identity.rhs.tail = [] := by
  have evaluated := valid (fun _ => (1 : Fin 4))
  constructor
  · intro leftSingleton
    apply (simpleEndpointsSingletonSeparator identity.rhs).mp
    rw [← evaluated]
    exact
      (simpleEndpointsSingletonSeparator identity.lhs).mpr leftSingleton
  · intro rightSingleton
    apply (simpleEndpointsSingletonSeparator identity.lhs).mp
    rw [evaluated]
    exact
      (simpleEndpointsSingletonSeparator identity.rhs).mpr rightSingleton

/-- Independent unrestricted factor invariants suffice for the historic
seventeen-law endpoint normalizer; no relation to the old `S5_353` factor is
assumed or synthesized. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have heads := leftValid_head identity leftValid
  have genuineRight :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_245.table.semigroup := by
    simpa [rightTable] using rightValid
  have simpleValid :=
    SemigroupBasis.CoRoots.S5_120Family.S5_245.valid_simpleEndpoints
      identity genuineRight
  have parityValid :=
    SemigroupBasis.CoRoots.S5_120Family.S5_245.valid_cyclicTwo
      identity genuineRight
  have singletonIff := simpleValid_tail_nil_iff identity simpleValid
  rcases identity with
    ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
  change leftHead = rightHead at heads
  change leftTail = [] ↔ rightTail = [] at singletonIff
  subst rightHead
  cases leftTail with
  | nil =>
      have rightNil : rightTail = [] := singletonIff.mp rfl
      subst rightTail
      exact Derives.refl _
  | cons leftSecond leftRest =>
      cases rightTail with
      | nil =>
          have impossible :
              leftSecond :: leftRest = [] :=
            singletonIff.mpr rfl
          simp at impossible
      | cons rightSecond rightRest =>
          let leftSuffix : Word Nat :=
            Word.mk leftSecond leftRest
          let rightSuffix : Word Nat :=
            Word.mk rightSecond rightRest
          let leftSplit := splitPrefixFinal leftSuffix
          let rightSplit := splitPrefixFinal rightSuffix
          have leftReconstruct :
              wordOfEndpoints leftHead leftSplit.1 leftSplit.2 =
                Word.mk leftHead (leftSecond :: leftRest) := by
            rw [wordOfEndpoints_eq]
            simp only [leftSplit]
            rw [wordOfPrefixFinal_split leftSuffix]
            rfl
          have rightReconstruct :
              wordOfEndpoints leftHead rightSplit.1 rightSplit.2 =
                Word.mk leftHead (rightSecond :: rightRest) := by
            rw [wordOfEndpoints_eq]
            simp only [rightSplit]
            rw [wordOfPrefixFinal_split rightSuffix]
            rfl
          have simpleEqual :
              ∀ valuation : Nat → Fin 4,
                simpleEndpointsFour.semigroup.eval valuation
                    (wordOfEndpoints
                      leftHead leftSplit.1 leftSplit.2) =
                  simpleEndpointsFour.semigroup.eval valuation
                    (wordOfEndpoints
                      leftHead rightSplit.1 rightSplit.2) := by
            intro valuation
            rw [leftReconstruct, rightReconstruct]
            exact simpleValid valuation
          have parityEqual :
              ∀ valuation : Nat → Fin 2,
                cyclicTwo.semigroup.eval valuation
                    (wordOfEndpoints
                      leftHead leftSplit.1 leftSplit.2) =
                  cyclicTwo.semigroup.eval valuation
                    (wordOfEndpoints
                      leftHead rightSplit.1 rightSplit.2) := by
            intro valuation
            rw [leftReconstruct, rightReconstruct]
            exact parityValid valuation
          have derivation :=
            SemigroupBasis.CoRoots.Order6FactorPairS2S5353Normal.derivesEndpointWordsSameInitial
              leftHead leftSplit.1 leftSplit.2
              rightSplit.1 rightSplit.2
              simpleEqual parityEqual
          rw [leftReconstruct, rightReconstruct] at derivation
          simpa only [displayedBasis_eq_legacy] using derivation

/-- Package the factor intersection only after unrestricted completeness. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- Quotient normalization is downstream of the honest joint proof. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_6222_representative_basis :
    BasisFor S6_6222.table.semigroup basis :=
  S6_6222.representative_basis_of_normalizer normalizer

theorem s6_6222_opposite_basis :
    BasisFor S6_6222.table.semigroup.opposite (reversedBasis basis) :=
  S6_6222.opposite_basis_of_normalizer normalizer

theorem s6_9873_representative_basis :
    BasisFor S6_9873.table.semigroup basis :=
  S6_9873.representative_basis_of_normalizer normalizer

theorem s6_9873_opposite_basis :
    BasisFor S6_9873.table.semigroup.opposite (reversedBasis basis) :=
  S6_9873.opposite_basis_of_normalizer normalizer

/-- Reviewed common transport still requires every law derivation and both
unrestricted target-to-source factor-theory implications explicitly. -/
noncomputable def transportedNormalizer
    {A : Type u} {B : Type v}
    {targetLeft : Semigroup A} {targetRight : Semigroup B}
    {targetBasis : List (Identity Nat)}
    (lawDerivations :
      ∀ law : Identity Nat,
        law ∈ basis → Derives targetBasis law.lhs law.rhs)
    (leftTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetLeft →
          identity.SatisfiedBy leftTable.semigroup)
    (rightTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetRight →
          identity.SatisfiedBy rightTable.semigroup) :
    IntersectionNormalizer targetLeft targetRight targetBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    normalizer lawDerivations leftTheory rightTheory

end SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank049.Seed
