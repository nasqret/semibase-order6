import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_804FinalComponents
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer

/-!
# Unrestricted S2_2 x S5_804 completeness, workload133 / frozen rank092

The actual factor pair supplies occurrence parity and the ordered sequence
of component supports, unary-repeat flags and every component's final letter.
Disjoint supports project the whole-word parity into each aligned component.
The newly proved connected-component theorem then assembles an unrestricted
derivation of the exact ELEVEN laws. Only afterwards is the proved result
refined to a quotient normalizer and transported across the literal cyclic
table identification using the approved transportNormalizer interface.

Both class endpoints are unconditional. The finite/model screen is not a
premise, and no old S5_442 endpoint-changing law is imported as a target law.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank092.Seed

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots
open FinalComponents

theorem count_flatten_eq_component {components : List (List Nat)} {component : List Nat}
    {tested : Nat} (pairwise : components.Pairwise ConnectedComponentSupportsDisjoint)
    (componentMember : component ∈ components) (testedMember : tested ∈ component) :
    components.flatten.count tested = component.count tested := by
  induction components with
  | nil => simp at componentMember
  | cons current remaining induction =>
      rw [List.pairwise_cons] at pairwise
      rcases List.mem_cons.mp componentMember with rfl | componentMember
      · have remainingAbsent : tested ∉ remaining.flatten := by
          intro remainingMember
          rcases List.mem_flatten.mp remainingMember with
            ⟨candidate, candidateMember, candidateContains⟩
          exact (pairwise.1 candidate candidateMember tested testedMember) candidateContains
        simp [List.count_eq_zero.mpr remainingAbsent]
      · have currentAbsent : tested ∉ current := by
          intro currentMember
          exact (pairwise.1 component componentMember tested currentMember) testedMember
        rw [List.flatten_cons, List.count_append, List.count_eq_zero.mpr currentAbsent,
          induction pairwise.2 componentMember]
        simp

/-- Pointwise parity projects into aligned disjoint-support components. -/
theorem componentParity {leftComponents rightComponents : List (List Nat)}
    {left right : List Nat}
    (leftPairwise : leftComponents.Pairwise ConnectedComponentSupportsDisjoint)
    (rightPairwise : rightComponents.Pairwise ConnectedComponentSupportsDisjoint)
    (leftMember : left ∈ leftComponents) (rightMember : right ∈ rightComponents)
    (signature : connectedComponentSignatureOfList left = connectedComponentSignatureOfList right)
    (wholeParity : ∀ tested,
      leftComponents.flatten.count tested % 2 = rightComponents.flatten.count tested % 2) :
    ∀ tested, left.count tested % 2 = right.count tested % 2 := by
  intro tested
  have supports := supportIffOfSignature signature tested
  by_cases present : tested ∈ left
  · have rightPresent := supports.mp present
    rw [← count_flatten_eq_component leftPairwise leftMember present,
      ← count_flatten_eq_component rightPairwise rightMember rightPresent]
    exact wholeParity tested
  · have rightAbsent : tested ∉ right := fun member => present (supports.mpr member)
    rw [List.count_eq_zero.mpr present, List.count_eq_zero.mpr rightAbsent]

theorem deriveAlignedComponents (leftComponents rightComponents : List (List Nat))
    (signatures : leftComponents.map S5_804.connectedCutComponentSignatureOfList =
      rightComponents.map S5_804.connectedCutComponentSignatureOfList)
    (derive : ∀ left, left ∈ leftComponents → ∀ right, right ∈ rightComponents →
      S5_804.connectedCutComponentSignatureOfList left = S5_804.connectedCutComponentSignatureOfList right →
      ListDerives left right) :
    ListDerives leftComponents.flatten rightComponents.flatten := by
  induction leftComponents generalizing rightComponents with
  | nil =>
      cases rightComponents with
      | nil => exact S5_107.ListDerives.empty
      | cons head tail => simp at signatures
  | cons head tail induction =>
      cases rightComponents with
      | nil => simp at signatures
      | cons rightHead rightTail =>
          simp only [List.map_cons, List.cons.injEq] at signatures
          have headDerivation := derive head (by simp) rightHead (by simp) signatures.1
          have tailDerivation := induction rightTail signatures.2 (by
            intro left leftMember right rightMember same
            exact derive left (List.mem_cons_of_mem head leftMember)
              right (List.mem_cons_of_mem rightHead rightMember) same)
          simpa only [List.flatten_cons] using
            (headDerivation.append tail.flatten).trans (tailDerivation.prepend rightHead)

/-- Full, unbounded derivational sufficiency of the actual factor key. -/
theorem derives_of_signatures {left right : Word Nat} (same : SameSignature left right) :
    Derives basis left right := by
  let leftComponents := connectedComponentDecomposeWord left
  let rightComponents := connectedComponentDecomposeWord right
  have signatures : leftComponents.map S5_804.connectedCutComponentSignatureOfList =
      rightComponents.map S5_804.connectedCutComponentSignatureOfList := by
    simpa [leftComponents, rightComponents, S5_804.SameConnectedCutSignature,
      S5_804.connectedCutSignaturesWord, S5_804.connectedCutSignaturesList,
      connectedComponentDecomposeWord] using same.componentFinal
  have leftFlatten : leftComponents.flatten = left.toList := connectedComponentDecomposeWord_flatten left
  have rightFlatten : rightComponents.flatten = right.toList := connectedComponentDecomposeWord_flatten right
  have wholeParity : ∀ tested,
      leftComponents.flatten.count tested % 2 = rightComponents.flatten.count tested % 2 := by
    intro tested
    rw [leftFlatten, rightFlatten]
    exact same.parity tested
  have leftPairwise := connectedComponentDecomposeWord_pairwiseDisjoint left
  have rightPairwise := connectedComponentDecomposeWord_pairwiseDisjoint right
  have joined := deriveAlignedComponents leftComponents rightComponents signatures (by
    intro leftComponent leftMember rightComponent rightMember signature
    have baseEqual : connectedComponentSignatureOfList leftComponent =
        connectedComponentSignatureOfList rightComponent :=
      congrArg S5_804.ConnectedCutComponentSignature.base signature
    have finalEqual : S5_804.componentFinal leftComponent = S5_804.componentFinal rightComponent :=
      congrArg S5_804.ConnectedCutComponentSignature.final signature
    exact listDerivesConnectedFinal
      (connectedComponentDecomposeWord_nonempty_components left leftComponent leftMember)
      (connectedComponentDecomposeWord_nonempty_components right rightComponent rightMember)
      (connectedComponentDecomposeWord_supportConnected left leftComponent leftMember)
      (connectedComponentDecomposeWord_supportConnected right rightComponent rightMember)
      baseEqual finalEqual
      (componentParity leftPairwise rightPairwise leftMember rightMember baseEqual wholeParity))
  have listDerivation : ListDerives left.toList right.toList := by
    rw [leftFlatten, rightFlatten] at joined
    exact joined
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail => exact S5_107.ListDerives.toWord listDerivation

theorem derives_of_factor_valid (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derives_of_signatures (sameSignature_of_factorValid identity leftValid rightValid)

def intersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- The semantic C2 model is literally the catalogue table, not merely a
bounded equivalent. This source intersection is proved before normality. -/
def cyclicIntersectionBasis : IntersectionBasis cyclicTwo.semigroup rightTable.semigroup basis where
  leftModels := by
    rw [← leftTable_eq_cyclic]
    exact leftModels
  rightModels := rightModels
  complete := by
    intro identity cyclicValid rightValid
    apply derives_of_factor_valid identity ?_ rightValid
    rw [leftTable_eq_cyclic]
    exact cyclicValid

/-- Approved theory transport applied to an already proved unrestricted
seed, with literal catalogue-to-C2 identification and identical laws. -/
noncomputable def normalizer : IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    (Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer cyclicIntersectionBasis)
    (by intro law member; exact Derives.fromBasis member)
    (by intro identity valid; rw [leftTable_eq_cyclic] at valid; exact valid)
    (by intro identity valid; exact valid)

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank092.Seed

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank092.S6_8864

open SemigroupBasis

/-- Literal zero-based catalogue rows, also checked before authoring. -/
theorem table_rows_exact :
    List.ofFn (fun left : Fin 6 => List.ofFn (fun right : Fin 6 => (table.mul left right).val)) =
      [[0,0,2,0,0,0], [0,0,2,0,0,1], [2,2,0,2,2,2],
       [0,1,2,3,4,0], [0,1,2,3,4,1], [0,0,2,0,0,5]] := by
  decide

theorem representative_basis : BasisFor table.semigroup basis :=
  representative_basis_of_normalizer Seed.normalizer

theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  opposite_basis_of_normalizer Seed.normalizer

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank092.S6_8864
