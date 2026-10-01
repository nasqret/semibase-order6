import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS5_379OrderedInterior
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal

/-!
# Unrestricted exact S3_16 × S5_379 joint completeness

The nine displayed laws derive equality from the actual two-factor signature:
the ordered connected-component supports, capped multiplicities, and full
first-occurrence order. Connected components are normalized without changing
their first head or sorting distinct first occurrences. Disjoint-support
projection then recovers each component's order and counts from the whole
word. No bounded screen, oracle, or unproved completeness premise is used.

Only after proving unrestricted derivability do we refine the result to the
shared proof-producing normalizer interface.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank105.Seed

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots
open OrderedInterior

/-- Compare arbitrary nonempty connected components at their original first
letter. Singleton/nontrivial mismatches are excluded by the actual capped
multiplicity of that first letter. -/
theorem listDerivesConnected {left right : List Nat}
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (leftConnected : ConnectedComponentSupportConnected left)
    (rightConnected : ConnectedComponentSupportConnected right)
    (order : firstOccurrenceSequence left = firstOccurrenceSequence right)
    (counts : ∀ tested, min (left.count tested) 2 = min (right.count tested) 2) :
    ListDerives left right := by
  cases left with
  | nil => exact False.elim (leftNonempty rfl)
  | cons head tail =>
      cases right with
      | nil => exact False.elim (rightNonempty rfl)
      | cons other rest =>
          have heads : head = other := (List.cons.inj order).1
          subst other
          cases tail with
          | nil =>
              cases rest with
              | nil => exact S5_107.ListDerives.refl _
              | cons next remaining =>
                  have member := connectedComponentSupportConnected_cons_tail
                    rightConnected (by simp)
                  have positive := List.count_pos_iff.mpr member
                  have equal := counts head
                  simp only [List.count_cons_self, List.count_nil] at equal
                  omega
          | cons next remaining =>
              cases rest with
              | nil =>
                  have member := connectedComponentSupportConnected_cons_tail
                    leftConnected (by simp)
                  have positive := List.count_pos_iff.mpr member
                  have equal := counts head
                  simp only [List.count_cons_self, List.count_nil] at equal
                  omega
              | cons rightNext rightRemaining =>
                  obtain ⟨leftInterior, leftDerivation, leftAbsent, leftLimited⟩ :=
                    existsNormalizedEnvelope head next remaining leftConnected
                  obtain ⟨rightInterior, rightDerivation, rightAbsent, rightLimited⟩ :=
                    existsNormalizedEnvelope head rightNext rightRemaining rightConnected
                  have normalizedOrder := (listDerives_firstOrder leftDerivation).symm.trans
                    (order.trans (listDerives_firstOrder rightDerivation))
                  have normalizedCounts : ∀ tested,
                      min ((head :: leftInterior ++ [head]).count tested) 2 =
                        min ((head :: rightInterior ++ [head]).count tested) 2 := by
                    intro tested
                    exact (listDerives_cappedCounts leftDerivation tested).symm.trans
                      ((counts tested).trans (listDerives_cappedCounts rightDerivation tested))
                  have middle := compareNormalizedEnvelopes head leftInterior rightInterior
                    leftAbsent rightAbsent leftLimited rightLimited normalizedOrder normalizedCounts
                  exact leftDerivation.trans (middle.trans rightDerivation.symm)

theorem supportIffOfSignature {left right : List Nat}
    (same : connectedComponentSignatureOfList left = connectedComponentSignatureOfList right)
    (tested : Nat) : tested ∈ left ↔ tested ∈ right := by
  have supports := congrArg (fun signature => tested ∈ signature.support) same
  have membership : (tested ∈ left) = (tested ∈ right) := by
    simpa only [connectedComponentSignatureOfList_support,
      connectedComponentSortedSupport_mem_iff] using supports
  exact Iff.of_eq membership

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

/-- Filtering a disjoint component concatenation by one component's support
recovers that entire component, including its order and multiplicities. -/
theorem filter_flatten_eq_component {components : List (List Nat)} {component : List Nat}
    (pairwise : components.Pairwise ConnectedComponentSupportsDisjoint)
    (componentMember : component ∈ components) :
    components.flatten.filter (fun tested => decide (tested ∈ component)) = component := by
  induction components with
  | nil => simp at componentMember
  | cons current remaining induction =>
      rw [List.pairwise_cons] at pairwise
      rcases List.mem_cons.mp componentMember with rfl | componentMember
      · have currentFilter : component.filter (fun tested => decide (tested ∈ component)) = component := by
          apply List.filter_eq_self.mpr
          intro tested member
          simp [member]
        have remainingFilter :
            remaining.flatten.filter (fun tested => decide (tested ∈ component)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro tested member
          have absent : tested ∉ component := by
            intro currentMember
            rcases List.mem_flatten.mp member with
              ⟨candidate, candidateMember, candidateContains⟩
            exact (pairwise.1 candidate candidateMember tested currentMember) candidateContains
          simp [absent]
        simp only [List.flatten_cons, List.filter_append, currentFilter, remainingFilter,
          List.append_nil]
      · have currentFilter : current.filter (fun tested => decide (tested ∈ component)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro tested member
          have absent := pairwise.1 component componentMember tested member
          simp [absent]
        rw [List.flatten_cons, List.filter_append, currentFilter,
          induction pairwise.2 componentMember]
        simp

/-- Component order is a projection of the whole word's first order. -/
theorem componentFirstOrder {leftComponents rightComponents : List (List Nat)}
    {left right : List Nat}
    (leftPairwise : leftComponents.Pairwise ConnectedComponentSupportsDisjoint)
    (rightPairwise : rightComponents.Pairwise ConnectedComponentSupportsDisjoint)
    (leftMember : left ∈ leftComponents) (rightMember : right ∈ rightComponents)
    (same : connectedComponentSignatureOfList left = connectedComponentSignatureOfList right)
    (wholeOrder : firstOccurrenceSequence leftComponents.flatten =
      firstOccurrenceSequence rightComponents.flatten) :
    firstOccurrenceSequence left = firstOccurrenceSequence right := by
  have keepEqual : (fun tested : Nat => decide (tested ∈ left)) =
      (fun tested : Nat => decide (tested ∈ right)) := by
    funext tested
    by_cases member : tested ∈ left
    · simp [member, (supportIffOfSignature same tested).mp member]
    · have absent : tested ∉ right := fun h => member ((supportIffOfSignature same tested).mpr h)
      simp [member, absent]
  have selected := congrArg (List.filter (fun tested => decide (tested ∈ left))) wholeOrder
  rw [← firstOccurrenceSequence_filter, ← firstOccurrenceSequence_filter] at selected
  rw [filter_flatten_eq_component leftPairwise leftMember, keepEqual,
    filter_flatten_eq_component rightPairwise rightMember] at selected
  exact selected

theorem componentCappedCounts {leftComponents rightComponents : List (List Nat)}
    {left right : List Nat}
    (leftPairwise : leftComponents.Pairwise ConnectedComponentSupportsDisjoint)
    (rightPairwise : rightComponents.Pairwise ConnectedComponentSupportsDisjoint)
    (leftMember : left ∈ leftComponents) (rightMember : right ∈ rightComponents)
    (same : connectedComponentSignatureOfList left = connectedComponentSignatureOfList right)
    (wholeCounts : ∀ tested, min (leftComponents.flatten.count tested) 2 =
      min (rightComponents.flatten.count tested) 2) (tested : Nat) :
    min (left.count tested) 2 = min (right.count tested) 2 := by
  by_cases member : tested ∈ left
  · have rightContains := (supportIffOfSignature same tested).mp member
    rw [← count_flatten_eq_component leftPairwise leftMember member,
      ← count_flatten_eq_component rightPairwise rightMember rightContains]
    exact wholeCounts tested
  · have rightAbsent : tested ∉ right := fun h => member ((supportIffOfSignature same tested).mpr h)
    rw [List.count_eq_zero.mpr member, List.count_eq_zero.mpr rightAbsent]

/-- Concatenate derivations for aligned signatures. The callback retains the
fixed original whole-word invariants throughout the structural recursion. -/
theorem deriveAlignedWith (leftComponents rightComponents : List (List Nat))
    (signatures : leftComponents.map connectedComponentSignatureOfList =
      rightComponents.map connectedComponentSignatureOfList)
    (derive : ∀ left, left ∈ leftComponents → ∀ right, right ∈ rightComponents →
      connectedComponentSignatureOfList left = connectedComponentSignatureOfList right →
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

/-- Unrestricted joint completeness for arbitrary nonempty natural-variable
words and the exact nine-law displayed presentation. -/
theorem derives_of_signatures {left right : Word Nat} (same : SameSignature left right) :
    Derives basis left right := by
  let leftComponents := connectedComponentDecomposeWord left
  let rightComponents := connectedComponentDecomposeWord right
  have signatures : leftComponents.map connectedComponentSignatureOfList =
      rightComponents.map connectedComponentSignatureOfList := by
    simpa [leftComponents, rightComponents, connectedComponentSignaturesWord,
      connectedComponentSignaturesList, connectedComponentDecomposeWord] using
      S5_379.sameComponentSignatures_of_sameComponentSimpleSignature same.componentSimple
  have leftFlatten : leftComponents.flatten = left.toList :=
    connectedComponentDecomposeWord_flatten left
  have rightFlatten : rightComponents.flatten = right.toList :=
    connectedComponentDecomposeWord_flatten right
  have wholeOrder : firstOccurrenceSequence leftComponents.flatten =
      firstOccurrenceSequence rightComponents.flatten := by
    rw [leftFlatten, rightFlatten]
    exact same.firstOrder
  have wholeCounts : ∀ tested, min (leftComponents.flatten.count tested) 2 =
      min (rightComponents.flatten.count tested) 2 := by
    intro tested
    rw [leftFlatten, rightFlatten]
    exact S5_379.cappedCounts_eq_of_sameComponentSimpleSignature same.componentSimple tested
  have leftPairwise := connectedComponentDecomposeWord_pairwiseDisjoint left
  have rightPairwise := connectedComponentDecomposeWord_pairwiseDisjoint right
  have joined := deriveAlignedWith leftComponents rightComponents signatures (by
    intro leftComponent leftMember rightComponent rightMember signature
    exact listDerivesConnected
      (connectedComponentDecomposeWord_nonempty_components left leftComponent leftMember)
      (connectedComponentDecomposeWord_nonempty_components right rightComponent rightMember)
      (connectedComponentDecomposeWord_supportConnected left leftComponent leftMember)
      (connectedComponentDecomposeWord_supportConnected right rightComponent rightMember)
      (componentFirstOrder leftPairwise rightPairwise leftMember rightMember signature wholeOrder)
      (componentCappedCounts leftPairwise rightPairwise leftMember rightMember signature wholeCounts))
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

/-- The shared normalizer interface is populated only from the proved,
unrestricted joint derivation theorem above. -/
noncomputable def normalizer : IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer intersectionBasis

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank105.Seed
