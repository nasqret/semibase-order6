import SemigroupBasis.CoRoots.Order6SporadicSection15InvariantSyntax

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis

namespace Lemma15_2Invariants

private theorem sortedNodup_eq_of_mem_iff
    {left right : List Nat}
    (leftSorted : left.Pairwise (· ≤ ·))
    (rightSorted : right.Pairwise (· ≤ ·))
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (sameSupport : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left = right := by
  have permutation : left.Perm right := by
    rw [List.perm_iff_count]
    intro letter
    rw [leftNodup.count, rightNodup.count]
    simp only [sameSupport letter]
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
    leftSorted rightSorted permutation

theorem sortedDoubledLetters_eq
    {left right : Word Nat}
    (same : Lemma15_2Invariants left right) :
    CanonicalData.sortedDoubledLetters left.toList =
      CanonicalData.sortedDoubledLetters right.toList := by
  apply sortedNodup_eq_of_mem_iff
    (CanonicalData.sortedDoubledLetters_pairwise left.toList)
    (CanonicalData.sortedDoubledLetters_pairwise right.toList)
    (CanonicalData.sortedDoubledLetters_nodup left.toList)
    (CanonicalData.sortedDoubledLetters_nodup right.toList)
  intro letter
  rw [CanonicalData.sortedDoubledLetters_mem_iff,
    CanonicalData.sortedDoubledLetters_mem_iff]
  rw [← S5_213Syntax.cappedMultiplicity_eq_two_iff,
    ← S5_213Syntax.cappedMultiplicity_eq_two_iff,
    same.countStrata letter]

theorem sortedHighCountLetters_eq
    {left right : Word Nat}
    (same : Lemma15_2Invariants left right) :
    CanonicalData.sortedHighCountLetters left.toList =
      CanonicalData.sortedHighCountLetters right.toList := by
  apply sortedNodup_eq_of_mem_iff
    (CanonicalData.sortedHighCountLetters_pairwise left.toList)
    (CanonicalData.sortedHighCountLetters_pairwise right.toList)
    (CanonicalData.sortedHighCountLetters_nodup left.toList)
    (CanonicalData.sortedHighCountLetters_nodup right.toList)
  intro letter
  rw [CanonicalData.sortedHighCountLetters_mem_iff,
    CanonicalData.sortedHighCountLetters_mem_iff]
  rw [← S5_213Syntax.cappedMultiplicity_eq_three_iff,
    ← S5_213Syntax.cappedMultiplicity_eq_three_iff,
    same.countStrata letter]

theorem initialSimpleBlock_eq
    {left right : Word Nat}
    (same : Lemma15_2Invariants left right) :
    S5_107.initialSimpleBlock left.toList =
      S5_107.initialSimpleBlock right.toList :=
  same.toSimpleAdjacencySignature.initialSimpleBlock_eq

theorem finalSimpleBlock_eq
    {left right : Word Nat}
    (same : Lemma15_2Invariants left right) :
    S5_107.finalSimpleBlock left.toList =
      S5_107.finalSimpleBlock right.toList :=
  same.toSimpleAdjacencySignature.finalSimpleBlock_eq

theorem sortedInteriorSimpleBlocks_eq
    {left right : Word Nat}
    (same : Lemma15_2Invariants left right) :
    S5_107.sortedSimpleBlocks
        (S5_107.interiorSimpleBlocks left.toList) =
      S5_107.sortedSimpleBlocks
        (S5_107.interiorSimpleBlocks right.toList) :=
  S5_107.sortedSimpleBlocks_eq_of_perm
    same.toSimpleAdjacencySignature.interiorSimpleBlocks_perm

theorem alphaRenderData_eq
    {left right : Word Nat}
    (same : Lemma15_2Invariants left right) :
    CanonicalData.alphaRenderData left.toList =
      CanonicalData.alphaRenderData right.toList := by
  unfold CanonicalData.alphaRenderData
  rw [same.sortedDoubledLetters_eq,
    same.sortedInteriorSimpleBlocks_eq,
    same.finalSimpleBlock_eq,
    same.initialSimpleBlock_eq]

theorem betaRenderData_eq
    {left right : Word Nat}
    (same : Lemma15_2Invariants left right) :
    CanonicalData.betaRenderData left.toList =
      CanonicalData.betaRenderData right.toList := by
  unfold CanonicalData.betaRenderData
  rw [same.sortedInteriorSimpleBlocks_eq,
    same.finalSimpleBlock_eq,
    same.initialSimpleBlock_eq,
    same.sortedDoubledLetters_eq,
    same.sortedHighCountLetters_eq]

theorem alphaCanonicalList_eq
    {left right : Word Nat}
    (same : Lemma15_2Invariants left right) :
    CanonicalData.alphaCanonicalList left.toList =
      CanonicalData.alphaCanonicalList right.toList := by
  simpa only [CanonicalData.alphaCanonicalList] using
    congrArg CanonicalData.renderAlphaData same.alphaRenderData_eq

theorem betaCanonicalList_eq
    {left right : Word Nat}
    (same : Lemma15_2Invariants left right) :
    CanonicalData.betaCanonicalList left.toList =
      CanonicalData.betaCanonicalList right.toList := by
  simpa only [CanonicalData.betaCanonicalList] using
    congrArg CanonicalData.renderBetaData same.betaRenderData_eq

theorem canonicalBranch_eq
    {left right : Word Nat}
    (same : Lemma15_2Invariants left right) :
    CanonicalData.canonicalBranch left.toList =
      CanonicalData.canonicalBranch right.toList := by
  unfold CanonicalData.canonicalBranch
  rw [same.sortedHighCountLetters_eq,
    same.sortedDoubledLetters_eq]

private theorem sortedMultipleLetters_eq_nil_of_simple_branch
    (word : Word Nat)
    (branch : CanonicalData.canonicalBranch word.toList = .simple) :
    S5_107.sortedMultipleLetters word.toList = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro letter member
  have multiple :=
    (S5_107.sortedMultipleLetters_mem_iff
      letter word.toList).1 member
  have classified :=
    (CanonicalData.sortedMultiplicityClasses_mem_iff
      letter word.toList).2 multiple
  unfold CanonicalData.canonicalBranch at branch
  cases highShape :
      CanonicalData.sortedHighCountLetters word.toList with
  | cons high rest =>
      simp [highShape] at branch
  | nil =>
      cases doubledShape :
          CanonicalData.sortedDoubledLetters word.toList with
      | cons doubled rest =>
          simp [highShape, doubledShape] at branch
      | nil =>
          rw [highShape, doubledShape] at classified
          simp at classified

/-- The deterministic Section 15 renderer depends only on the four fields of
Lemma 15.2. This is the unrestricted uniqueness half of Proposition 15.1; it
does not assert that an arbitrary word derives to the rendered form. -/
theorem canonicalList_eq
    {left right : Word Nat}
    (same : Lemma15_2Invariants left right) :
    CanonicalData.canonicalList left.toList =
      CanonicalData.canonicalList right.toList := by
  have branchEq := same.canonicalBranch_eq
  unfold CanonicalData.canonicalList
  rw [branchEq]
  cases branchShape : CanonicalData.canonicalBranch right.toList with
  | alpha => exact same.alphaCanonicalList_eq
  | beta => exact same.betaCanonicalList_eq
  | simple =>
      have rightMultiple :=
        sortedMultipleLetters_eq_nil_of_simple_branch right branchShape
      have leftMultiple :
          S5_107.sortedMultipleLetters left.toList = [] := by
        rw [same.toSimpleAdjacencySignature.sortedMultipleLetters_eq,
          rightMultiple]
      have oldCanonical :=
        same.toSimpleAdjacencySignature.canonicalList_eq
      simpa [S5_107.simpleAdjacencyCanonicalList,
        leftMultiple, rightMultiple] using oldCanonical

end Lemma15_2Invariants

end SemigroupBasis.CoRoots.Order6SporadicSection15
