import Init.Data.List.Sort.Lemmas
import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedSquareFusion

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquarePermutation

open CrossFactor CrossSweep BinaryPowers FactorContexts OccurrenceWitnesses
  MarkedZones OrderedSquareForm SquareFusion

private theorem gap_context_toList (word : Word Nat) (letters : List Nat) :
    (gap word (contextWord letters)).toList = word.toList ++ letters := by
  cases letters with
  | nil => exact (List.append_nil word.toList).symm
  | cons first rest => exact Word.toList_append word (Word.mk first rest)

/-- Interchange adjacent nonempty blocks in BOTH copies of a square. The
actual prefix and suffix are preserved. The two edges are e_back followed
by the reverse e_front with its block variables exchanged. -/
theorem adjacent_blocks (u v : Word Nat) (before after : List Nat) :
    Derives basis
      (Context.frame (contextWord before) (contextWord after) (u ++ v) ++
        Context.frame (contextWord before) (contextWord after) (u ++ v))
      (Context.frame (contextWord before) (contextWord after) (v ++ u) ++
        Context.frame (contextWord before) (contextWord after) (v ++ u)) := by
  let middleGap : Option (Word Nat) := contextWord (after ++ before)
  let first : Word Nat := gap (u ++ v) middleGap ++ (u ++ v)
  let middle : Word Nat := gap (u ++ v) middleGap ++ (v ++ u)
  let last : Word Nat := gap (v ++ u) middleGap ++ (v ++ u)
  have edge1 : Derives basis first middle := by
    simpa only [first, middle, gap, Word.append_assoc] using
      e_back u v none middleGap
  have edge2 : Derives basis middle last := by
    simpa only [middle, last, gap, Word.append_assoc] using
      (e_front v u none middleGap).symm
  have source :
      (Context.frame (contextWord before) (contextWord after) (u ++ v) ++
        Context.frame (contextWord before) (contextWord after) (u ++ v)) =
      Context.frame (contextWord before) (contextWord after) first := by
    apply Word.toList_injective
    simp only [first, middleGap, frame_of_lists_toList, Word.toList_append,
      gap_context_toList, List.append_assoc]
  have target :
      (Context.frame (contextWord before) (contextWord after) (v ++ u) ++
        Context.frame (contextWord before) (contextWord after) (v ++ u)) =
      Context.frame (contextWord before) (contextWord after) last := by
    apply Word.toList_injective
    simp only [last, middleGap, frame_of_lists_toList, Word.toList_append,
      gap_context_toList, List.append_assoc]
  rw [source, target]
  exact Context.frame_derives (edge1.trans edge2) (contextWord before) (contextWord after)

private theorem word_length_positive (word : Word Nat) : 0 < word.toList.length := by
  cases word
  simp [Word.toList]

/-- Permutation induction retains typed nonempty words at every boundary.
Empty lists are only contexts, never substitution images or adjoined units. -/
theorem permutation_in_context {xs ys : List Nat} (permutation : xs.Perm ys)
    (before after : List Nat) (left right : Word Nat)
    (leftSplit : left.toList = before ++ xs ++ after)
    (rightSplit : right.toList = before ++ ys ++ after) :
    Derives basis (left ++ left) (right ++ right) := by
  induction permutation generalizing before after left right with
  | nil =>
      have equal : left = right := Word.toList_injective (leftSplit.trans rightSplit.symm)
      rw [equal]
      exact Derives.refl _
  | cons letter permutation ih =>
      apply ih (before ++ [letter]) after left right
      · simpa only [List.append_assoc, List.cons_append, List.nil_append] using leftSplit
      · simpa only [List.append_assoc, List.cons_append, List.nil_append] using rightSplit
  | swap x y tail =>
      have leftFrame : left = Context.frame (contextWord before)
          (contextWord (tail ++ after)) (Word.singleton y ++ Word.singleton x) := by
        apply word_frame_of_split
        simpa only [Word.toList_append, Word.singleton, Word.toList,
          List.append_assoc, List.cons_append, List.nil_append] using leftSplit
      have rightFrame : right = Context.frame (contextWord before)
          (contextWord (tail ++ after)) (Word.singleton x ++ Word.singleton y) := by
        apply word_frame_of_split
        simpa only [Word.toList_append, Word.singleton, Word.toList,
          List.append_assoc, List.cons_append, List.nil_append] using rightSplit
      rw [leftFrame, rightFrame]
      exact adjacent_blocks (Word.singleton y) (Word.singleton x) before (tail ++ after)
  | @trans xs ys zs first second ihFirst ihSecond =>
      cases middleSplit : before ++ ys ++ after with
      | nil =>
          have middleLength := congrArg List.length middleSplit
          have leftLength := congrArg List.length leftSplit
          have sameLength := first.length_eq
          have positive := word_length_positive left
          simp only [List.length_append, List.length_nil] at middleLength leftLength
          omega
      | cons head tail =>
          let middle : Word Nat := Word.mk head tail
          have actualMiddle : middle.toList = before ++ ys ++ after := by
            simpa only [middle, Word.toList] using middleSplit.symm
          exact (ihFirst before after left middle leftSplit actualMiddle).trans
            (ihSecond before after middle right actualMiddle rightSplit)

/-- Arbitrarily many adjacent exchanges; no alphabet or length restriction. -/
theorem square_of_perm (left right : Word Nat) (permutation : left.toList.Perm right.toList) :
    Derives basis (left ++ left) (right ++ right) := by
  exact permutation_in_context permutation [] [] left right (by simp) (by simp)

private def fromNonempty (letters : List Nat) (nonempty : letters ≠ []) : Word Nat :=
  match letters with
  | [] => False.elim (nonempty rfl)
  | first :: rest => Word.mk first rest

private theorem fromNonempty_toList (letters : List Nat) (nonempty : letters ≠ []) :
    (fromNonempty letters nonempty).toList = letters := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest => rfl

def letterLE (x y : Nat) : Bool := decide (x ≤ y)

private theorem sorted_nonempty (word : Word Nat) : word.toList.mergeSort letterLE ≠ [] := by
  intro empty
  have sameLength := (List.mergeSort_perm word.toList letterLE).length_eq
  rw [empty] at sameLength
  have positive := word_length_positive word
  simp only [List.length_nil] at sameLength
  omega

/-- Sort the actual root multiset. Repetitions are NOT silently deleted. -/
def sortedRoot (word : Word Nat) : Word Nat :=
  fromNonempty (word.toList.mergeSort letterLE) (sorted_nonempty word)

theorem sortedRoot_toList (word : Word Nat) :
    (sortedRoot word).toList = word.toList.mergeSort letterLE :=
  fromNonempty_toList _ _

theorem sortedRoot_perm (word : Word Nat) : word.toList.Perm (sortedRoot word).toList := by
  rw [sortedRoot_toList]
  exact (List.mergeSort_perm word.toList letterLE).symm

theorem sortedRoot_ordered (word : Word Nat) : (sortedRoot word).toList.Pairwise (· ≤ ·) := by
  have transitive : ∀ a b c : Nat, letterLE a b → letterLE b c → letterLE a c := by
    intro a b c
    simp only [letterLE, decide_eq_true_eq]
    exact Nat.le_trans
  have total : ∀ a b : Nat, letterLE a b || letterLE b a := by
    intro a b
    simp only [letterLE, Bool.or_eq_true, decide_eq_true_eq]
    omega
  rw [sortedRoot_toList]
  simpa only [letterLE, decide_eq_true_eq] using
    List.pairwise_mergeSort transitive total word.toList

theorem sortedRoot_nodup (word : Word Nat) (distinct : word.toList.Nodup) :
    (sortedRoot word).toList.Nodup :=
  (sortedRoot_perm word).nodup distinct

theorem square_sorted (word : Word Nat) :
    Derives basis (word ++ word) (sortedRoot word ++ sortedRoot word) :=
  square_of_perm word (sortedRoot word) (sortedRoot_perm word)

/-- Disjoint duplicate-free roots really give the perfect square's sorted
union root, with the exact union support. This is not an assumed renderer. -/
theorem sorted_union_perfect (u v : Word Nat)
    (uDistinct : u.toList.Nodup) (vDistinct : v.toList.Nodup)
    (apart : ∀ a ∈ u.toList, ∀ b ∈ v.toList, a ≠ b) :
    (sortedRoot (u ++ v)).toList.Nodup ∧
      (sortedRoot (u ++ v)).toList.Pairwise (· ≤ ·) ∧
      ∀ letter, letter ∈ (sortedRoot (u ++ v)).toList ↔
        letter ∈ u.toList ∨ letter ∈ v.toList := by
  have rootsDistinct : (u ++ v).toList.Nodup := by
    rw [Word.toList_append]
    exact List.nodup_append.mpr ⟨uDistinct, vDistinct, apart⟩
  refine ⟨sortedRoot_nodup (u ++ v) rootsDistinct, sortedRoot_ordered (u ++ v), ?_⟩
  intro letter
  have members := (sortedRoot_perm (u ++ v)).symm.mem_iff (a := letter)
  simpa only [Word.toList_append, List.mem_append] using members

/-- The missing sorting half of generalized block fusion. Existing doubled
roots fuse first, then the actual combined root is sorted by permutation. -/
theorem fused_square_sorted (u v : Word Nat) :
    Derives basis (square (u ++ u) (v ++ v))
      (sortedRoot (u ++ v) ++ sortedRoot (u ++ v)) :=
  (square_fusion u v).trans (square_sorted (u ++ v))

theorem fused_sorted_framed_chain (u v : Word Nat) (gaps : List (List Nat))
    (before after : List Nat) :
    Derives basis
      (Context.frame (contextWord before) (contextWord after)
        (SquareCoalescing.chain (square (u ++ u) (v ++ v)) gaps))
      (Context.frame (contextWord before) (contextWord after)
        (SquareCoalescing.chain (sortedRoot (u ++ v) ++ sortedRoot (u ++ v)) gaps)) :=
  framed_chain_derives (fused_square_sorted u v) gaps before after

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquarePermutation

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquarePermutation.adjacent_blocks
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquarePermutation.permutation_in_context
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquarePermutation.square_of_perm
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquarePermutation.sortedRoot_toList
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquarePermutation.sortedRoot_perm
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquarePermutation.sortedRoot_ordered
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquarePermutation.sortedRoot_nodup
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquarePermutation.square_sorted
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquarePermutation.sorted_union_perfect
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquarePermutation.fused_square_sorted
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquarePermutation.fused_sorted_framed_chain
