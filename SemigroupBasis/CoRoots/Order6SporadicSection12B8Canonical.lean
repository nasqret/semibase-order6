import SemigroupBasis.CoRoots.Order6SporadicSection12B8Normalization
import SemigroupBasis.CoRoots.S5_107MarkerCombinatorics

namespace SemigroupBasis.CoRoots.Order6SporadicSection12

open SemigroupBasis
open SemigroupBasis.CoRoots
open SemigroupBasis.Examples

namespace B8Canonical

def sortedSimpleLetters (letters : List Nat) : List Nat :=
  (connectedComponentSortedSupport letters).filter
    (fun letter => decide (letters.count letter = 1))

def renderRepeatedBlocks
    (letters labels : List Nat) : List Nat :=
  labels.flatMap fun letter =>
    List.replicate
      (B8Normalization.capThree (letters.count letter)) letter

/-- The deterministic form from Section 12.2. The first multiple letter is
the least one; its prefix multiplicity is capped at two and one final copy is
retained. -/
def canonicalList (letters : List Nat) : List Nat :=
  match S5_107.sortedMultipleLetters letters with
  | [] => []
  | owner :: others =>
      List.replicate
          (B8Normalization.capTwo (letters.count owner - 1)) owner ++
        renderRepeatedBlocks letters others ++
        sortedSimpleLetters letters ++ [owner]

/-- Intrinsic canonicality. The explicit count bound is retained in the
predicate because it is exactly what turns `N_3^1` capped-count semantics into
literal count equality. -/
structure Canonical (word : Word Nat) : Prop where
  fixed : canonicalList word.toList = word.toList
  count_le_three : ∀ letter, word.toList.count letter ≤ 3

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

private theorem sortedMultipleLetters_eq_of_count_eq
    {left right : List Nat}
    (countEq : ∀ letter, left.count letter = right.count letter) :
    S5_107.sortedMultipleLetters left =
      S5_107.sortedMultipleLetters right := by
  apply sortedNodup_eq_of_mem_iff
    (S5_107.sortedMultipleLetters_pairwise left)
    (S5_107.sortedMultipleLetters_pairwise right)
    (S5_107.sortedMultipleLetters_nodup left)
    (S5_107.sortedMultipleLetters_nodup right)
  intro letter
  rw [S5_107.sortedMultipleLetters_mem_iff,
    S5_107.sortedMultipleLetters_mem_iff, countEq letter]

private theorem sortedSupport_eq_of_count_eq
    {left right : List Nat}
    (countEq : ∀ letter, left.count letter = right.count letter) :
    connectedComponentSortedSupport left =
      connectedComponentSortedSupport right := by
  apply sortedNodup_eq_of_mem_iff
    (connectedComponentSortedSupport_sorted left)
    (connectedComponentSortedSupport_sorted right)
    (connectedComponentSortedSupport_nodup left)
    (connectedComponentSortedSupport_nodup right)
  intro letter
  rw [connectedComponentSortedSupport_mem_iff,
    connectedComponentSortedSupport_mem_iff]
  constructor
  · intro member
    apply List.count_pos_iff.mp
    rw [← countEq letter]
    exact List.count_pos_iff.mpr member
  · intro member
    apply List.count_pos_iff.mp
    rw [countEq letter]
    exact List.count_pos_iff.mpr member

private theorem sortedSimpleLetters_eq_of_count_eq
    {left right : List Nat}
    (countEq : ∀ letter, left.count letter = right.count letter) :
    sortedSimpleLetters left = sortedSimpleLetters right := by
  unfold sortedSimpleLetters
  rw [sortedSupport_eq_of_count_eq countEq]
  apply List.filter_congr
  intro letter _
  simp [countEq letter]

private theorem renderRepeatedBlocks_eq_of_count_eq
    {left right : List Nat}
    (countEq : ∀ letter, left.count letter = right.count letter) :
    ∀ labels,
      renderRepeatedBlocks left labels =
        renderRepeatedBlocks right labels
  | [] => rfl
  | label :: labels => by
      change
        List.replicate
              (B8Normalization.capThree (left.count label)) label ++
            renderRepeatedBlocks left labels =
          List.replicate
              (B8Normalization.capThree (right.count label)) label ++
            renderRepeatedBlocks right labels
      rw [countEq label,
        renderRepeatedBlocks_eq_of_count_eq countEq labels]

theorem capThree_eq_min (count : Nat) :
    B8Normalization.capThree count = min count 3 := by
  unfold B8Normalization.capThree
  by_cases small : count < 3
  · rw [if_pos small, Nat.min_eq_left (by omega)]
  · rw [if_neg small, Nat.min_eq_right (by omega)]

private theorem capTwo_sub_one_eq (count : Nat) :
    B8Normalization.capTwo (count - 1) = min count 3 - 1 := by
  unfold B8Normalization.capTwo
  by_cases small : count < 3
  · rw [Nat.min_eq_left (by omega)]
    split <;> omega
  · rw [Nat.min_eq_right (by omega)]
    split <;> omega

private theorem sortedMultipleLetters_eq_of_capped_count_eq
    {left right : List Nat}
    (countEq :
      ∀ letter, min (left.count letter) 3 = min (right.count letter) 3) :
    S5_107.sortedMultipleLetters left =
      S5_107.sortedMultipleLetters right := by
  apply sortedNodup_eq_of_mem_iff
    (S5_107.sortedMultipleLetters_pairwise left)
    (S5_107.sortedMultipleLetters_pairwise right)
    (S5_107.sortedMultipleLetters_nodup left)
    (S5_107.sortedMultipleLetters_nodup right)
  intro letter
  rw [S5_107.sortedMultipleLetters_mem_iff,
    S5_107.sortedMultipleLetters_mem_iff]
  have capped := countEq letter
  omega

private theorem sortedSupport_eq_of_capped_count_eq
    {left right : List Nat}
    (countEq :
      ∀ letter, min (left.count letter) 3 = min (right.count letter) 3) :
    connectedComponentSortedSupport left =
      connectedComponentSortedSupport right := by
  apply sortedNodup_eq_of_mem_iff
    (connectedComponentSortedSupport_sorted left)
    (connectedComponentSortedSupport_sorted right)
    (connectedComponentSortedSupport_nodup left)
    (connectedComponentSortedSupport_nodup right)
  intro letter
  rw [connectedComponentSortedSupport_mem_iff,
    connectedComponentSortedSupport_mem_iff,
    ← List.count_pos_iff, ← List.count_pos_iff]
  have capped := countEq letter
  omega

private theorem sortedSimpleLetters_eq_of_capped_count_eq
    {left right : List Nat}
    (countEq :
      ∀ letter, min (left.count letter) 3 = min (right.count letter) 3) :
    sortedSimpleLetters left = sortedSimpleLetters right := by
  unfold sortedSimpleLetters
  rw [sortedSupport_eq_of_capped_count_eq countEq]
  apply List.filter_congr
  intro letter _
  have capped := countEq letter
  have oneIff : left.count letter = 1 ↔ right.count letter = 1 := by
    omega
  simpa only [oneIff]

private theorem renderRepeatedBlocks_eq_of_capped_count_eq
    {left right : List Nat}
    (countEq :
      ∀ letter, min (left.count letter) 3 = min (right.count letter) 3) :
    ∀ labels,
      renderRepeatedBlocks left labels =
        renderRepeatedBlocks right labels
  | [] => rfl
  | label :: labels => by
      have exponentEq :
          B8Normalization.capThree (left.count label) =
            B8Normalization.capThree (right.count label) := by
        rw [capThree_eq_min, capThree_eq_min, countEq label]
      change
        List.replicate
              (B8Normalization.capThree (left.count label)) label ++
            renderRepeatedBlocks left labels =
          List.replicate
              (B8Normalization.capThree (right.count label)) label ++
            renderRepeatedBlocks right labels
      rw [exponentEq,
        renderRepeatedBlocks_eq_of_capped_count_eq countEq labels]

/-- The B8 renderer depends only on counts capped at three. -/
theorem canonicalList_eq_of_capped_count_eq
    {left right : List Nat}
    (countEq :
      ∀ letter, min (left.count letter) 3 = min (right.count letter) 3) :
    canonicalList left = canonicalList right := by
  have multipleEq := sortedMultipleLetters_eq_of_capped_count_eq countEq
  have simpleEq := sortedSimpleLetters_eq_of_capped_count_eq countEq
  unfold canonicalList
  rw [multipleEq]
  cases multipleShape : S5_107.sortedMultipleLetters right with
  | nil => rfl
  | cons owner others =>
      have ownerExponentEq :
          B8Normalization.capTwo (left.count owner - 1) =
            B8Normalization.capTwo (right.count owner - 1) := by
        rw [capTwo_sub_one_eq, capTwo_sub_one_eq, countEq owner]
      change
        List.replicate
              (B8Normalization.capTwo (left.count owner - 1)) owner ++
            renderRepeatedBlocks left others ++
            sortedSimpleLetters left ++ [owner] =
          List.replicate
              (B8Normalization.capTwo (right.count owner - 1)) owner ++
            renderRepeatedBlocks right others ++
            sortedSimpleLetters right ++ [owner]
      rw [ownerExponentEq,
        renderRepeatedBlocks_eq_of_capped_count_eq countEq others,
        simpleEq]

theorem canonicalList_eq_of_count_eq
    {left right : List Nat}
    (countEq : ∀ letter, left.count letter = right.count letter) :
    canonicalList left = canonicalList right := by
  have multipleEq := sortedMultipleLetters_eq_of_count_eq countEq
  have simpleEq := sortedSimpleLetters_eq_of_count_eq countEq
  unfold canonicalList
  rw [multipleEq]
  cases multipleShape : S5_107.sortedMultipleLetters right with
  | nil => rfl
  | cons owner others =>
      change
        List.replicate
              (B8Normalization.capTwo (left.count owner - 1)) owner ++
            renderRepeatedBlocks left others ++
            sortedSimpleLetters left ++ [owner] =
          List.replicate
              (B8Normalization.capTwo (right.count owner - 1)) owner ++
            renderRepeatedBlocks right others ++
            sortedSimpleLetters right ++ [owner]
      rw [countEq owner,
        renderRepeatedBlocks_eq_of_count_eq countEq others,
        simpleEq]

private theorem count_replicate_of_ne
    {tested label : Nat} (different : tested ≠ label) :
    ∀ count, (List.replicate count label).count tested = 0
  | 0 => rfl
  | count + 1 => by
      rw [List.replicate_succ,
        List.count_cons_of_ne (Ne.symm different),
        count_replicate_of_ne different count]

theorem sortedSimpleLetters_nodup (letters : List Nat) :
    (sortedSimpleLetters letters).Nodup := by
  exact (connectedComponentSortedSupport_nodup letters).filter _

theorem sortedSimpleLetters_mem_iff (letter : Nat) (letters : List Nat) :
    letter ∈ sortedSimpleLetters letters ↔ letters.count letter = 1 := by
  unfold sortedSimpleLetters
  simp only [List.mem_filter, decide_eq_true_eq,
    connectedComponentSortedSupport_mem_iff]
  constructor
  · intro member
    exact member.2
  · intro count
    exact ⟨List.count_pos_iff.mp (by omega), count⟩

private theorem sortedSimpleLetters_count
    (tested : Nat) (letters : List Nat) :
    (sortedSimpleLetters letters).count tested =
      if letters.count tested = 1 then 1 else 0 := by
  rw [(sortedSimpleLetters_nodup letters).count]
  by_cases simple : letters.count tested = 1
  · have member := (sortedSimpleLetters_mem_iff tested letters).2 simple
    rw [if_pos simple, if_pos member]
  · have absent : tested ∉ sortedSimpleLetters letters := by
      intro member
      exact simple ((sortedSimpleLetters_mem_iff tested letters).1 member)
    rw [if_neg simple, if_neg absent]

private theorem renderRepeatedBlocks_count
    (letters labels : List Nat) (tested : Nat)
    (nodup : labels.Nodup) :
    (renderRepeatedBlocks letters labels).count tested =
      if tested ∈ labels then
        B8Normalization.capThree (letters.count tested)
      else 0 := by
  induction labels with
  | nil => simp [renderRepeatedBlocks]
  | cons label labels ih =>
      have labelAbsent := (List.nodup_cons.mp nodup).1
      have labelsNodup := (List.nodup_cons.mp nodup).2
      change
        (List.replicate
              (B8Normalization.capThree (letters.count label)) label ++
            renderRepeatedBlocks letters labels).count tested =
          if tested ∈ label :: labels then
            B8Normalization.capThree (letters.count tested)
          else 0
      rw [List.count_append]
      by_cases same : tested = label
      · subst tested
        rw [List.count_replicate_self, ih labelsNodup]
        simp [labelAbsent]
      · rw [count_replicate_of_ne same, ih labelsNodup]
        simp [same]

/-- Exact multiplicity of every letter in the deterministic B8 renderer. -/
theorem canonicalList_count_of_multipleShape
    (letters : List Nat) {owner : Nat} {others : List Nat}
    (multipleShape :
      S5_107.sortedMultipleLetters letters = owner :: others)
    (tested : Nat) :
    (canonicalList letters).count tested = min (letters.count tested) 3 := by
  have allNodup : (owner :: others).Nodup := by
    simpa [multipleShape] using S5_107.sortedMultipleLetters_nodup letters
  have ownerAbsent : owner ∉ others := (List.nodup_cons.mp allNodup).1
  have othersNodup : others.Nodup := (List.nodup_cons.mp allNodup).2
  have ownerMultiple : 2 ≤ letters.count owner :=
    (S5_107.sortedMultipleLetters_mem_iff owner letters).1 <| by
      rw [multipleShape]
      simp
  have repeatedCount := renderRepeatedBlocks_count
    letters others tested othersNodup
  have simpleCount := sortedSimpleLetters_count tested letters
  unfold canonicalList
  rw [multipleShape]
  simp only [List.count_append]
  rw [repeatedCount, simpleCount]
  by_cases sameOwner : tested = owner
  · subst tested
    have notSimple : letters.count owner ≠ 1 := by omega
    rw [List.count_replicate_self, if_neg ownerAbsent,
      if_neg notSimple]
    simp only [List.count_cons_self, List.count_nil, Nat.add_zero]
    rw [capTwo_sub_one_eq]
    by_cases small : letters.count owner < 3
    · rw [Nat.min_eq_left (by omega)]
      omega
    · rw [Nat.min_eq_right (by omega)]
  · rw [count_replicate_of_ne sameOwner]
    have finalCount : [owner].count tested = 0 := by
      rw [List.count_cons_of_ne (Ne.symm sameOwner), List.count_nil]
    rw [finalCount]
    simp only [Nat.zero_add, Nat.add_zero]
    by_cases inOthers : tested ∈ others
    · have multiple : 2 ≤ letters.count tested :=
        (S5_107.sortedMultipleLetters_mem_iff tested letters).1 <| by
          rw [multipleShape]
          exact List.Mem.tail owner inOthers
      have notSimple : letters.count tested ≠ 1 := by omega
      rw [if_pos inOthers, if_neg notSimple, capThree_eq_min]
      simp
    · have notMultiple : ¬2 ≤ letters.count tested := by
        intro multiple
        have member :=
          (S5_107.sortedMultipleLetters_mem_iff tested letters).2 multiple
        rw [multipleShape] at member
        rcases List.mem_cons.mp member with equals | member
        · exact sameOwner equals
        · exact inOthers member
      rw [if_neg inOthers]
      by_cases simple : letters.count tested = 1
      · rw [if_pos simple, simple]
        simp
      · rw [if_neg simple]
        have absent : letters.count tested = 0 := by omega
        rw [absent]
        simp

theorem canonicalList_nonempty_of_multipleShape
    (letters : List Nat) {owner : Nat} {others : List Nat}
    (multipleShape :
      S5_107.sortedMultipleLetters letters = owner :: others) :
    canonicalList letters ≠ [] := by
  simp [canonicalList, multipleShape]

theorem canonicalList_count_le_three_of_multipleShape
    (letters : List Nat) {owner : Nat} {others : List Nat}
    (multipleShape :
      S5_107.sortedMultipleLetters letters = owner :: others)
    (tested : Nat) :
    (canonicalList letters).count tested ≤ 3 := by
  rw [canonicalList_count_of_multipleShape letters multipleShape tested]
  omega

theorem canonicalList_fixed_of_multipleShape
    (letters : List Nat) {owner : Nat} {others : List Nat}
    (multipleShape :
      S5_107.sortedMultipleLetters letters = owner :: others) :
    canonicalList (canonicalList letters) = canonicalList letters := by
  apply canonicalList_eq_of_capped_count_eq
  intro tested
  rw [canonicalList_count_of_multipleShape letters multipleShape tested]
  rw [Nat.min_eq_left (Nat.min_le_right _ _)]

theorem canonical_eq_of_valid
    {left right : Word Nat}
    (leftCanonical : Canonical left)
    (rightCanonical : Canonical right)
    (valid :
      (Identity.mk left right).SatisfiedBy S6_5626.table.semigroup) :
    left = right := by
  have n31Valid :=
    S6_5626.valid_n_3_1 (Identity.mk left right) valid
  have cappedEq :
      ∀ letter,
        min (left.toList.count letter) 3 =
          min (right.toList.count letter) 3 := by
    simpa [Generated.S4_40.table] using
      exponentFourValid_capped_count_eq (Identity.mk left right) n31Valid
  have countEq :
      ∀ letter, left.toList.count letter = right.toList.count letter := by
    intro letter
    have leftBound := leftCanonical.count_le_three letter
    have rightBound := rightCanonical.count_le_three letter
    simpa [Nat.min_eq_left leftBound, Nat.min_eq_left rightBound] using
      cappedEq letter
  have canonicalEq := canonicalList_eq_of_count_eq countEq
  apply Word.toList_injective
  exact leftCanonical.fixed.symm.trans <|
    canonicalEq.trans rightCanonical.fixed

end B8Canonical

end SemigroupBasis.CoRoots.Order6SporadicSection12
