import SemigroupBasis.CoRoots.Order6SporadicSection12B8Canonical

namespace SemigroupBasis.CoRoots.Order6SporadicSection12

open SemigroupBasis
open SemigroupBasis.CoRoots

namespace B8Assembly

private abbrev ListDerives :=
  S5_107.ListDerives b8Basis

/-- The uncapped repeated blocks used before applying (12.3a). -/
def renderFullBlocks (letters labels : List Nat) : List Nat :=
  labels.flatMap fun letter =>
    List.replicate (letters.count letter) letter

/-- The interior of the multiplicity-preserving owner envelope. -/
def expandedInterior
    (letters : List Nat) (owner : Nat) (others : List Nat) : List Nat :=
  List.replicate (letters.count owner - 2) owner ++
    renderFullBlocks letters others ++
    B8Canonical.sortedSimpleLetters letters

/-- A permutation of the source in which the least multiple letter is at both
ends and every remaining label occurs in one contiguous block. -/
def expandedCanonicalList (letters : List Nat) : List Nat :=
  match S5_107.sortedMultipleLetters letters with
  | [] => []
  | owner :: others =>
      owner :: expandedInterior letters owner others ++ [owner]

private theorem count_replicate_of_ne
    {tested label : Nat} (different : tested ≠ label) :
    ∀ count, (List.replicate count label).count tested = 0
  | 0 => rfl
  | count + 1 => by
      rw [List.replicate_succ,
        List.count_cons_of_ne (Ne.symm different),
        count_replicate_of_ne different count]

private theorem renderFullBlocks_count
    (letters labels : List Nat) (tested : Nat)
    (nodup : labels.Nodup) :
    (renderFullBlocks letters labels).count tested =
      if tested ∈ labels then letters.count tested else 0 := by
  induction labels with
  | nil => simp [renderFullBlocks]
  | cons label labels ih =>
      have labelAbsent := (List.nodup_cons.mp nodup).1
      have labelsNodup := (List.nodup_cons.mp nodup).2
      change
        (List.replicate (letters.count label) label ++
            renderFullBlocks letters labels).count tested =
          if tested ∈ label :: labels then letters.count tested else 0
      rw [List.count_append]
      by_cases same : tested = label
      · subst tested
        rw [List.count_replicate_self, ih labelsNodup]
        simp [labelAbsent]
      · rw [count_replicate_of_ne same, ih labelsNodup]
        simp [same]

private theorem sortedSimpleLetters_count
    (tested : Nat) (letters : List Nat) :
    (B8Canonical.sortedSimpleLetters letters).count tested =
      if letters.count tested = 1 then 1 else 0 := by
  rw [(B8Canonical.sortedSimpleLetters_nodup letters).count]
  by_cases simple : letters.count tested = 1
  · have member :=
      (B8Canonical.sortedSimpleLetters_mem_iff tested letters).2 simple
    rw [if_pos simple, if_pos member]
  · have absent : tested ∉ B8Canonical.sortedSimpleLetters letters := by
      intro member
      exact simple <|
        (B8Canonical.sortedSimpleLetters_mem_iff tested letters).1 member
    rw [if_neg simple, if_neg absent]

theorem expandedCanonicalList_count_of_multipleShape
    (letters : List Nat) {owner : Nat} {others : List Nat}
    (multipleShape :
      S5_107.sortedMultipleLetters letters = owner :: others)
    (tested : Nat) :
    (expandedCanonicalList letters).count tested = letters.count tested := by
  have allNodup : (owner :: others).Nodup := by
    simpa [multipleShape] using S5_107.sortedMultipleLetters_nodup letters
  have ownerAbsent : owner ∉ others := (List.nodup_cons.mp allNodup).1
  have othersNodup : others.Nodup := (List.nodup_cons.mp allNodup).2
  have ownerMultiple : 2 ≤ letters.count owner :=
    (S5_107.sortedMultipleLetters_mem_iff owner letters).1 <| by
      rw [multipleShape]
      simp
  have fullCount := renderFullBlocks_count
    letters others tested othersNodup
  have simpleCount := sortedSimpleLetters_count tested letters
  unfold expandedCanonicalList
  rw [multipleShape]
  simp only [List.count_append]
  by_cases sameOwner : tested = owner
  · subst tested
    rw [List.count_cons_self]
    unfold expandedInterior
    simp only [List.count_append]
    rw [fullCount, simpleCount]
    have notSimple : letters.count owner ≠ 1 := by omega
    rw [List.count_replicate_self, if_neg ownerAbsent,
      if_neg notSimple]
    simp only [List.count_cons_self, List.count_nil, Nat.add_zero]
    omega
  · rw [List.count_cons_of_ne (Ne.symm sameOwner)]
    unfold expandedInterior
    simp only [List.count_append]
    rw [fullCount, simpleCount, count_replicate_of_ne sameOwner]
    have finalCount : [owner].count tested = 0 := by
      simp [Ne.symm sameOwner]
    rw [finalCount]
    simp only [Nat.zero_add, Nat.add_zero]
    by_cases inOthers : tested ∈ others
    · have multiple : 2 ≤ letters.count tested :=
        (S5_107.sortedMultipleLetters_mem_iff tested letters).1 <| by
          rw [multipleShape]
          exact List.Mem.tail owner inOthers
      have notSimple : letters.count tested ≠ 1 := by omega
      rw [if_pos inOthers, if_neg notSimple]
      exact Nat.add_zero _
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
      · rw [if_neg simple]
        have absent : letters.count tested = 0 := by omega
        rw [absent]

theorem expandedCanonicalList_perm
    (letters : List Nat) {owner : Nat} {others : List Nat}
    (multipleShape :
      S5_107.sortedMultipleLetters letters = owner :: others) :
    letters.Perm (expandedCanonicalList letters) := by
  rw [List.perm_iff_count]
  intro tested
  exact (expandedCanonicalList_count_of_multipleShape
    letters multipleShape tested).symm

private theorem interior_perm_of_closed_envelope_perm
    (endpoint : Nat) {left right : List Nat}
    (permutation :
      (endpoint :: left ++ [endpoint]).Perm
        (endpoint :: right ++ [endpoint])) :
    left.Perm right := by
  rw [List.perm_iff_count]
  intro tested
  have counts := (List.perm_iff_count.mp permutation) tested
  simp only [List.count_cons, List.count_append, List.count_nil] at counts
  omega

/-- Retarget the matching endpoint produced by the connected-word scan to the
least multiple letter, preserving every multiplicity. -/
theorem listDerivesRetargetOwner
    (word : Word Nat) (connected : Connected word)
    {owner : Nat} {others : List Nat}
    (multipleShape :
      S5_107.sortedMultipleLetters word.toList = owner :: others) :
    ∃ interior,
      ListDerives word.toList (owner :: interior ++ [owner]) ∧
      word.toList.Perm (owner :: interior ++ [owner]) := by
  rcases B8Normalization.listDerivesConnectedToMatchingEndpointsWithPermutation
      word connected with
    ⟨initialInterior, initialDerivation, initialPermutation⟩
  by_cases sameEndpoint : word.head = owner
  · subst owner
    exact ⟨initialInterior, initialDerivation, initialPermutation⟩
  · have ownerMultiple : 2 ≤ word.toList.count owner :=
      (S5_107.sortedMultipleLetters_mem_iff owner word.toList).1 <| by
        rw [multipleShape]
        simp
    have targetCount :
        (word.head :: initialInterior ++ [word.head]).count owner =
          initialInterior.count owner := by
      simp [sameEndpoint]
    have countEquality :=
      (List.perm_iff_count.mp initialPermutation) owner
    rw [targetCount] at countEquality
    have repeated : 2 ≤ initialInterior.count owner := by omega
    let remainder :=
      (initialInterior.erase owner).erase owner
    let targetInterior := word.head :: remainder ++ [word.head]
    have switched := B8Normalization.listDerivesEndpointSwitch
      word.head owner initialInterior sameEndpoint repeated
    have switchedPermutation := B8Normalization.listDerivesEndpointSwitch_perm
      word.head owner initialInterior sameEndpoint repeated
    refine ⟨targetInterior, initialDerivation.trans ?_,
      initialPermutation.trans ?_⟩
    · simpa [targetInterior, remainder, List.append_assoc] using switched
    · simpa [targetInterior, remainder, List.append_assoc] using
        switchedPermutation

/-- Cap each full non-owner block independently while preserving its context. -/
theorem listDerivesCapFullBlocks
    (letters : List Nat) :
    ∀ (labels pre suffix : List Nat),
      ListDerives
        (pre ++ renderFullBlocks letters labels ++ suffix)
        (pre ++ B8Canonical.renderRepeatedBlocks letters labels ++ suffix)
  | [], pre, suffix => by
      simpa [renderFullBlocks, B8Canonical.renderRepeatedBlocks] using
        (S5_107.ListDerives.refl (basis := b8Basis) (pre ++ suffix))
  | label :: labels, pre, suffix => by
      have first := B8Normalization.listDerivesCapRunThree
        pre (renderFullBlocks letters labels ++ suffix)
        label (letters.count label)
      have recurse := listDerivesCapFullBlocks letters labels
        (pre ++ List.replicate
          (B8Normalization.capThree (letters.count label)) label)
        suffix
      simpa [renderFullBlocks, B8Canonical.renderRepeatedBlocks,
          List.append_assoc] using
        first.trans (by
          simpa [renderFullBlocks, B8Canonical.renderRepeatedBlocks,
            List.append_assoc] using recurse)

theorem listDerivesExpandedToCanonical
    (letters : List Nat) {owner : Nat} {others : List Nat}
    (multipleShape :
      S5_107.sortedMultipleLetters letters = owner :: others) :
    ListDerives
      (expandedCanonicalList letters)
      (B8Canonical.canonicalList letters) := by
  have ownerMultiple : 2 ≤ letters.count owner :=
    (S5_107.sortedMultipleLetters_mem_iff owner letters).1 <| by
      rw [multipleShape]
      simp
  have prefixShape :
      owner :: List.replicate (letters.count owner - 2) owner =
        List.replicate (letters.count owner - 1) owner := by
    have arithmetic :
        letters.count owner - 1 = (letters.count owner - 2) + 1 := by
      omega
    rw [arithmetic, List.replicate_succ]
  have expandedShape :
      expandedCanonicalList letters =
        List.replicate (letters.count owner - 1) owner ++
          renderFullBlocks letters others ++
          B8Canonical.sortedSimpleLetters letters ++ [owner] := by
    have prefixed := congrArg
      (fun stem =>
        stem ++ renderFullBlocks letters others ++
          B8Canonical.sortedSimpleLetters letters ++ [owner])
      prefixShape
    simpa [expandedCanonicalList, expandedInterior, multipleShape,
      List.append_assoc] using prefixed
  have capOwner := B8Normalization.listDerivesCapEndpointPrefix
    (renderFullBlocks letters others ++
      B8Canonical.sortedSimpleLetters letters)
    owner (letters.count owner - 1)
  have capOthers := listDerivesCapFullBlocks letters others
    (List.replicate
      (B8Normalization.capTwo (letters.count owner - 1)) owner)
    (B8Canonical.sortedSimpleLetters letters ++ [owner])
  rw [expandedShape]
  simpa [B8Canonical.canonicalList, multipleShape,
      List.append_assoc] using
    capOwner.trans (by
      simpa [List.append_assoc] using capOthers)

/-- Every connected word reaches the exact deterministic B8 renderer. -/
theorem listDerivesCanonical
    (word : Word Nat) (connected : Connected word) :
    ListDerives word.toList
      (B8Canonical.canonicalList word.toList) := by
  rcases B8Normalization.listDerivesConnectedToMatchingEndpointsWithPermutation
      word connected with
    ⟨initialInterior, _, initialPermutation⟩
  have headMultiple : 2 ≤ word.toList.count word.head := by
    have countEquality :=
      (List.perm_iff_count.mp initialPermutation) word.head
    have targetCount :
        2 ≤ (word.head :: initialInterior ++ [word.head]).count word.head := by
      simp
    omega
  have multipleNonempty :
      S5_107.sortedMultipleLetters word.toList ≠ [] := by
    intro empty
    have member :=
      (S5_107.sortedMultipleLetters_mem_iff word.head word.toList).2
        headMultiple
    rw [empty] at member
    simp at member
  cases multipleShape : S5_107.sortedMultipleLetters word.toList with
  | nil => exact False.elim (multipleNonempty multipleShape)
  | cons owner others =>
      rcases listDerivesRetargetOwner word connected multipleShape with
        ⟨interior, envelopeDerivation, envelopePermutation⟩
      have expandedPermutation :=
        expandedCanonicalList_perm word.toList multipleShape
      have closedPermutation :
          (owner :: interior ++ [owner]).Perm
            (owner :: expandedInterior word.toList owner others ++ [owner]) := by
        simpa [expandedCanonicalList, multipleShape] using
          envelopePermutation.symm.trans expandedPermutation
      have interiorPermutation :=
        interior_perm_of_closed_envelope_perm owner closedPermutation
      have grouped := B8Normalization.listDerivesInteriorPermutation
        [] [] owner [] interiorPermutation
      have toExpanded :
          ListDerives word.toList (expandedCanonicalList word.toList) :=
        envelopeDerivation.trans <| by
          simpa [expandedCanonicalList, multipleShape,
            List.append_assoc] using grouped
      exact toExpanded.trans <|
        listDerivesExpandedToCanonical word.toList multipleShape

private def wordOfListOr
    (fallback : Nat) : List Nat → Word Nat
  | [] => Word.singleton fallback
  | head :: tail => ⟨head, tail⟩

def canonicalWord (word : Word Nat) : Word Nat :=
  wordOfListOr word.head (B8Canonical.canonicalList word.toList)

private theorem multipleLetters_nonempty
    (word : Word Nat) (connected : Connected word) :
    S5_107.sortedMultipleLetters word.toList ≠ [] := by
  rcases B8Normalization.listDerivesConnectedToMatchingEndpointsWithPermutation
      word connected with
    ⟨interior, _, permutation⟩
  have countEquality := (List.perm_iff_count.mp permutation) word.head
  have multiple : 2 ≤ word.toList.count word.head := by
    have targetCount :
        2 ≤ (word.head :: interior ++ [word.head]).count word.head := by
      simp
    omega
  intro empty
  have member :=
    (S5_107.sortedMultipleLetters_mem_iff word.head word.toList).2 multiple
  rw [empty] at member
  simp at member

theorem canonicalWord_toList
    (word : Word Nat) (connected : Connected word) :
    (canonicalWord word).toList =
      B8Canonical.canonicalList word.toList := by
  have nonempty := multipleLetters_nonempty word connected
  cases multipleShape : S5_107.sortedMultipleLetters word.toList with
  | nil => exact False.elim (nonempty multipleShape)
  | cons owner others =>
      have targetNonempty :=
        B8Canonical.canonicalList_nonempty_of_multipleShape
          word.toList multipleShape
      unfold canonicalWord
      cases targetShape : B8Canonical.canonicalList word.toList with
      | nil => exact False.elim (targetNonempty targetShape)
      | cons head tail => rfl

theorem derivesCanonical
    (word : Word Nat) (connected : Connected word) :
    Derives b8Basis word (canonicalWord word) := by
  have listDerivation := listDerivesCanonical word connected
  cases word with
  | mk head tail =>
      obtain ⟨targetHead, targetTail, targetListEq, wordDerivation⟩ :=
        S5_107.ListDerives.from_cons listDerivation
      have targetWordEq :
          S5_107.listWordOfCons targetHead targetTail =
            canonicalWord (Word.mk head tail) := by
        apply Word.toList_injective
        unfold canonicalWord
        rw [targetListEq]
        rfl
      rw [targetWordEq] at wordDerivation
      simpa [S5_107.listWordOfCons] using wordDerivation

theorem canonicalWord_canonical
    (word : Word Nat) (connected : Connected word) :
    B8Canonical.Canonical (canonicalWord word) := by
  have nonempty := multipleLetters_nonempty word connected
  cases multipleShape : S5_107.sortedMultipleLetters word.toList with
  | nil => exact False.elim (nonempty multipleShape)
  | cons owner others =>
      have targetList := canonicalWord_toList word connected
      refine
        { fixed := ?_,
          count_le_three := ?_ }
      · rw [targetList]
        exact B8Canonical.canonicalList_fixed_of_multipleShape
          word.toList multipleShape
      · intro tested
        rw [targetList]
        exact B8Canonical.canonicalList_count_le_three_of_multipleShape
          word.toList multipleShape tested

theorem normalize
    (word : Word Nat) (connected : Connected word) :
    ∃ target,
      B8Canonical.Canonical target ∧ Derives b8Basis word target :=
  ⟨canonicalWord word, canonicalWord_canonical word connected,
    derivesCanonical word connected⟩

def canonicalProof :
    RestrictedCanonicalProof S6_5626.table b8Basis Connected where
  canonical := B8Canonical.Canonical
  normalize := normalize
  uniqueOfValid := fun left right leftCanonical rightCanonical valid =>
    B8Canonical.canonical_eq_of_valid
      leftCanonical rightCanonical valid

theorem basisFor : BasisFor S6_5626.table.semigroup b8Basis :=
  S6_5626.basisFor_of_canonicalProof
    S6_5626.connectedReduction canonicalProof

theorem oppositeBasisFor :
    BasisFor S6_5626.table.semigroup.opposite b8OppositeBasis :=
  S6_5626.oppositeBasisFor_of_canonicalProof
    S6_5626.connectedReduction canonicalProof

end B8Assembly

end SemigroupBasis.CoRoots.Order6SporadicSection12
