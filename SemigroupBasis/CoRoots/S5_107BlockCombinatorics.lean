import SemigroupBasis.CoRoots.S5_107Syntax

namespace SemigroupBasis.CoRoots.S5_107

open SemigroupBasis

/-- Boolean test used by the block scanner: retain exactly the globally
simple letters of `whole`. -/
private def simpleKeep (whole : List Nat) (letter : Nat) : Bool :=
  decide (whole.count letter = 1)

/-- Boolean test for an edge whose two endpoints are globally simple. -/
private def simpleEdgeKeep
    (whole : List Nat) (edge : Nat × Nat) : Bool :=
  simpleKeep whole edge.1 && simpleKeep whole edge.2

/-- Consecutive directed pairs of a possibly empty list.  This is the list
counterpart of `Word.adjacentPairs`. -/
def listAdjacentPairs : List Nat → List (Nat × Nat)
  | [] => []
  | first :: rest => Word.adjacentPairsFrom first rest

@[simp]
theorem listAdjacentPairs_nil :
    listAdjacentPairs [] = [] :=
  rfl

@[simp]
theorem listAdjacentPairs_singleton (letter : Nat) :
    listAdjacentPairs [letter] = [] :=
  rfl

@[simp]
theorem listAdjacentPairs_cons_cons
    (first second : Nat) (rest : List Nat) :
    listAdjacentPairs (first :: second :: rest) =
      (first, second) :: listAdjacentPairs (second :: rest) :=
  rfl

/-- A directed pair occurs exactly at a two-letter factor. -/
theorem mem_listAdjacentPairs_iff_exists_split
    (source target : Nat) :
    ∀ letters : List Nat,
      (source, target) ∈ listAdjacentPairs letters ↔
        ∃ before after,
          letters = before ++ source :: target :: after
  | [] => by
      constructor
      · simp [listAdjacentPairs]
      · rintro ⟨before, after, split⟩
        have lengthEquality := congrArg List.length split
        simp at lengthEquality
        omega
  | [first] => by
      constructor
      · simp [listAdjacentPairs, Word.adjacentPairsFrom]
      · rintro ⟨before, after, split⟩
        have lengthEquality := congrArg List.length split
        simp at lengthEquality
        omega
  | first :: second :: rest => by
      change
        (source, target) ∈
              (first, second) :: listAdjacentPairs (second :: rest) ↔
          ∃ before after,
            first :: second :: rest =
              before ++ source :: target :: after
      simp only [List.mem_cons, Prod.mk.injEq]
      constructor
      · intro member
        rcases member with firstEdge | laterEdge
        · exact
            ⟨[], rest, by
              rcases firstEdge with ⟨rfl, rfl⟩
              rfl⟩
        · obtain ⟨before, after, split⟩ :=
            (mem_listAdjacentPairs_iff_exists_split
              source target (second :: rest)).mp laterEdge
          exact ⟨first :: before, after, by simp [split]⟩
      · rintro ⟨before, after, split⟩
        cases before with
        | nil =>
            simp only [List.nil_append] at split
            injection split with firstEq tailEq
            injection tailEq with secondEq _
            exact Or.inl ⟨firstEq.symm, secondEq.symm⟩
        | cons beforeHead beforeTail =>
            simp only [List.cons_append] at split
            injection split with _ tailSplit
            exact Or.inr <|
              (mem_listAdjacentPairs_iff_exists_split
                source target (second :: rest)).mpr
                ⟨beforeTail, after, tailSplit⟩

theorem listAdjacentPairs_toList (word : Word Nat) :
    listAdjacentPairs word.toList = word.adjacentPairs := by
  cases word
  rfl

theorem mem_adjacentPairs_iff_exists_split
    (source target : Nat) (word : Word Nat) :
    (source, target) ∈ word.adjacentPairs ↔
      ∃ before after,
        word.toList = before ++ source :: target :: after := by
  rw [← listAdjacentPairs_toList]
  exact
    mem_listAdjacentPairs_iff_exists_split
      source target word.toList

private theorem count_filter_of_kept
    (letters : List Nat) (keep : Nat → Bool) (letter : Nat)
    (kept : keep letter = true) :
    (letters.filter keep).count letter = letters.count letter := by
  induction letters with
  | nil => simp
  | cons first rest ih =>
      by_cases equality : first = letter
      · subst first
        simp [kept, ih]
      · by_cases firstKept : keep first
        · simp [firstKept, equality, ih]
        · simp [firstKept, equality, ih]

private theorem count_filter_eq_zero_of_rejected
    (letters : List Nat) (keep : Nat → Bool) (letter : Nat)
    (rejected : keep letter = false) :
    (letters.filter keep).count letter = 0 := by
  apply List.count_eq_zero.mpr
  intro member
  have kept := (List.mem_filter.mp member).2
  rw [rejected] at kept
  contradiction

private theorem nodup_of_count_le_one
    {letters : List Nat}
    (bounded : ∀ letter, letters.count letter ≤ 1) :
    letters.Nodup := by
  induction letters with
  | nil => simp
  | cons first rest ih =>
      simp only [List.nodup_cons]
      constructor
      · intro member
        have positive : 1 ≤ rest.count first :=
          List.count_pos_iff.mpr member
        have bound := bounded first
        simp only [List.count_cons_self] at bound
        omega
      · apply ih
        intro letter
        have bound := bounded letter
        by_cases equality : first = letter
        · subst first
          simp only [List.count_cons_self] at bound
          omega
        · simpa [equality] using bound

/-- Filtering a list by global multiplicity one cannot retain a duplicate. -/
theorem simpleFilter_nodup (letters : List Nat) :
    (letters.filter (simpleKeep letters)).Nodup := by
  apply nodup_of_count_le_one
  intro letter
  by_cases simple : letters.count letter = 1
  · have kept : simpleKeep letters letter = true := by
      simp [simpleKeep, simple]
    rw [count_filter_of_kept letters (simpleKeep letters) letter kept,
      simple]
    omega
  · have rejected : simpleKeep letters letter = false := by
      simp [simpleKeep, simple]
    rw [count_filter_eq_zero_of_rejected
      letters (simpleKeep letters) letter rejected]
    omega

/-- Flattening the scanner output retains the completed current block,
followed by exactly the globally simple letters of the unprocessed suffix. -/
theorem simpleBlockScan_flatten
    (whole current remaining : List Nat) :
    (simpleBlockScan whole current remaining).flatten =
      current.reverse ++ remaining.filter (simpleKeep whole) := by
  induction remaining generalizing current with
  | nil =>
      cases current <;> simp [simpleBlockScan]
  | cons letter rest ih =>
      simp only [simpleBlockScan]
      split <;> rename_i simple
      · rw [ih]
        simp [simpleKeep, simple, List.reverse_cons,
          List.append_assoc]
      · cases current with
        | nil =>
            rw [ih]
            simp [simpleKeep, simple]
        | cons first more =>
            simp only [List.flatten_cons]
            rw [ih]
            simp [simpleKeep, simple]

/-- The complete scanner partitions exactly the globally simple letters. -/
theorem simpleBlocks_flatten (letters : List Nat) :
    (simpleBlocks letters).flatten =
      letters.filter (simpleKeep letters) := by
  simpa [simpleBlocks] using
    simpleBlockScan_flatten letters [] letters

/-- No scanner-emitted block is empty. -/
theorem simpleBlockScan_blocks_nonempty
    (whole current remaining : List Nat) :
    ∀ block ∈ simpleBlockScan whole current remaining,
      block ≠ [] := by
  induction remaining generalizing current with
  | nil =>
      cases current with
      | nil => simp [simpleBlockScan]
      | cons first more =>
          simpa [simpleBlockScan]
  | cons letter rest ih =>
      simp only [simpleBlockScan]
      split <;> rename_i simple
      · exact ih (letter :: current)
      · cases current with
        | nil =>
            exact ih []
        | cons first more =>
            intro block member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · simp
            · exact ih [] block member

theorem simpleBlocks_blocks_nonempty (letters : List Nat) :
    ∀ block ∈ simpleBlocks letters, block ≠ [] := by
  unfold simpleBlocks
  exact simpleBlockScan_blocks_nonempty letters [] letters

/-- The flattened block decomposition is duplicate-free. -/
theorem simpleBlocks_flatten_nodup (letters : List Nat) :
    (simpleBlocks letters).flatten.Nodup := by
  rw [simpleBlocks_flatten]
  exact simpleFilter_nodup letters

theorem simpleBlocks_block_nodup
    {letters block : List Nat}
    (member : block ∈ simpleBlocks letters) :
    block.Nodup := by
  have flattened :
      (simpleBlocks letters).flatten.Pairwise
        (fun left right : Nat => left ≠ right) :=
    simpleBlocks_flatten_nodup letters
  exact (List.pairwise_flatten.mp flattened).1 block member

theorem simpleBlocks_pairwise_disjoint (letters : List Nat) :
    (simpleBlocks letters).Pairwise
      (fun left right =>
        ∀ x ∈ left, ∀ y ∈ right, x ≠ y) := by
  have flattened :
      (simpleBlocks letters).flatten.Pairwise
        (fun left right : Nat => left ≠ right) :=
    simpleBlocks_flatten_nodup letters
  exact (List.pairwise_flatten.mp flattened).2

private theorem blocks_nodup_of_flatten_nodup
    {blocks : List (List Nat)}
    (flattenNodup : blocks.flatten.Nodup)
    (nonempty : ∀ block ∈ blocks, block ≠ []) :
    blocks.Nodup := by
  induction blocks with
  | nil => simp
  | cons block rest ih =>
      simp only [List.nodup_cons]
      have appendNodup :
          (block ++ rest.flatten).Nodup := by
        simpa using flattenNodup
      refine ⟨?_, ih (List.nodup_append.mp appendNodup).2.1 ?_⟩
      · intro blockInRest
        obtain ⟨letter, letterInBlock⟩ :=
          List.exists_mem_of_ne_nil block
            (nonempty block (List.Mem.head rest))
        have letterInFlatten :
            letter ∈ rest.flatten :=
          List.mem_flatten_of_mem blockInRest letterInBlock
        exact
          (List.nodup_append.mp appendNodup).2.2
            letter letterInBlock letter letterInFlatten rfl
      · intro candidate candidateInRest
        exact nonempty candidate
          (List.Mem.tail block candidateInRest)

theorem simpleBlocks_nodup (letters : List Nat) :
    (simpleBlocks letters).Nodup :=
  blocks_nodup_of_flatten_nodup
    (simpleBlocks_flatten_nodup letters)
    (simpleBlocks_blocks_nonempty letters)

/-- Consecutive pairs across a nonempty prefix followed by a nonempty
suffix consist of the pairs inside each side and their boundary edge. -/
private theorem listAdjacentPairs_append_cons
    (head : Nat) (tail : List Nat) (next : Nat) (suffix : List Nat) :
    listAdjacentPairs ((head :: tail) ++ next :: suffix) =
      listAdjacentPairs (head :: tail) ++
        (tail.getLastD head, next) ::
          listAdjacentPairs (next :: suffix) := by
  exact Word.adjacentPairsFrom_append head tail next suffix

private theorem filter_listAdjacentPairs_eq_self
    (whole : List Nat) :
    ∀ letters : List Nat,
      (∀ letter ∈ letters, whole.count letter = 1) →
      (listAdjacentPairs letters).filter (simpleEdgeKeep whole) =
        listAdjacentPairs letters
  | [], _ => rfl
  | [letter], _ => rfl
  | first :: second :: rest, allSimple => by
      have firstSimple :
          whole.count first = 1 :=
        allSimple first (by simp)
      have secondSimple :
          whole.count second = 1 :=
        allSimple second (by simp)
      have tailSimple :
          ∀ letter ∈ second :: rest,
            whole.count letter = 1 := by
        intro letter member
        exact allSimple letter (by simp [member])
      simp [listAdjacentPairs_cons_cons, simpleEdgeKeep, simpleKeep,
        firstSimple, secondSimple,
        filter_listAdjacentPairs_eq_self
          whole (second :: rest) tailSimple]

private theorem filter_listAdjacentPairs_cons_of_not_simple
    (whole : List Nat) (letter : Nat) (rest : List Nat)
    (notSimple : whole.count letter ≠ 1) :
    (listAdjacentPairs (letter :: rest)).filter
        (simpleEdgeKeep whole) =
      (listAdjacentPairs rest).filter
        (simpleEdgeKeep whole) := by
  cases rest with
  | nil => rfl
  | cons next suffix =>
      simp [listAdjacentPairs_cons_cons, simpleEdgeKeep,
        simpleKeep, notSimple]

/-- The scanner retains exactly those consecutive edges whose two endpoints
are globally simple.  This is the edge counterpart of
`simpleBlockScan_flatten`. -/
theorem simpleBlockScan_edges
    (whole current remaining : List Nat)
    (currentSimple :
      ∀ letter ∈ current, whole.count letter = 1) :
    (simpleBlockScan whole current remaining).flatMap
        listAdjacentPairs =
      (listAdjacentPairs (current.reverse ++ remaining)).filter
        (simpleEdgeKeep whole) := by
  induction remaining generalizing current with
  | nil =>
      cases current with
      | nil =>
          simp [simpleBlockScan, listAdjacentPairs]
      | cons first more =>
          have reversedSimple :
              ∀ letter ∈ (first :: more).reverse,
                whole.count letter = 1 := by
            intro letter member
            exact currentSimple letter (List.mem_reverse.mp member)
          have filtered :=
            filter_listAdjacentPairs_eq_self
              whole (first :: more).reverse reversedSimple
          simpa [simpleBlockScan] using filtered.symm
  | cons letter rest ih =>
      by_cases simple : whole.count letter = 1
      · have extendedSimple :
            ∀ value ∈ letter :: current,
              whole.count value = 1 := by
          intro value member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact simple
          · exact currentSimple value member
        have step := ih (letter :: current) extendedSimple
        simpa only [simpleBlockScan, if_pos simple,
          List.reverse_cons, List.append_assoc,
          List.singleton_append] using step
      · cases current with
        | nil =>
            have step := ih [] (by simp)
            rw [simpleBlockScan, if_neg simple]
            exact step.trans <|
              (filter_listAdjacentPairs_cons_of_not_simple
                whole letter rest simple).symm
        | cons first more =>
            have step := ih [] (by simp)
            have reversedSimple :
                ∀ value ∈ (first :: more).reverse,
                  whole.count value = 1 := by
              intro value member
              exact currentSimple value (List.mem_reverse.mp member)
            cases reversed :
                (first :: more).reverse with
            | nil =>
                have impossible :
                    (first :: more).reverse ≠ [] := by simp
                exact False.elim (impossible reversed)
            | cons reversedHead reversedTail =>
                have reversedSimple' :
                    ∀ value ∈ reversedHead :: reversedTail,
                      whole.count value = 1 := by
                  simpa [reversed] using reversedSimple
                have prefixFiltered :=
                  filter_listAdjacentPairs_eq_self
                    whole (reversedHead :: reversedTail)
                    reversedSimple'
                have suffixFiltered :=
                  filter_listAdjacentPairs_cons_of_not_simple
                    whole letter rest simple
                simp only [simpleBlockScan, if_neg simple,
                  List.flatMap_cons]
                rw [step, reversed]
                rw [listAdjacentPairs_append_cons]
                simp only [List.filter_append]
                rw [prefixFiltered]
                simp [simpleEdgeKeep, simpleKeep, simple,
                  suffixFiltered]

/-- The internal scanner edges are exactly the globally simple adjacent
pairs of the source list. -/
theorem simpleBlocks_edges (letters : List Nat) :
    (simpleBlocks letters).flatMap listAdjacentPairs =
      (listAdjacentPairs letters).filter
        (simpleEdgeKeep letters) := by
  simpa [simpleBlocks] using
    simpleBlockScan_edges letters [] letters (by simp)

/-- Every member of an emitted block is globally simple. -/
theorem simpleBlocks_letter_simple
    {letters block : List Nat} {letter : Nat}
    (blockMember : block ∈ simpleBlocks letters)
    (letterMember : letter ∈ block) :
    letters.count letter = 1 := by
  have flattenedMember :
      letter ∈ (simpleBlocks letters).flatten :=
    List.mem_flatten_of_mem blockMember letterMember
  rw [simpleBlocks_flatten] at flattenedMember
  have kept := (List.mem_filter.mp flattenedMember).2
  simpa [simpleKeep] using of_decide_eq_true kept

/-- The scanner's graph is exactly `SimpleAdjacent`. -/
theorem mem_simpleBlocks_edges_iff
    (word : Word Nat) (source target : Nat) :
    (source, target) ∈
        (simpleBlocks word.toList).flatMap listAdjacentPairs ↔
      SimpleAdjacent word source target := by
  rw [simpleBlocks_edges]
  simp only [List.mem_filter, simpleEdgeKeep, Bool.and_eq_true,
    simpleKeep, decide_eq_true_eq, listAdjacentPairs_toList]
  simp [SimpleAdjacent, SimpleIn, and_assoc, and_left_comm, and_comm]

/-- The source of a listed edge occurs in the underlying list. -/
private theorem source_mem_of_mem_listAdjacentPairs
    {letters : List Nat} {source target : Nat}
    (edge : (source, target) ∈ listAdjacentPairs letters) :
    source ∈ letters := by
  rcases
      (mem_listAdjacentPairs_iff_exists_split
        source target letters).mp edge with
    ⟨before, after, split⟩
  rw [split]
  simp

/-- The target of a listed edge occurs in the underlying list. -/
private theorem target_mem_of_mem_listAdjacentPairs
    {letters : List Nat} {source target : Nat}
    (edge : (source, target) ∈ listAdjacentPairs letters) :
    target ∈ letters := by
  rcases
      (mem_listAdjacentPairs_iff_exists_split
        source target letters).mp edge with
    ⟨before, after, split⟩
  rw [split]
  simp

/-- In a duplicate-free flattening, two member blocks sharing a letter are
the same block. -/
private theorem block_eq_of_common_letter
    {blocks : List (List Nat)} {leftBlock rightBlock : List Nat}
    {letter : Nat}
    (flattenNodup : blocks.flatten.Nodup)
    (leftMember : leftBlock ∈ blocks)
    (rightMember : rightBlock ∈ blocks)
    (letterLeft : letter ∈ leftBlock)
    (letterRight : letter ∈ rightBlock) :
    leftBlock = rightBlock := by
  induction blocks with
  | nil =>
      simp at leftMember
  | cons first rest ih =>
      have appendNodup :
          (first ++ rest.flatten).Nodup := by
        simpa using flattenNodup
      have tailNodup :
          rest.flatten.Nodup :=
        (List.nodup_append.mp appendNodup).2.1
      have disjoint :
          ∀ left ∈ first, ∀ right ∈ rest.flatten,
            left = right → False :=
        (List.nodup_append.mp appendNodup).2.2
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftMember <;>
        rcases rightMember with rfl | rightMember
      · rfl
      · have rightInFlatten :
            letter ∈ rest.flatten :=
          List.mem_flatten_of_mem rightMember letterRight
        exact False.elim <|
          disjoint letter letterLeft letter rightInFlatten rfl
      · have leftInFlatten :
            letter ∈ rest.flatten :=
          List.mem_flatten_of_mem leftMember letterLeft
        exact False.elim <|
          disjoint letter letterRight letter leftInFlatten rfl
      · exact ih tailNodup leftMember rightMember

private theorem not_mem_parts_of_nodup_split
    {letters before after : List Nat} {letter : Nat}
    (nodup : letters.Nodup)
    (split : letters = before ++ letter :: after) :
    letter ∉ before ∧ letter ∉ after := by
  have splitNodup :
      (before ++ letter :: after).Nodup := by
    rw [← split]
    exact nodup
  have appendData := List.nodup_append.mp splitNodup
  constructor
  · intro member
    exact appendData.2.2
      letter member letter (by simp) rfl
  · exact (List.nodup_cons.mp appendData.2.1).1

/-- A designated occurrence in a nodup list has a unique prefix and suffix. -/
private theorem nodup_split_unique
    {letters firstBefore firstAfter secondBefore secondAfter : List Nat}
    {letter : Nat}
    (nodup : letters.Nodup)
    (firstSplit :
      letters = firstBefore ++ letter :: firstAfter)
    (secondSplit :
      letters = secondBefore ++ letter :: secondAfter) :
    firstBefore = secondBefore ∧ firstAfter = secondAfter := by
  have firstAbsent :=
    not_mem_parts_of_nodup_split nodup firstSplit
  have secondAbsent :=
    not_mem_parts_of_nodup_split nodup secondSplit
  have equality :
      firstBefore ++ letter :: firstAfter =
        secondBefore ++ letter :: secondAfter :=
    firstSplit.symm.trans secondSplit
  rcases List.append_eq_append_iff.mp equality with
      ⟨extra, secondPrefix, firstTail⟩ |
      ⟨extra, firstPrefix, secondTail⟩
  · cases extra with
    | nil =>
        simp only [List.append_nil] at secondPrefix
        simp only [List.nil_append, List.cons.injEq, true_and] at firstTail
        exact ⟨secondPrefix.symm, firstTail⟩
    | cons head tail =>
        injection firstTail with headEq _
        subst head
        exfalso
        apply secondAbsent.1
        rw [secondPrefix]
        simp
  · cases extra with
    | nil =>
        simp only [List.append_nil] at firstPrefix
        simp only [List.nil_append, List.cons.injEq, true_and] at secondTail
        exact ⟨firstPrefix, secondTail.symm⟩
    | cons head tail =>
        injection secondTail with headEq _
        subst head
        exfalso
        apply firstAbsent.1
        rw [firstPrefix]
        simp

/-- If a global segmentation edge starts at a letter of a fixed block, that
edge occurs inside the fixed block. -/
private theorem global_edge_split_from_source
    {blocks : List (List Nat)} {block : List Nat}
    {source target : Nat}
    (flattenNodup : blocks.flatten.Nodup)
    (blockMember : block ∈ blocks)
    (sourceMember : source ∈ block)
    (edge :
      (source, target) ∈ blocks.flatMap listAdjacentPairs) :
    ∃ before after,
      block = before ++ source :: target :: after := by
  rcases List.mem_flatMap.mp edge with
    ⟨candidate, candidateMember, candidateEdge⟩
  have sourceCandidate :
      source ∈ candidate :=
    source_mem_of_mem_listAdjacentPairs candidateEdge
  have equalBlocks :=
    block_eq_of_common_letter flattenNodup
      blockMember candidateMember sourceMember sourceCandidate
  subst candidate
  exact
    (mem_listAdjacentPairs_iff_exists_split
      source target block).mp candidateEdge

/-- If a global segmentation edge ends at a letter of a fixed block, that
edge occurs inside the fixed block. -/
private theorem global_edge_split_from_target
    {blocks : List (List Nat)} {block : List Nat}
    {source target : Nat}
    (flattenNodup : blocks.flatten.Nodup)
    (blockMember : block ∈ blocks)
    (targetMember : target ∈ block)
    (edge :
      (source, target) ∈ blocks.flatMap listAdjacentPairs) :
    ∃ before after,
      block = before ++ source :: target :: after := by
  rcases List.mem_flatMap.mp edge with
    ⟨candidate, candidateMember, candidateEdge⟩
  have targetCandidate :
      target ∈ candidate :=
    target_mem_of_mem_listAdjacentPairs candidateEdge
  have equalBlocks :=
    block_eq_of_common_letter flattenNodup
      blockMember candidateMember targetMember targetCandidate
  subst candidate
  exact
    (mem_listAdjacentPairs_iff_exists_split
      source target block).mp candidateEdge

/-- Two blocks in duplicate-free segmentations with the same global edge
set have equal suffixes after any common letter. -/
private theorem block_suffix_eq_of_same_edges
    {leftBlocks rightBlocks : List (List Nat)}
    {leftBlock rightBlock : List Nat}
    (leftFlattenNodup : leftBlocks.flatten.Nodup)
    (rightFlattenNodup : rightBlocks.flatten.Nodup)
    (leftBlockMember : leftBlock ∈ leftBlocks)
    (rightBlockMember : rightBlock ∈ rightBlocks)
    (sameEdges :
      ∀ source target,
        (source, target) ∈
              leftBlocks.flatMap listAdjacentPairs ↔
          (source, target) ∈
              rightBlocks.flatMap listAdjacentPairs) :
    ∀ {anchor : Nat}
      {leftPrefix leftSuffix rightPrefix rightSuffix : List Nat},
      leftBlock = leftPrefix ++ anchor :: leftSuffix →
      rightBlock = rightPrefix ++ anchor :: rightSuffix →
      leftSuffix = rightSuffix := by
  intro anchor leftPrefix leftSuffix
    rightPrefix rightSuffix leftSplit rightSplit
  induction leftSuffix generalizing
      anchor leftPrefix rightPrefix rightSuffix with
  | nil =>
      cases rightSuffix with
      | nil => rfl
      | cons next rightRest =>
          have rightLocal :
              (anchor, next) ∈
                listAdjacentPairs rightBlock := by
            apply
              (mem_listAdjacentPairs_iff_exists_split
                anchor next rightBlock).mpr
            exact ⟨rightPrefix, rightRest, rightSplit⟩
          have rightGlobal :
              (anchor, next) ∈
                rightBlocks.flatMap listAdjacentPairs :=
            List.mem_flatMap.mpr
              ⟨rightBlock, rightBlockMember, rightLocal⟩
          have leftGlobal :
              (anchor, next) ∈
                leftBlocks.flatMap listAdjacentPairs :=
            (sameEdges anchor next).mpr rightGlobal
          have anchorLeft : anchor ∈ leftBlock := by
            rw [leftSplit]
            simp
          rcases
              global_edge_split_from_source
                leftFlattenNodup leftBlockMember
                anchorLeft leftGlobal with
            ⟨before, after, edgeSplit⟩
          have leftBlockNodup :
              leftBlock.Nodup :=
            leftFlattenNodup.sublist
              (List.sublist_flatten_of_mem leftBlockMember)
          have compared :=
            nodup_split_unique leftBlockNodup
              leftSplit edgeSplit
          simp at compared
  | cons next leftRest ih =>
      have leftLocal :
          (anchor, next) ∈
            listAdjacentPairs leftBlock := by
        apply
          (mem_listAdjacentPairs_iff_exists_split
            anchor next leftBlock).mpr
        exact ⟨leftPrefix, leftRest, leftSplit⟩
      have leftGlobal :
          (anchor, next) ∈
            leftBlocks.flatMap listAdjacentPairs :=
        List.mem_flatMap.mpr
          ⟨leftBlock, leftBlockMember, leftLocal⟩
      have rightGlobal :
          (anchor, next) ∈
            rightBlocks.flatMap listAdjacentPairs :=
        (sameEdges anchor next).mp leftGlobal
      have anchorRight : anchor ∈ rightBlock := by
        rw [rightSplit]
        simp
      rcases
          global_edge_split_from_source
            rightFlattenNodup rightBlockMember
            anchorRight rightGlobal with
        ⟨before, after, edgeSplit⟩
      have rightBlockNodup :
          rightBlock.Nodup :=
        rightFlattenNodup.sublist
          (List.sublist_flatten_of_mem rightBlockMember)
      have compared :=
        nodup_split_unique rightBlockNodup
          rightSplit edgeSplit
      have rightPrefixEq : rightPrefix = before :=
        compared.1
      have rightSuffixEq :
          rightSuffix = next :: after :=
        compared.2
      have leftNextSplit :
          leftBlock =
            (leftPrefix ++ [anchor]) ++ next :: leftRest := by
        simpa [List.append_assoc] using leftSplit
      have rightNextSplit :
          rightBlock =
            (rightPrefix ++ [anchor]) ++ next :: after := by
        rw [rightSplit, rightSuffixEq]
        simp [List.append_assoc]
      have restEqual :
          leftRest = after :=
        ih leftNextSplit rightNextSplit
      rw [rightSuffixEq, restEqual]

private theorem listReverseRec
    {α : Type} {motive : List α → Prop}
    (letters : List α)
    (empty : motive [])
    (snoc :
      ∀ initial last, motive initial →
        motive (initial ++ [last])) :
    motive letters := by
  have reversed : motive letters.reverse.reverse := by
    induction letters.reverse with
    | nil => simpa using empty
    | cons last reversedInitial ih =>
        simpa [List.reverse_cons] using
          snoc reversedInitial.reverse last ih
  simpa using reversed

/-- Two blocks in duplicate-free segmentations with the same global edge
set have equal prefixes before any common letter. -/
private theorem block_prefix_eq_of_same_edges
    {leftBlocks rightBlocks : List (List Nat)}
    {leftBlock rightBlock : List Nat}
    (leftFlattenNodup : leftBlocks.flatten.Nodup)
    (rightFlattenNodup : rightBlocks.flatten.Nodup)
    (leftBlockMember : leftBlock ∈ leftBlocks)
    (rightBlockMember : rightBlock ∈ rightBlocks)
    (sameEdges :
      ∀ source target,
        (source, target) ∈
              leftBlocks.flatMap listAdjacentPairs ↔
          (source, target) ∈
              rightBlocks.flatMap listAdjacentPairs) :
    ∀ {anchor : Nat}
      {leftPrefix leftSuffix rightPrefix rightSuffix : List Nat},
      leftBlock = leftPrefix ++ anchor :: leftSuffix →
      rightBlock = rightPrefix ++ anchor :: rightSuffix →
      leftPrefix = rightPrefix := by
  intro anchor leftPrefix leftSuffix
    rightPrefix rightSuffix leftSplit rightSplit
  revert anchor leftSuffix rightPrefix rightSuffix
  apply listReverseRec leftPrefix
  · intro anchor leftSuffix rightPrefix rightSuffix
      leftSplit rightSplit
    by_cases rightEmpty : rightPrefix = []
    · exact rightEmpty.symm
    · let previous := rightPrefix.getLast rightEmpty
      let before := rightPrefix.dropLast
      have rightPrefixShape :
          before ++ [previous] = rightPrefix := by
        exact List.dropLast_concat_getLast rightEmpty
      have rightLocal :
          (previous, anchor) ∈
            listAdjacentPairs rightBlock := by
        apply
          (mem_listAdjacentPairs_iff_exists_split
            previous anchor rightBlock).mpr
        refine ⟨before, rightSuffix, ?_⟩
        rw [rightSplit, ← rightPrefixShape]
        simp [List.append_assoc]
      have rightGlobal :
          (previous, anchor) ∈
            rightBlocks.flatMap listAdjacentPairs :=
        List.mem_flatMap.mpr
          ⟨rightBlock, rightBlockMember, rightLocal⟩
      have leftGlobal :
          (previous, anchor) ∈
            leftBlocks.flatMap listAdjacentPairs :=
        (sameEdges previous anchor).mpr rightGlobal
      have anchorLeft : anchor ∈ leftBlock := by
        rw [leftSplit]
        simp
      rcases
          global_edge_split_from_target
            leftFlattenNodup leftBlockMember
            anchorLeft leftGlobal with
        ⟨edgeBefore, edgeAfter, edgeSplit⟩
      have leftBlockNodup :
          leftBlock.Nodup :=
        leftFlattenNodup.sublist
          (List.sublist_flatten_of_mem leftBlockMember)
      have edgeAtAnchor :
          leftBlock =
            (edgeBefore ++ [previous]) ++
              anchor :: edgeAfter := by
        simpa [List.append_assoc] using edgeSplit
      have compared :=
        nodup_split_unique leftBlockNodup
          leftSplit edgeAtAnchor
      simp at compared
  · intro leftBefore previous ih
      anchor leftSuffix rightPrefix rightSuffix
      leftSplit rightSplit
    have leftLocal :
        (previous, anchor) ∈
          listAdjacentPairs leftBlock := by
      apply
        (mem_listAdjacentPairs_iff_exists_split
          previous anchor leftBlock).mpr
      refine ⟨leftBefore, leftSuffix, ?_⟩
      simpa [List.append_assoc] using leftSplit
    have leftGlobal :
        (previous, anchor) ∈
          leftBlocks.flatMap listAdjacentPairs :=
      List.mem_flatMap.mpr
        ⟨leftBlock, leftBlockMember, leftLocal⟩
    have rightGlobal :
        (previous, anchor) ∈
          rightBlocks.flatMap listAdjacentPairs :=
      (sameEdges previous anchor).mp leftGlobal
    have anchorRight : anchor ∈ rightBlock := by
      rw [rightSplit]
      simp
    rcases
        global_edge_split_from_target
          rightFlattenNodup rightBlockMember
          anchorRight rightGlobal with
      ⟨before, after, edgeSplit⟩
    have rightBlockNodup :
        rightBlock.Nodup :=
      rightFlattenNodup.sublist
        (List.sublist_flatten_of_mem rightBlockMember)
    have edgeAtAnchor :
        rightBlock =
          (before ++ [previous]) ++ anchor :: after := by
      simpa [List.append_assoc] using edgeSplit
    have compared :=
      nodup_split_unique rightBlockNodup
        rightSplit edgeAtAnchor
    have rightPrefixEq :
        rightPrefix = before ++ [previous] :=
      compared.1
    have rightSuffixEq : rightSuffix = after :=
      compared.2
    have leftPreviousSplit :
        leftBlock =
          leftBefore ++ previous :: anchor :: leftSuffix := by
      simpa [List.append_assoc] using leftSplit
    have rightPreviousSplit :
        rightBlock =
          before ++ previous :: anchor :: after := by
      exact edgeSplit
    have beforeEqual :
        leftBefore = before :=
      ih leftPreviousSplit rightPreviousSplit
    rw [rightPrefixEq, beforeEqual]

/-- A common vertex identifies the same complete path block in two nodup
segmentations with the same directed edge set. -/
private theorem block_eq_of_common_letter_and_same_edges
    {leftBlocks rightBlocks : List (List Nat)}
    {leftBlock rightBlock : List Nat}
    {letter : Nat}
    (leftFlattenNodup : leftBlocks.flatten.Nodup)
    (rightFlattenNodup : rightBlocks.flatten.Nodup)
    (leftBlockMember : leftBlock ∈ leftBlocks)
    (rightBlockMember : rightBlock ∈ rightBlocks)
    (letterLeft : letter ∈ leftBlock)
    (letterRight : letter ∈ rightBlock)
    (sameEdges :
      ∀ source target,
        (source, target) ∈
              leftBlocks.flatMap listAdjacentPairs ↔
          (source, target) ∈
              rightBlocks.flatMap listAdjacentPairs) :
    leftBlock = rightBlock := by
  rcases List.mem_iff_append.mp letterLeft with
    ⟨leftPrefix, leftSuffix, leftSplit⟩
  rcases List.mem_iff_append.mp letterRight with
    ⟨rightPrefix, rightSuffix, rightSplit⟩
  have prefixEqual :=
    block_prefix_eq_of_same_edges
      leftFlattenNodup rightFlattenNodup
      leftBlockMember rightBlockMember sameEdges
      leftSplit rightSplit
  have suffixEqual :=
    block_suffix_eq_of_same_edges
      leftFlattenNodup rightFlattenNodup
      leftBlockMember rightBlockMember sameEdges
      leftSplit rightSplit
  rw [leftSplit, rightSplit, prefixEqual, suffixEqual]

/-- Duplicate-free nonempty path segmentations are determined, up to block
permutation, by their vertex set and directed edge set. -/
private theorem pathSegmentations_perm
    {leftBlocks rightBlocks : List (List Nat)}
    (leftFlattenNodup : leftBlocks.flatten.Nodup)
    (rightFlattenNodup : rightBlocks.flatten.Nodup)
    (leftNonempty :
      ∀ block ∈ leftBlocks, block ≠ [])
    (rightNonempty :
      ∀ block ∈ rightBlocks, block ≠ [])
    (sameVertices :
      ∀ letter,
        letter ∈ leftBlocks.flatten ↔
          letter ∈ rightBlocks.flatten)
    (sameEdges :
      ∀ source target,
        (source, target) ∈
              leftBlocks.flatMap listAdjacentPairs ↔
          (source, target) ∈
              rightBlocks.flatMap listAdjacentPairs) :
    leftBlocks.Perm rightBlocks := by
  have leftNodup :
      leftBlocks.Nodup :=
    blocks_nodup_of_flatten_nodup
      leftFlattenNodup leftNonempty
  have rightNodup :
      rightBlocks.Nodup :=
    blocks_nodup_of_flatten_nodup
      rightFlattenNodup rightNonempty
  have sameBlockMembership :
      ∀ block, block ∈ leftBlocks ↔ block ∈ rightBlocks := by
    intro block
    constructor
    · intro blockMember
      obtain ⟨letter, letterMember⟩ :=
        List.exists_mem_of_ne_nil block
          (leftNonempty block blockMember)
      have leftFlattenMember :
          letter ∈ leftBlocks.flatten :=
        List.mem_flatten_of_mem blockMember letterMember
      have rightFlattenMember :
          letter ∈ rightBlocks.flatten :=
        (sameVertices letter).mp leftFlattenMember
      rcases List.mem_flatten.mp rightFlattenMember with
        ⟨rightBlock, rightBlockMember, letterRight⟩
      have blockEqual :=
        block_eq_of_common_letter_and_same_edges
          leftFlattenNodup rightFlattenNodup
          blockMember rightBlockMember
          letterMember letterRight sameEdges
      rwa [blockEqual]
    · intro blockMember
      obtain ⟨letter, letterMember⟩ :=
        List.exists_mem_of_ne_nil block
          (rightNonempty block blockMember)
      have rightFlattenMember :
          letter ∈ rightBlocks.flatten :=
        List.mem_flatten_of_mem blockMember letterMember
      have leftFlattenMember :
          letter ∈ leftBlocks.flatten :=
        (sameVertices letter).mpr rightFlattenMember
      rcases List.mem_flatten.mp leftFlattenMember with
        ⟨leftBlock, leftBlockMember, letterLeft⟩
      have blockEqual :=
        block_eq_of_common_letter_and_same_edges
          leftFlattenNodup rightFlattenNodup
          leftBlockMember blockMember
          letterLeft letterMember sameEdges
      rwa [← blockEqual]
  rw [List.perm_iff_count]
  intro block
  rw [leftNodup.count, rightNodup.count]
  simp only [sameBlockMembership block]

theorem mem_simpleBlocks_flatten_iff
    (word : Word Nat) (letter : Nat) :
    letter ∈ (simpleBlocks word.toList).flatten ↔
      SimpleIn word letter := by
  rw [simpleBlocks_flatten]
  simp only [List.mem_filter, simpleKeep,
    decide_eq_true_eq, SimpleIn]
  constructor
  · exact And.right
  · intro countOne
    exact
      ⟨List.count_pos_iff.mp (by omega), countOne⟩

private theorem headD_data_of_flatten_cons
    {blocks : List (List Nat)} {first : Nat} {rest : List Nat}
    (blocksNonempty :
      ∀ block ∈ blocks, block ≠ [])
    (flattenShape : blocks.flatten = first :: rest) :
    blocks.headD [] ∈ blocks ∧
      first ∈ blocks.headD [] := by
  cases blocks with
  | nil =>
      simp at flattenShape
  | cons block blocks =>
      have blockNonempty :
          block ≠ [] :=
        blocksNonempty block (by simp)
      cases block with
      | nil => contradiction
      | cons blockHead blockTail =>
          simp only [List.flatten_cons, List.cons_append] at flattenShape
          injection flattenShape with headEqual
          subst blockHead
          simp

private theorem reverseBlocks_flatten
    (blocks : List (List Nat)) :
    (blocks.reverse.map List.reverse).flatten =
      blocks.flatten.reverse := by
  simpa only [List.map_reverse] using
    (List.reverse_flatten (L := blocks)).symm

private theorem reverseBlocks_headD
    (blocks : List (List Nat)) :
    (blocks.reverse.map List.reverse).headD [] =
      (blocks.getLastD []).reverse := by
  rw [List.headD_eq_head?_getD, List.head?_map,
    List.head?_reverse, List.getLastD_eq_getLast?]
  simpa using
    (Option.getD_map List.reverse
      ([] : List Nat) blocks.getLast?)

private theorem getLastD_data_of_flatten_append
    {blocks : List (List Nat)} {initial : List Nat} {last : Nat}
    (blocksNonempty :
      ∀ block ∈ blocks, block ≠ [])
    (flattenShape : blocks.flatten = initial ++ [last]) :
    blocks.getLastD [] ∈ blocks ∧
      last ∈ blocks.getLastD [] := by
  have transformedNonempty :
      ∀ block ∈ blocks.reverse.map List.reverse,
        block ≠ [] := by
    intro block member
    rcases List.mem_map.mp member with
      ⟨source, sourceMember, rfl⟩
    have sourceMember' : source ∈ blocks := by
      simpa using sourceMember
    simpa using blocksNonempty source sourceMember'
  have transformedShape :
      (blocks.reverse.map List.reverse).flatten =
        last :: initial.reverse := by
    rw [reverseBlocks_flatten, flattenShape]
    simp [List.reverse_append]
  have transformedData :=
    headD_data_of_flatten_cons
      transformedNonempty transformedShape
  have blocksNotNil : blocks ≠ [] := by
    intro empty
    rw [empty] at flattenShape
    simp at flattenShape
  have lastBlockMember :
      blocks.getLastD [] ∈ blocks := by
    cases blocks with
    | nil => contradiction
    | cons first rest =>
        simpa only [List.getLastD_cons] using
          (List.getLastD_mem_cons
            (l := rest) (a := first))
  refine ⟨lastBlockMember, ?_⟩
  rw [reverseBlocks_headD] at transformedData
  simpa using transformedData.2

private theorem word_toList_eq_prefix_final
    (word : Word Nat) :
    ∃ initial, word.toList = initial ++ [word.final] := by
  cases word with
  | mk head tail =>
      refine ⟨(head :: tail).dropLast, ?_⟩
      have reconstruct :=
        (List.dropLast_concat_getLast
          (l := head :: tail) (by simp)).symm
      rw [List.getLast_eq_getLastD] at reconstruct
      simpa [Word.toList, Word.final] using reconstruct

private theorem initialSimpleBlock_toList
    (word : Word Nat) :
    initialSimpleBlock word.toList =
      if decide (word.toList.count word.head = 1) then
        (simpleBlocks word.toList).headD []
      else
        [] := by
  cases word
  rfl

private theorem finalSimpleBlock_toList
    (word : Word Nat) :
    finalSimpleBlock word.toList =
      if decide (word.toList.count word.final = 1) then
        (simpleBlocks word.toList).getLastD []
      else
        [] := by
  cases word
  rfl

private theorem initial_block_data
    (word : Word Nat)
    (simple : SimpleIn word word.head) :
    initialSimpleBlock word.toList ∈
        simpleBlocks word.toList ∧
      word.head ∈ initialSimpleBlock word.toList := by
  have filteredShape :
      word.toList.filter (simpleKeep word.toList) =
        word.head ::
          word.tail.filter (simpleKeep word.toList) := by
    cases word with
    | mk head tail =>
        have headKept :
            simpleKeep (head :: tail) head = true := by
          simpa [simpleKeep, SimpleIn, Word.toList] using simple
        exact List.filter_cons_of_pos headKept
  have flattenedShape :
      (simpleBlocks word.toList).flatten =
        word.head ::
          word.tail.filter (simpleKeep word.toList) := by
    rw [simpleBlocks_flatten, filteredShape]
  have data :=
    headD_data_of_flatten_cons
      (simpleBlocks_blocks_nonempty word.toList)
      flattenedShape
  rw [initialSimpleBlock_toList]
  simp [SimpleIn] at simple
  simpa [simple] using data

private theorem final_block_data
    (word : Word Nat)
    (simple : SimpleIn word word.final) :
    finalSimpleBlock word.toList ∈
        simpleBlocks word.toList ∧
      word.final ∈ finalSimpleBlock word.toList := by
  rcases word_toList_eq_prefix_final word with
    ⟨initial, wordShape⟩
  have finalKept :
      simpleKeep word.toList word.final = true := by
    simpa [simpleKeep, SimpleIn] using simple
  have finalKeptAfterShape :
      simpleKeep (initial ++ [word.final]) word.final = true := by
    rw [← wordShape]
    exact finalKept
  have filteredShape :
      word.toList.filter (simpleKeep word.toList) =
        initial.filter (simpleKeep word.toList) ++ [word.final] := by
    rw [wordShape, List.filter_append]
    simp only [List.filter_cons_of_pos finalKeptAfterShape,
      List.filter_nil]
  have flattenedShape :
      (simpleBlocks word.toList).flatten =
        initial.filter (simpleKeep word.toList) ++ [word.final] := by
    rw [simpleBlocks_flatten, filteredShape]
  have data :=
    getLastD_data_of_flatten_append
      (simpleBlocks_blocks_nonempty word.toList)
      flattenedShape
  rw [finalSimpleBlock_toList]
  simp [SimpleIn] at simple
  simpa [simple] using data

/-- `distinctLetters` really contains no duplicate. -/
theorem distinctLetters_nodup :
    ∀ letters : List Nat, (distinctLetters letters).Nodup
  | [] => by simp [distinctLetters]
  | head :: tail => by
      simp only [distinctLetters, List.nodup_cons]
      constructor
      · intro member
        have tested := (List.mem_filter.mp member).2
        simp at tested
      · exact
          (distinctLetters_nodup tail).filter
            (fun next => decide (next ≠ head))

private def multipleLetterInput (letters : List Nat) : List Nat :=
  (distinctLetters letters).filter
    (fun letter => decide (2 ≤ letters.count letter))

private theorem multipleLetterInput_nodup (letters : List Nat) :
    (multipleLetterInput letters).Nodup := by
  exact
    (distinctLetters_nodup letters).filter
      (fun letter => decide (2 ≤ letters.count letter))

private theorem multipleLetterInput_mem_iff
    (letter : Nat) (letters : List Nat) :
    letter ∈ multipleLetterInput letters ↔
      2 ≤ letters.count letter := by
  simp only [multipleLetterInput, List.mem_filter,
    distinctLetters_mem_iff, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro multiple
    exact
      ⟨List.count_pos_iff.mp (by omega), multiple⟩

private theorem sortedMultipleLetters_perm_input
    (letters : List Nat) :
    (sortedMultipleLetters letters).Perm
      (multipleLetterInput letters) := by
  exact List.mergeSort_perm _ _

private theorem compare_not_gt_iff_le :
    ∀ left right : List Nat,
      compare left right != Ordering.gt ↔ left ≤ right
  | [], [] => by simp
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp
  | leftHead :: leftTail, rightHead :: rightTail => by
      rw [List.cons_le_cons_iff]
      by_cases less : leftHead < rightHead
      · have compared :
            compare leftHead rightHead = Ordering.lt :=
          Nat.compare_eq_lt.mpr less
        simp [List.compare_cons_cons, compared, less]
      · by_cases equal : leftHead = rightHead
        · subst rightHead
          simpa [List.compare_cons_cons] using
            compare_not_gt_iff_le leftTail rightTail
        · have greater : rightHead < leftHead := by
            omega
          have compared :
              compare leftHead rightHead = Ordering.gt :=
            Nat.compare_eq_gt.mpr greater
          simp [List.compare_cons_cons, compared, less, equal]

theorem sortedMultipleLetters_pairwise
    (letters : List Nat) :
    (sortedMultipleLetters letters).Pairwise (· ≤ ·) := by
  have transitive :
      ∀ left middle right : Nat,
        decide (left ≤ middle) = true →
        decide (middle ≤ right) = true →
        decide (left ≤ right) = true := by
    intro left middle right first second
    exact decide_eq_true
      (Nat.le_trans
        (of_decide_eq_true first)
        (of_decide_eq_true second))
  have total :
      ∀ left right : Nat,
        (decide (left ≤ right) ||
          decide (right ≤ left)) = true := by
    intro left right
    rcases Nat.le_total left right with first | second
    · simp [first]
    · simp [second]
  have sorted :=
    List.pairwise_mergeSort transitive total
      (multipleLetterInput letters)
  simpa [sortedMultipleLetters, multipleLetterInput] using
    (sorted.imp fun relation => of_decide_eq_true relation)

theorem sortedSimpleBlocks_pairwise
    (blocks : List (List Nat)) :
    (sortedSimpleBlocks blocks).Pairwise (· ≤ ·) := by
  have transitive :
      ∀ left middle right : List Nat,
        decide (compare left middle != Ordering.gt) = true →
        decide (compare middle right != Ordering.gt) = true →
        decide (compare left right != Ordering.gt) = true := by
    intro left middle right first second
    apply decide_eq_true
    apply (compare_not_gt_iff_le left right).mpr
    exact List.le_trans
      ((compare_not_gt_iff_le left middle).mp
        (of_decide_eq_true first))
      ((compare_not_gt_iff_le middle right).mp
        (of_decide_eq_true second))
  have total :
      ∀ left right : List Nat,
        (decide (compare left right != Ordering.gt) ||
          decide (compare right left != Ordering.gt)) = true := by
    intro left right
    rcases List.le_total left right with first | second
    · have tested :
          compare left right != Ordering.gt :=
        (compare_not_gt_iff_le left right).mpr first
      simp [tested]
    · have tested :
          compare right left != Ordering.gt :=
        (compare_not_gt_iff_le right left).mpr second
      simp [tested]
  have sorted :=
    List.pairwise_mergeSort transitive total blocks
  simpa [sortedSimpleBlocks] using
    (sorted.imp fun relation =>
      (compare_not_gt_iff_le _ _).mp
        (of_decide_eq_true relation))

theorem sortedSimpleBlocks_eq_of_perm
    {left right : List (List Nat)}
    (permutation : left.Perm right) :
    sortedSimpleBlocks left = sortedSimpleBlocks right := by
  have sortedPermutation :
      (sortedSimpleBlocks left).Perm
        (sortedSimpleBlocks right) :=
    (List.mergeSort_perm _ _).trans <|
      permutation.trans (List.mergeSort_perm _ _).symm
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe =>
      List.le_antisymm leftLe rightLe)
    (sortedSimpleBlocks_pairwise left)
    (sortedSimpleBlocks_pairwise right)
    sortedPermutation

private theorem mem_drop_one_iff
    {blocks : List (List Nat)} {block : List Nat}
    (nodup : blocks.Nodup) :
    block ∈ blocks.drop 1 ↔
      block ∈ blocks ∧ block ≠ blocks.headD [] := by
  cases blocks with
  | nil => simp
  | cons first rest =>
      simp only [List.nodup_cons] at nodup
      change
        block ∈ rest ↔
          block ∈ first :: rest ∧ block ≠ first
      constructor
      · intro member
        exact
          ⟨List.mem_cons_of_mem first member,
            fun equality => nodup.1 (equality ▸ member)⟩
      · rintro ⟨member, notFirst⟩
        exact (List.mem_cons.mp member).resolve_left notFirst

private theorem mem_dropLast_iff
    {blocks : List (List Nat)} {block : List Nat}
    (nodup : blocks.Nodup) :
    block ∈ blocks.dropLast ↔
      block ∈ blocks ∧ block ≠ blocks.getLastD [] := by
  revert nodup block
  apply listReverseRec blocks
  · intro block _
    simp
  · intro initial last _ block appendNodup
    have lastNotInitial : last ∉ initial := by
      have data := List.nodup_append.mp appendNodup
      intro member
      exact data.2.2 last member last (by simp) rfl
    rw [List.dropLast_concat, List.getLastD_concat,
      List.mem_append, List.mem_singleton]
    constructor
    · intro member
      refine ⟨Or.inl member, ?_⟩
      intro equality
      subst block
      exact lastNotInitial member
    · rintro ⟨member, notLast⟩
      rcases member with member | equality
      · exact member
      · exact False.elim (notLast equality)

private theorem mem_drop_one_dropLast_iff
    {blocks : List (List Nat)} {block : List Nat}
    (nodup : blocks.Nodup) :
    block ∈ (blocks.drop 1).dropLast ↔
      block ∈ blocks ∧
        block ≠ blocks.headD [] ∧
        block ≠ blocks.getLastD [] := by
  cases blocks with
  | nil => simp
  | cons first rest =>
      simp only [List.nodup_cons] at nodup
      cases rest with
      | nil => simp
      | cons second tail =>
          have tailNodup :
              (second :: tail).Nodup := nodup.2
          change
            block ∈ (second :: tail).dropLast ↔
              block ∈ first :: second :: tail ∧
                block ≠ first ∧
                block ≠ (second :: tail).getLastD []
          rw [mem_dropLast_iff tailNodup]
          constructor
          · rintro ⟨member, notLast⟩
            have notFirst : block ≠ first := by
              intro equality
              subst block
              exact nodup.1 member
            exact
              ⟨List.mem_cons_of_mem first member,
                notFirst, notLast⟩
          · rintro ⟨member, notFirst, notLast⟩
            exact
              ⟨(List.mem_cons.mp member).resolve_left notFirst,
                notLast⟩

/-- Interior blocks are exactly the scanner blocks other than the retained
initial and final blocks. -/
theorem mem_interiorSimpleBlocks_iff
    (letters block : List Nat) :
    block ∈ interiorSimpleBlocks letters ↔
      block ∈ simpleBlocks letters ∧
        block ≠ initialSimpleBlock letters ∧
        block ≠ finalSimpleBlock letters := by
  have blocksNodup :
      (simpleBlocks letters).Nodup :=
    simpleBlocks_nodup letters
  have blocksNonempty :
      ∀ candidate ∈ simpleBlocks letters,
        candidate ≠ [] :=
    simpleBlocks_blocks_nonempty letters
  unfold interiorSimpleBlocks initialSimpleBlock finalSimpleBlock
  split <;> rename_i initialSimple
  · split <;> rename_i finalSimple
    ·
      rw [mem_drop_one_dropLast_iff blocksNodup]
    ·
      rw [mem_drop_one_iff blocksNodup]
      constructor
      · rintro ⟨member, notInitial⟩
        exact
          ⟨member, notInitial,
            blocksNonempty block member⟩
      · exact fun data => ⟨data.1, data.2.1⟩
  · split <;> rename_i finalSimple
    ·
      rw [mem_dropLast_iff blocksNodup]
      constructor
      · rintro ⟨member, notFinal⟩
        exact
          ⟨member, blocksNonempty block member, notFinal⟩
      · exact fun data => ⟨data.1, data.2.2⟩
    ·
      constructor
      · intro member
        exact
          ⟨member, blocksNonempty block member,
            blocksNonempty block member⟩
      · exact And.left

private theorem count_drop_le
    (amount : Nat) (letters : List (List Nat)) (block : List Nat) :
    (letters.drop amount).count block ≤ letters.count block := by
  induction amount generalizing letters with
  | zero => simp
  | succ amount ih =>
      cases letters with
      | nil => simp
      | cons first rest =>
          exact Nat.le_trans
            (ih rest)
            (by
              by_cases equality : first = block
              · subst first
                simp
              · simpa [equality])

private theorem count_dropLast_le
    (letters : List (List Nat)) (block : List Nat) :
    letters.dropLast.count block ≤ letters.count block := by
  induction letters with
  | nil => simp
  | cons first rest ih =>
      cases rest with
      | nil => simp
      | cons second tail =>
          by_cases equality : first = block
          · subst first
            simp
            omega
          · simpa [equality] using ih

private theorem nodup_drop
    (amount : Nat) {letters : List (List Nat)}
    (nodup : letters.Nodup) :
    (letters.drop amount).Nodup := by
  exact (List.drop_sublist amount letters).nodup nodup

private theorem nodup_dropLast
    {letters : List (List Nat)}
    (nodup : letters.Nodup) :
    letters.dropLast.Nodup := by
  exact (List.dropLast_sublist letters).nodup nodup

theorem interiorSimpleBlocks_nodup (letters : List Nat) :
    (interiorSimpleBlocks letters).Nodup := by
  have blocksNodup :
      (simpleBlocks letters).Nodup :=
    simpleBlocks_nodup letters
  unfold interiorSimpleBlocks
  split <;> rename_i initialSimple
  · split <;> rename_i finalSimple
    · exact nodup_dropLast (nodup_drop 1 blocksNodup)
    · exact nodup_drop 1 blocksNodup
  · split <;> rename_i finalSimple
    · exact nodup_dropLast blocksNodup
    · exact blocksNodup

private theorem simpleBlockScan_eq_singleton_of_all_simple
    (whole current remaining : List Nat)
    (combinedNonempty : current.reverse ++ remaining ≠ [])
    (currentSimple :
      ∀ letter ∈ current, whole.count letter = 1)
    (remainingSimple :
      ∀ letter ∈ remaining, whole.count letter = 1) :
    simpleBlockScan whole current remaining =
      [current.reverse ++ remaining] := by
  induction remaining generalizing current with
  | nil =>
      cases current with
      | nil =>
          simp at combinedNonempty
      | cons first rest =>
          simp [simpleBlockScan]
  | cons letter rest ih =>
      have letterSimple :
          whole.count letter = 1 :=
        remainingSimple letter (by simp)
      have extendedSimple :
          ∀ value ∈ letter :: current,
            whole.count value = 1 := by
        intro value member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact letterSimple
        · exact currentSimple value member
      have restSimple :
          ∀ value ∈ rest, whole.count value = 1 := by
        intro value member
        exact remainingSimple value (by simp [member])
      have step :=
        ih (letter :: current) (by simp)
          extendedSimple restSimple
      simpa only [simpleBlockScan, if_pos letterSimple,
        List.reverse_cons, List.append_assoc,
        List.singleton_append] using step

private theorem simpleBlocks_eq_singleton_of_all_simple
    {letters : List Nat}
    (nonempty : letters ≠ [])
    (allSimple :
      ∀ letter ∈ letters, letters.count letter = 1) :
    simpleBlocks letters = [letters] := by
  unfold simpleBlocks
  simpa using
    simpleBlockScan_eq_singleton_of_all_simple
      letters [] letters nonempty (by simp) allSimple

private theorem cappedMultiplicity_eq_two_iff
    (word : Word Nat) (letter : Nat) :
    cappedMultiplicity word letter = 2 ↔
      2 ≤ word.toList.count letter := by
  unfold cappedMultiplicity
  simp only [Nat.min_def]
  split <;> omega

namespace SameSimpleAdjacencySignature

/-- The signature preserves the distinction between simple and multiple
letters. -/
theorem multiple
    {left right : Word Nat}
    (same : SameSimpleAdjacencySignature left right)
    (letter : Nat) :
    2 ≤ left.toList.count letter ↔
      2 ≤ right.toList.count letter := by
  have cappedEqual := same.capped letter
  rw [← cappedMultiplicity_eq_two_iff left letter,
    ← cappedMultiplicity_eq_two_iff right letter,
    cappedEqual]

/-- The sorted multiple-letter support is determined by the signature. -/
theorem sortedMultipleLetters_eq
    {left right : Word Nat}
    (same : SameSimpleAdjacencySignature left right) :
    sortedMultipleLetters left.toList =
      sortedMultipleLetters right.toList := by
  have inputPermutation :
      (multipleLetterInput left.toList).Perm
        (multipleLetterInput right.toList) := by
    rw [List.perm_iff_count]
    intro letter
    rw [(multipleLetterInput_nodup left.toList).count,
      (multipleLetterInput_nodup right.toList).count]
    simp only [multipleLetterInput_mem_iff,
      same.multiple letter]
  have sortedPermutation :
      (sortedMultipleLetters left.toList).Perm
        (sortedMultipleLetters right.toList) :=
    (sortedMultipleLetters_perm_input left.toList).trans <|
      inputPermutation.trans
        (sortedMultipleLetters_perm_input right.toList).symm
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe =>
      Nat.le_antisymm leftLe rightLe)
    (sortedMultipleLetters_pairwise left.toList)
    (sortedMultipleLetters_pairwise right.toList)
    sortedPermutation

/-- Member blocks containing a common simple letter agree literally. -/
private theorem block_eq_of_common_simple
    {left right : Word Nat}
    (same : SameSimpleAdjacencySignature left right)
    {leftBlock rightBlock : List Nat} {letter : Nat}
    (leftMember : leftBlock ∈ simpleBlocks left.toList)
    (rightMember : rightBlock ∈ simpleBlocks right.toList)
    (letterLeft : letter ∈ leftBlock)
    (letterRight : letter ∈ rightBlock) :
    leftBlock = rightBlock := by
  apply block_eq_of_common_letter_and_same_edges
    (simpleBlocks_flatten_nodup left.toList)
    (simpleBlocks_flatten_nodup right.toList)
    leftMember rightMember letterLeft letterRight
  intro source target
  rw [mem_simpleBlocks_edges_iff,
    mem_simpleBlocks_edges_iff]
  exact same.adjacent source target

/-- The complete list of maximal simple blocks is invariant up to
permutation under the simple-adjacency signature. -/
theorem simpleBlocks_perm
    {left right : Word Nat}
    (same : SameSimpleAdjacencySignature left right) :
    (simpleBlocks left.toList).Perm
      (simpleBlocks right.toList) := by
  apply pathSegmentations_perm
    (simpleBlocks_flatten_nodup left.toList)
    (simpleBlocks_flatten_nodup right.toList)
    (simpleBlocks_blocks_nonempty left.toList)
    (simpleBlocks_blocks_nonempty right.toList)
  · intro letter
    rw [mem_simpleBlocks_flatten_iff,
      mem_simpleBlocks_flatten_iff]
    exact same.simple letter
  · intro source target
    rw [mem_simpleBlocks_edges_iff,
      mem_simpleBlocks_edges_iff]
    exact same.adjacent source target

/-- The marked initial simple block is determined by the signature. -/
theorem initialSimpleBlock_eq
    {left right : Word Nat}
    (same : SameSimpleAdjacencySignature left right) :
    initialSimpleBlock left.toList =
      initialSimpleBlock right.toList := by
  by_cases leftSimple : SimpleIn left left.head
  · have leftInitial :
        SimpleInitial left left.head :=
      ⟨leftSimple, rfl⟩
    have rightInitial :
        SimpleInitial right left.head :=
      (same.initial left.head).mp leftInitial
    have headEqual : right.head = left.head :=
      rightInitial.2
    have rightSimpleAtLeft :
        SimpleIn right left.head :=
      rightInitial.1
    have rightSimple :
        SimpleIn right right.head := by
      rwa [headEqual]
    have leftData :=
      initial_block_data left leftSimple
    have rightData :=
      initial_block_data right rightSimple
    apply same.block_eq_of_common_simple
      leftData.1 rightData.1 leftData.2
    simpa [headEqual] using rightData.2
  · have rightNotSimple :
        ¬SimpleIn right right.head := by
      intro rightSimple
      have rightInitial :
          SimpleInitial right right.head :=
        ⟨rightSimple, rfl⟩
      have leftInitial :
          SimpleInitial left right.head :=
        (same.initial right.head).mpr rightInitial
      have headEqual : left.head = right.head :=
        leftInitial.2
      apply leftSimple
      simpa [headEqual] using leftInitial.1
    rw [initialSimpleBlock_toList,
      initialSimpleBlock_toList]
    simp [SimpleIn] at leftSimple rightNotSimple
    simp [leftSimple, rightNotSimple]

/-- The marked final simple block is determined by the signature. -/
theorem finalSimpleBlock_eq
    {left right : Word Nat}
    (same : SameSimpleAdjacencySignature left right) :
    finalSimpleBlock left.toList =
      finalSimpleBlock right.toList := by
  by_cases leftSimple : SimpleIn left left.final
  · have leftFinal :
        SimpleFinal left left.final :=
      ⟨leftSimple, rfl⟩
    have rightFinal :
        SimpleFinal right left.final :=
      (same.final left.final).mp leftFinal
    have finalEqual : right.final = left.final :=
      rightFinal.2
    have rightSimpleAtLeft :
        SimpleIn right left.final :=
      rightFinal.1
    have rightSimple :
        SimpleIn right right.final := by
      rwa [finalEqual]
    have leftData :=
      final_block_data left leftSimple
    have rightData :=
      final_block_data right rightSimple
    apply same.block_eq_of_common_simple
      leftData.1 rightData.1 leftData.2
    simpa [finalEqual] using rightData.2
  · have rightNotSimple :
        ¬SimpleIn right right.final := by
      intro rightSimple
      have rightFinal :
          SimpleFinal right right.final :=
        ⟨rightSimple, rfl⟩
      have leftFinal :
          SimpleFinal left right.final :=
        (same.final right.final).mpr rightFinal
      have finalEqual : left.final = right.final :=
        leftFinal.2
      apply leftSimple
      simpa [finalEqual] using leftFinal.1
    rw [finalSimpleBlock_toList,
      finalSimpleBlock_toList]
    simp [SimpleIn] at leftSimple rightNotSimple
    simp [leftSimple, rightNotSimple]

/-- Deleting the equal endpoint blocks leaves the same multiset of interior
simple blocks. -/
theorem interiorSimpleBlocks_perm
    {left right : Word Nat}
    (same : SameSimpleAdjacencySignature left right) :
    (interiorSimpleBlocks left.toList).Perm
      (interiorSimpleBlocks right.toList) := by
  have leftNodup :=
    interiorSimpleBlocks_nodup left.toList
  have rightNodup :=
    interiorSimpleBlocks_nodup right.toList
  rw [List.perm_iff_count]
  intro block
  rw [leftNodup.count, rightNodup.count]
  have memEq :
      block ∈ interiorSimpleBlocks left.toList ↔
        block ∈ interiorSimpleBlocks right.toList := by
    rw [mem_interiorSimpleBlocks_iff,
      mem_interiorSimpleBlocks_iff,
      same.initialSimpleBlock_eq,
      same.finalSimpleBlock_eq,
      (same.simpleBlocks_perm).mem_iff]
  by_cases member :
      block ∈ interiorSimpleBlocks left.toList
  · have rightMember := memEq.mp member
    simp [member, rightMember]
  · have rightNotMember :
        block ∉ interiorSimpleBlocks right.toList :=
      fun rightMember => member (memEq.mpr rightMember)
    simp [member, rightNotMember]

private theorem toList_eq_of_sortedMultipleLetters_eq_nil
    {left right : Word Nat}
    (same : SameSimpleAdjacencySignature left right)
    (rightEmpty :
      sortedMultipleLetters right.toList = []) :
    left.toList = right.toList := by
  have leftEmpty :
      sortedMultipleLetters left.toList = [] := by
    rw [same.sortedMultipleLetters_eq, rightEmpty]
  have leftAllSimple :
      ∀ letter ∈ left.toList,
        left.toList.count letter = 1 := by
    intro letter member
    have positive :
        1 ≤ left.toList.count letter :=
      List.count_pos_iff.mpr member
    have notMultiple :
        ¬2 ≤ left.toList.count letter := by
      intro multiple
      have listed :=
        (sortedMultipleLetters_mem_iff
          letter left.toList).mpr multiple
      rw [leftEmpty] at listed
      simp at listed
    omega
  have rightAllSimple :
      ∀ letter ∈ right.toList,
        right.toList.count letter = 1 := by
    intro letter member
    have positive :
        1 ≤ right.toList.count letter :=
      List.count_pos_iff.mpr member
    have notMultiple :
        ¬2 ≤ right.toList.count letter := by
      intro multiple
      have listed :=
        (sortedMultipleLetters_mem_iff
          letter right.toList).mpr multiple
      rw [rightEmpty] at listed
      simp at listed
    omega
  have leftBlocks :
      simpleBlocks left.toList = [left.toList] :=
    simpleBlocks_eq_singleton_of_all_simple
      (by
        cases left
        simp [Word.toList])
      leftAllSimple
  have rightBlocks :
      simpleBlocks right.toList = [right.toList] :=
    simpleBlocks_eq_singleton_of_all_simple
      (by
        cases right
        simp [Word.toList])
      rightAllSimple
  have blocksPermutation := same.simpleBlocks_perm
  rw [leftBlocks, rightBlocks] at blocksPermutation
  simpa using blocksPermutation

end SameSimpleAdjacencySignature

/-- The block-level data extracted from two words with one
simple-adjacency signature. -/
structure SameSimpleBlockDecomposition
    (left right : Word Nat) : Prop where
  allBlocks :
    (simpleBlocks left.toList).Perm
      (simpleBlocks right.toList)
  initial :
    initialSimpleBlock left.toList =
      initialSimpleBlock right.toList
  final :
    finalSimpleBlock left.toList =
      finalSimpleBlock right.toList
  interior :
    (interiorSimpleBlocks left.toList).Perm
      (interiorSimpleBlocks right.toList)

namespace SameSimpleAdjacencySignature

/-- Package the four scanner invariants used by the canonical form. -/
theorem blockDecomposition
    {left right : Word Nat}
    (same : SameSimpleAdjacencySignature left right) :
    SameSimpleBlockDecomposition left right :=
  ⟨same.simpleBlocks_perm,
    same.initialSimpleBlock_eq,
    same.finalSimpleBlock_eq,
    same.interiorSimpleBlocks_perm⟩

/-- The canonical list is a function only of the
simple-adjacency signature. -/
theorem canonicalList_eq
    {left right : Word Nat}
    (same : SameSimpleAdjacencySignature left right) :
    simpleAdjacencyCanonicalList left.toList =
      simpleAdjacencyCanonicalList right.toList := by
  have multipleEqual := same.sortedMultipleLetters_eq
  have initialEqual := same.initialSimpleBlock_eq
  have finalEqual := same.finalSimpleBlock_eq
  have sortedInteriorEqual :
      sortedSimpleBlocks
          (interiorSimpleBlocks left.toList) =
        sortedSimpleBlocks
          (interiorSimpleBlocks right.toList) :=
    sortedSimpleBlocks_eq_of_perm
      same.interiorSimpleBlocks_perm
  unfold simpleAdjacencyCanonicalList
  rw [multipleEqual]
  cases multiple :
      sortedMultipleLetters right.toList with
  | nil =>
      simpa only using
        same.toList_eq_of_sortedMultipleLetters_eq_nil
          multiple
  | cons anchor remaining =>
      simp only [initialEqual, sortedInteriorEqual,
        finalEqual]

/-- Public integration theorem: equal simple-adjacency signatures produce
literally equal canonical words. -/
theorem canonicalWord_eq
    {left right : Word Nat}
    (same : SameSimpleAdjacencySignature left right) :
    simpleAdjacencyCanonicalWord left =
      simpleAdjacencyCanonicalWord right := by
  apply Word.toList_injective
  simpa using same.canonicalList_eq

end SameSimpleAdjacencySignature

end SemigroupBasis.CoRoots.S5_107
