import SemigroupBasis.Nonfinite.A2One.FactorizationReconstruction

namespace SemigroupBasis.Nonfinite.A2One

open SemigroupBasis

/-- Two distinct singleton separators divide a word into three
duplicate-free blocks, none of which contains either separator. -/
def TwoSingletonSeparatorNodupFactorization
    (first second : Nat) (letters : List Nat) : Prop :=
  ∃ before middle after,
    letters =
      before ++ first :: (middle ++ second :: after) ∧
      before.Nodup ∧ middle.Nodup ∧ after.Nodup ∧
      first ≠ second ∧
      first ∉ before ∧ first ∉ middle ∧ first ∉ after ∧
      second ∉ before ∧ second ∉ middle ∧ second ∉ after

/-- The displayed separators in a two-singleton factorization each occur
exactly once. -/
theorem twoSingletonSeparatorNodupFactorization_separator_counts
    {first second : Nat} {letters : List Nat}
    (shape :
      TwoSingletonSeparatorNodupFactorization first second letters) :
    letters.count first = 1 ∧ letters.count second = 1 := by
  rcases shape with
    ⟨before, middle, after, split, _beforeNodup, _middleNodup,
      _afterNodup, different, firstNotBefore, firstNotMiddle,
      firstNotAfter, secondNotBefore, secondNotMiddle,
      secondNotAfter⟩
  rw [split]
  constructor
  · simp [List.count_eq_zero.mpr firstNotBefore,
      List.count_eq_zero.mpr firstNotMiddle,
      List.count_eq_zero.mpr firstNotAfter, Ne.symm different]
  · simp [List.count_eq_zero.mpr secondNotBefore,
      List.count_eq_zero.mpr secondNotMiddle,
      List.count_eq_zero.mpr secondNotAfter, different]

private theorem word_toList_map
    (word : Word Nat) (rename : Nat → Nat) :
    (word.map rename).toList = word.toList.map rename := by
  cases word
  rfl

private theorem adjacentPairsFrom_map
    (rename : Nat → Nat) :
    ∀ previous letters,
      Word.adjacentPairsFrom (rename previous) (letters.map rename) =
        (Word.adjacentPairsFrom previous letters).map
          (fun edge => (rename edge.1, rename edge.2))
  | _, [] => rfl
  | previous, next :: rest => by
      simp [Word.adjacentPairsFrom,
        adjacentPairsFrom_map rename next rest]

private theorem adjacentPairsList_map
    (letters : List Nat) (rename : Nat → Nat) :
    adjacentPairsList (letters.map rename) =
      (adjacentPairsList letters).map
        (fun edge => (rename edge.1, rename edge.2)) := by
  cases letters with
  | nil => rfl
  | cons first rest =>
      simpa [adjacentPairsList] using
        adjacentPairsFrom_map rename first rest

private theorem sameMarkedDigraphList_map
    {left right : List Nat}
    (rename : Nat → Nat)
    (same : SameMarkedDigraphList left right) :
    SameMarkedDigraphList (left.map rename) (right.map rename) := by
  constructor
  · simpa using congrArg (Option.map rename) same.1
  constructor
  · simpa using congrArg (Option.map rename) same.2.1
  constructor
  · intro letter
    constructor
    · intro member
      rcases List.mem_map.mp member with
        ⟨preimage, preimageMember, rfl⟩
      exact List.mem_map.mpr
        ⟨preimage,
          (same.2.2.1 preimage).mp preimageMember, rfl⟩
    · intro member
      rcases List.mem_map.mp member with
        ⟨preimage, preimageMember, rfl⟩
      exact List.mem_map.mpr
        ⟨preimage,
          (same.2.2.1 preimage).mpr preimageMember, rfl⟩
  · intro source target
    rw [adjacentPairsList_map, adjacentPairsList_map]
    constructor
    · intro member
      rcases List.mem_map.mp member with
        ⟨edge, edgeMember, edgeEquality⟩
      have rightEdge :
          edge ∈ adjacentPairsList right := by
        simpa using
          (same.2.2.2 edge.1 edge.2).mp
            (by simpa using edgeMember)
      exact List.mem_map.mpr
        ⟨edge, rightEdge, edgeEquality⟩
    · intro member
      rcases List.mem_map.mp member with
        ⟨edge, edgeMember, edgeEquality⟩
      have leftEdge :
          edge ∈ adjacentPairsList left := by
        simpa using
          (same.2.2.2 edge.1 edge.2).mpr
            (by simpa using edgeMember)
      exact List.mem_map.mpr
        ⟨edge, leftEdge, edgeEquality⟩

private theorem filter_map_commute
    (letters : List Nat) (rename : Nat → Nat) (keep : Nat → Bool) :
    (letters.map rename).filter keep =
      (letters.filter (fun letter => keep (rename letter))).map rename := by
  induction letters with
  | nil => rfl
  | cons first rest ih =>
      by_cases kept : keep (rename first)
      · simp [kept, ih]
      · simp [kept, ih]

private theorem sameDeletionMarkedDigraph_map
    {left right : Word Nat}
    (rename : Nat → Nat)
    (same : SameDeletionMarkedDigraph left right) :
    SameDeletionMarkedDigraph (left.map rename) (right.map rename) := by
  intro keep
  rw [word_toList_map, word_toList_map,
    filter_map_commute, filter_map_commute]
  exact
    sameMarkedDigraphList_map rename
      (same (fun letter => keep (rename letter)))

private def collapseSecond
    (first second letter : Nat) : Nat :=
  if letter = second then first else letter

private theorem map_collapseSecond_eq_self
    (first second : Nat) {letters : List Nat}
    (secondAbsent : second ∉ letters) :
    letters.map (collapseSecond first second) = letters := by
  calc
    letters.map (collapseSecond first second) =
        letters.map id := by
      apply List.map_congr_left
      intro letter member
      have different : letter ≠ second := by
        intro equality
        subst letter
        exact secondAbsent member
      simp [collapseSecond, different]
    _ = letters := List.map_id letters

private theorem count_map_collapseSecond
    {first second : Nat}
    (different : first ≠ second) :
    ∀ letters : List Nat,
      (letters.map (collapseSecond first second)).count first =
        letters.count first + letters.count second
  | [] => by simp
  | letter :: rest => by
      by_cases firstEquality : letter = first
      · subst letter
        simp [collapseSecond, different,
          count_map_collapseSecond different rest]
        omega
      · by_cases secondEquality : letter = second
        · subst letter
          simp [collapseSecond, Ne.symm different,
            count_map_collapseSecond different rest]
          omega
        · simp [collapseSecond, firstEquality, secondEquality,
            count_map_collapseSecond different rest]

private theorem pairFilter_eq_nil_of_absent
    (letters : List Nat) (first second : Nat)
    (firstAbsent : first ∉ letters)
    (secondAbsent : second ∉ letters) :
    letters.filter
        (fun value => value == first || value == second) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro letter member
  have firstDifferent : letter ≠ first := by
    intro equality
    subst letter
    exact firstAbsent member
  have secondDifferent : letter ≠ second := by
    intro equality
    subst letter
    exact secondAbsent member
  simpa only [Bool.or_eq_true, beq_iff_eq, not_or] using
    And.intro firstDifferent secondDifferent

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

private theorem length_eq_two_counts_of_mem
    {first second : Nat} {letters : List Nat}
    (different : first ≠ second)
    (only :
      ∀ letter, letter ∈ letters →
        letter = first ∨ letter = second) :
    letters.length =
      letters.count first + letters.count second := by
  induction letters with
  | nil => simp
  | cons head tail ih =>
      have headCases :
          head = first ∨ head = second :=
        only head (by simp)
      have tailOnly :
          ∀ letter, letter ∈ tail →
            letter = first ∨ letter = second := by
        intro letter member
        exact only letter (by simp [member])
      simp only [List.length_cons, List.count_cons]
      rw [ih tailOnly]
      rcases headCases with equality | equality
      · subst head
        simp [different]
        omega
      · subst head
        simp [Ne.symm different]
        omega

private theorem list_eq_pair_of_length_head_last
    {letters : List Nat} {first second : Nat}
    (lengthTwo : letters.length = 2)
    (headFirst : letters.head? = some first)
    (lastSecond : letters.getLast? = some second) :
    letters = [first, second] := by
  cases letters with
  | nil => simp at lengthTwo
  | cons head tail =>
      cases tail with
      | nil => simp at lengthTwo
      | cons last rest =>
          have restLengthZero : rest.length = 0 := by
            simp only [List.length_cons] at lengthTwo
            omega
          have restEmpty : rest = [] :=
            List.eq_nil_of_length_eq_zero restLengthZero
          subst rest
          have headEquality : head = first := by
            simpa using headFirst
          have lastEquality : last = second := by
            simpa using lastSecond
          subst head
          subst last
          rfl

private theorem exists_one_occurrence_split_of_count_eq_one
    {α : Type} [DecidableEq α]
    {letters : List α} {letter : α}
    (countOne : letters.count letter = 1) :
    ∃ before after,
      letter ∉ before ∧
        letter ∉ after ∧
          letters = before ++ letter :: after := by
  induction letters with
  | nil => simp at countOne
  | cons first rest ih =>
      by_cases equality : first = letter
      · subst first
        have restCountZero : rest.count letter = 0 := by
          simp only [List.count_cons_self] at countOne
          omega
        exact
          ⟨[], rest, by simp,
            List.count_eq_zero.mp restCountZero, by simp⟩
      · have restCountOne : rest.count letter = 1 := by
          simpa [equality] using countOne
        obtain ⟨before, after, notBefore, notAfter, split⟩ :=
          ih restCountOne
        exact
          ⟨first :: before, after,
            by simp [Ne.symm equality, notBefore],
            notAfter, by simp [split]⟩

private theorem append_cons_eq_append_cons_of_not_mem
    {α : Type} [DecidableEq α] {separator : α} :
    ∀ {left right leftTail rightTail : List α},
      separator ∉ left →
      separator ∉ right →
      left ++ separator :: leftTail =
        right ++ separator :: rightTail →
      left = right ∧ leftTail = rightTail
  | [], [], leftTail, rightTail, _, _, equality => by
      simpa using equality
  | [], rightHead :: right, leftTail, rightTail, _,
      separatorNotRight, equality => by
      have separatorNeRightHead : separator ≠ rightHead := by
        intro separatorEq
        subst rightHead
        exact separatorNotRight (by simp)
      have headsEqual : separator = rightHead := by
        simpa using congrArg List.head? equality
      exact False.elim (separatorNeRightHead headsEqual)
  | leftHead :: left, [], leftTail, rightTail,
      separatorNotLeft, _, equality => by
      have separatorNeLeftHead : separator ≠ leftHead := by
        intro separatorEq
        subst leftHead
        exact separatorNotLeft (by simp)
      have headsEqual : leftHead = separator := by
        simpa using congrArg List.head? equality
      exact False.elim (separatorNeLeftHead headsEqual.symm)
  | leftHead :: left, rightHead :: right, leftTail, rightTail,
      separatorNotLeft, separatorNotRight, equality => by
      have leftAbsence :
          separator ≠ leftHead ∧ separator ∉ left := by
        simpa only [List.mem_cons, not_or] using separatorNotLeft
      have rightAbsence :
          separator ≠ rightHead ∧ separator ∉ right := by
        simpa only [List.mem_cons, not_or] using separatorNotRight
      have consEquality :
          leftHead = rightHead ∧
            left ++ separator :: leftTail =
              right ++ separator :: rightTail := by
        simpa only [List.cons_append, List.cons.injEq] using equality
      rcases consEquality with ⟨rfl, restEquality⟩
      have tailEquality :=
        append_cons_eq_append_cons_of_not_mem
          leftAbsence.2 rightAbsence.2 restEquality
      exact
        ⟨congrArg (List.cons leftHead) tailEquality.1,
          tailEquality.2⟩

/-- Two distinct singleton separators with duplicate-free intervening blocks
determine the word from its complete deletion marked-digraph family. -/
theorem twoSingletonSeparatorNodupFactorization_rigid
    {first second : Nat} {left right : Word Nat}
    (leftShape :
      TwoSingletonSeparatorNodupFactorization
        first second left.toList)
    (same : SameDeletionMarkedDigraph left right) :
    right = left := by
  rcases leftShape with
    ⟨leftBefore, leftMiddle, leftAfter, leftSplit,
      leftBeforeNodup, leftMiddleNodup, leftAfterNodup,
      different, firstNotLeftBefore, firstNotLeftMiddle,
      firstNotLeftAfter, secondNotLeftBefore,
      secondNotLeftMiddle, secondNotLeftAfter⟩
  have leftCounts :
      left.toList.count first = 1 ∧
        left.toList.count second = 1 :=
    twoSingletonSeparatorNodupFactorization_separator_counts
      ⟨leftBefore, leftMiddle, leftAfter, leftSplit,
        leftBeforeNodup, leftMiddleNodup, leftAfterNodup,
        different, firstNotLeftBefore, firstNotLeftMiddle,
        firstNotLeftAfter, secondNotLeftBefore,
        secondNotLeftMiddle, secondNotLeftAfter⟩
  have rightFirstCount : right.toList.count first = 1 :=
    (sameDeletionMarkedDigraph_count_eq_one_iff
      same first).mp leftCounts.1
  have rightSecondCount : right.toList.count second = 1 :=
    (sameDeletionMarkedDigraph_count_eq_one_iff
      same second).mp leftCounts.2
  let keep :=
    fun value : Nat =>
      value == first || value == second
  have leftBeforeProjection :
      leftBefore.filter keep = [] := by
    simpa only [keep] using
      pairFilter_eq_nil_of_absent leftBefore first second
        firstNotLeftBefore secondNotLeftBefore
  have leftMiddleProjection :
      leftMiddle.filter keep = [] := by
    simpa only [keep] using
      pairFilter_eq_nil_of_absent leftMiddle first second
        firstNotLeftMiddle secondNotLeftMiddle
  have leftAfterProjection :
      leftAfter.filter keep = [] := by
    simpa only [keep] using
      pairFilter_eq_nil_of_absent leftAfter first second
        firstNotLeftAfter secondNotLeftAfter
  have leftPairProjection :
      left.toList.filter keep = [first, second] := by
    rw [leftSplit, List.filter_append, List.filter_cons,
      List.filter_append, List.filter_cons,
      leftBeforeProjection, leftMiddleProjection,
      leftAfterProjection]
    simp [keep]
  have rightPairOnly :
      ∀ letter, letter ∈ right.toList.filter keep →
        letter = first ∨ letter = second := by
    intro letter member
    have kept := (List.mem_filter.mp member).2
    simpa only [keep, Bool.or_eq_true, beq_iff_eq] using kept
  have rightPairFirstCount :
      (right.toList.filter keep).count first = 1 := by
    calc
      (right.toList.filter keep).count first =
          right.toList.count first :=
        count_filter_of_kept right.toList keep first (by simp [keep])
      _ = 1 := rightFirstCount
  have rightPairSecondCount :
      (right.toList.filter keep).count second = 1 := by
    calc
      (right.toList.filter keep).count second =
          right.toList.count second :=
        count_filter_of_kept right.toList keep second (by simp [keep])
      _ = 1 := rightSecondCount
  have rightPairLength :
      (right.toList.filter keep).length = 2 := by
    calc
      (right.toList.filter keep).length =
          (right.toList.filter keep).count first +
            (right.toList.filter keep).count second :=
        length_eq_two_counts_of_mem different rightPairOnly
      _ = 2 := by
        rw [rightPairFirstCount, rightPairSecondCount]
  have markedPair := same keep
  have rightPairHead :
      (right.toList.filter keep).head? = some first := by
    calc
      (right.toList.filter keep).head? =
          (left.toList.filter keep).head? := markedPair.1.symm
      _ = some first := by simp [leftPairProjection]
  have rightPairLast :
      (right.toList.filter keep).getLast? = some second := by
    calc
      (right.toList.filter keep).getLast? =
          (left.toList.filter keep).getLast? := markedPair.2.1.symm
      _ = some second := by simp [leftPairProjection]
  have rightPairProjection :
      right.toList.filter keep = [first, second] :=
    list_eq_pair_of_length_head_last
      rightPairLength rightPairHead rightPairLast
  let rename := collapseSecond first second
  have leftBeforeMap :
      leftBefore.map rename = leftBefore := by
    exact
      map_collapseSecond_eq_self first second
        secondNotLeftBefore
  have leftMiddleMap :
      leftMiddle.map rename = leftMiddle := by
    exact
      map_collapseSecond_eq_self first second
        secondNotLeftMiddle
  have leftAfterMap :
      leftAfter.map rename = leftAfter := by
    exact
      map_collapseSecond_eq_self first second
        secondNotLeftAfter
  have mappedLeftSplit :
      (left.map rename).toList =
        leftBefore ++ first ::
          (leftMiddle ++ first :: leftAfter) := by
    rw [word_toList_map, leftSplit, List.map_append,
      List.map_cons, List.map_append, List.map_cons,
      leftBeforeMap, leftMiddleMap, leftAfterMap]
    simp [rename, collapseSecond, different]
  have mappedLeftShape :
      TwoSeparatorNodupFactorization
        first (left.map rename).toList :=
    ⟨leftBefore, leftMiddle, leftAfter, mappedLeftSplit,
      leftBeforeNodup, leftMiddleNodup, leftAfterNodup,
      firstNotLeftBefore, firstNotLeftMiddle,
      firstNotLeftAfter⟩
  have mappedSame :
      SameDeletionMarkedDigraph
        (left.map rename) (right.map rename) :=
    sameDeletionMarkedDigraph_map rename same
  have mappedRightCount :
      (right.map rename).toList.count first = 2 := by
    calc
      (right.map rename).toList.count first =
          (right.toList.map rename).count first := by
        rw [word_toList_map]
      _ = right.toList.count first +
          right.toList.count second := by
        exact count_map_collapseSecond different right.toList
      _ = 2 := by
        rw [rightFirstCount, rightSecondCount]
  have mappedEquality :
      right.map rename = left.map rename :=
    twoSeparatorNodupFactorization_rigid
      mappedLeftShape mappedSame mappedRightCount
  have collapsedLists :
      right.toList.map rename =
        left.toList.map rename := by
    have listed := congrArg Word.toList mappedEquality
    simpa only [word_toList_map] using listed
  obtain
    ⟨rightBefore, rightTail, firstNotRightBefore,
      firstNotRightTail, rightFirstSplit⟩ :=
    exists_one_occurrence_split_of_count_eq_one rightFirstCount
  have rightPairExpanded :
      rightBefore.filter keep ++
          first :: rightTail.filter keep =
        [] ++ first :: [second] := by
    calc
      rightBefore.filter keep ++
          first :: rightTail.filter keep =
          right.toList.filter keep := by
        rw [rightFirstSplit, List.filter_append, List.filter_cons]
        simp [keep]
      _ = [first, second] := rightPairProjection
      _ = [] ++ first :: [second] := by rfl
  have firstNotRightBeforeProjection :
      first ∉ rightBefore.filter keep := by
    intro member
    exact firstNotRightBefore (List.mem_filter.mp member).1
  have rightPairSplit :=
    append_cons_eq_append_cons_of_not_mem
      firstNotRightBeforeProjection (by simp)
      rightPairExpanded
  have secondNotRightBefore : second ∉ rightBefore := by
    intro member
    have filteredMember :
        second ∈ rightBefore.filter keep :=
      List.mem_filter.mpr ⟨member, by simp [keep]⟩
    rw [rightPairSplit.1] at filteredMember
    simp at filteredMember
  have rightTailSecondCount :
      rightTail.count second = 1 := by
    rw [rightFirstSplit, List.count_append,
      List.count_cons] at rightSecondCount
    simp [List.count_eq_zero.mpr secondNotRightBefore,
      different] at rightSecondCount
    exact rightSecondCount
  obtain
    ⟨rightMiddle, rightAfter, secondNotRightMiddle,
      secondNotRightAfter, rightTailSplit⟩ :=
    exists_one_occurrence_split_of_count_eq_one
      rightTailSecondCount
  have firstNotRightMiddle : first ∉ rightMiddle := by
    intro member
    apply firstNotRightTail
    rw [rightTailSplit]
    simp [member]
  have firstNotRightAfter : first ∉ rightAfter := by
    intro member
    apply firstNotRightTail
    rw [rightTailSplit]
    simp [member]
  have rightSplit :
      right.toList =
        rightBefore ++ first ::
          (rightMiddle ++ second :: rightAfter) := by
    rw [rightFirstSplit, rightTailSplit]
  have rightBeforeMap :
      rightBefore.map rename = rightBefore :=
    map_collapseSecond_eq_self first second
      secondNotRightBefore
  have rightMiddleMap :
      rightMiddle.map rename = rightMiddle :=
    map_collapseSecond_eq_self first second
      secondNotRightMiddle
  have rightAfterMap :
      rightAfter.map rename = rightAfter :=
    map_collapseSecond_eq_self first second
      secondNotRightAfter
  have collapsedExpanded :
      rightBefore ++ first ::
          (rightMiddle ++ first :: rightAfter) =
        leftBefore ++ first ::
          (leftMiddle ++ first :: leftAfter) := by
    calc
      rightBefore ++ first ::
          (rightMiddle ++ first :: rightAfter) =
          right.toList.map rename := by
        rw [rightSplit, List.map_append, List.map_cons,
          List.map_append, List.map_cons,
          rightBeforeMap, rightMiddleMap, rightAfterMap]
        simp [rename, collapseSecond, different]
      _ = left.toList.map rename := collapsedLists
      _ = leftBefore ++ first ::
          (leftMiddle ++ first :: leftAfter) := by
        rw [leftSplit, List.map_append, List.map_cons,
          List.map_append, List.map_cons,
          leftBeforeMap, leftMiddleMap, leftAfterMap]
        simp [rename, collapseSecond, different]
  have firstDelimiterSplit :=
    append_cons_eq_append_cons_of_not_mem
      firstNotRightBefore firstNotLeftBefore collapsedExpanded
  have secondDelimiterSplit :=
    append_cons_eq_append_cons_of_not_mem
      firstNotRightMiddle firstNotLeftMiddle
      firstDelimiterSplit.2
  apply Word.toList_injective
  rw [rightSplit, leftSplit, firstDelimiterSplit.1,
    secondDelimiterSplit.1, secondDelimiterSplit.2]

private theorem nodup_of_flatMap_nodup_local
    (source : List Nat) (images : Nat → List Nat)
    (imageNonempty : ∀ letter, images letter ≠ [])
    (mappedNodup : (source.flatMap images).Nodup) :
    source.Nodup := by
  rw [List.nodup_iff_count]
  intro sourceLetter
  obtain ⟨marker, markerMember⟩ :=
    List.exists_mem_of_ne_nil
      (images sourceLetter) (imageNonempty sourceLetter)
  have contribution :=
    count_le_flatMap_count_of_mem source images
      sourceLetter marker markerMember
  have mappedBound :=
    List.nodup_iff_count.mp mappedNodup marker
  omega

/-- A triple-occurring source variable exposes either one twice-occurring
owner of both anchor separators or two distinct singleton separator owners
whose occurrences divide the source into duplicate-free blocks. -/
theorem preimage_three_occurrence_separator_factorization_cases
    {bound : Nat} {word : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    {sourceLetter : Nat}
    (sourceCount : word.toList.count sourceLetter = 3) :
    (∃ owner,
      word.toList.count owner = 2 ∧
        3 * bound + 2 ∈ (substitution owner).toList) ∨
      ∃ first second,
        TwoSingletonSeparatorNodupFactorization
          first second word.toList := by
  obtain
    ⟨before, middleFirst, middleSecond, after,
      firstOwner, secondOwner, sourceSplit,
      sourceNotBefore, sourceNotMiddleFirst,
      sourceNotMiddleSecond, sourceNotAfter,
      firstOwnerMember, firstSeparatorMember,
      secondOwnerMember, secondSeparatorMember, ownerCases⟩ :=
    preimage_three_occurrence_separator_owners
      mapped sourceCount
  rcases ownerCases with
    ⟨ownersEqual, firstOwnerCount⟩ |
      ⟨ownersDifferent, firstOwnerCount, secondOwnerCount⟩
  · subst secondOwner
    exact
      Or.inl
        ⟨firstOwner, firstOwnerCount, firstSeparatorMember⟩
  · have sourceNeFirstOwner : sourceLetter ≠ firstOwner := by
      intro equality
      subst firstOwner
      exact sourceNotMiddleFirst firstOwnerMember
    have sourceNeSecondOwner : sourceLetter ≠ secondOwner := by
      intro equality
      subst secondOwner
      exact sourceNotMiddleSecond secondOwnerMember
    have firstMiddleCount :
        middleFirst.count firstOwner = 1 := by
      have expanded := firstOwnerCount
      rw [sourceSplit] at expanded
      simp only [List.count_append, List.count_cons] at expanded
      have positive :
          1 ≤ middleFirst.count firstOwner :=
        List.count_pos_iff.mpr firstOwnerMember
      simp [sourceNeFirstOwner] at expanded
      omega
    have secondMiddleCount :
        middleSecond.count secondOwner = 1 := by
      have expanded := secondOwnerCount
      rw [sourceSplit] at expanded
      simp only [List.count_append, List.count_cons] at expanded
      have positive :
          1 ≤ middleSecond.count secondOwner :=
        List.count_pos_iff.mpr secondOwnerMember
      simp [sourceNeSecondOwner] at expanded
      omega
    obtain
      ⟨firstBefore, firstAfter, firstNotBefore,
        firstNotAfter, firstMiddleSplit⟩ :=
      exists_one_occurrence_split_of_count_eq_one
        firstMiddleCount
    obtain
      ⟨secondBefore, secondAfter, secondNotBefore,
        secondNotAfter, secondMiddleSplit⟩ :=
      exists_one_occurrence_split_of_count_eq_one
        secondMiddleCount
    let sourceBefore :=
      before ++ sourceLetter :: firstBefore
    let sourceMiddle :=
      firstAfter ++ sourceLetter :: secondBefore
    let sourceAfter :=
      secondAfter ++ sourceLetter :: after
    have sourceOwnerSplit :
        word.toList =
          sourceBefore ++ firstOwner ::
            (sourceMiddle ++ secondOwner :: sourceAfter) := by
      dsimp only [sourceBefore, sourceMiddle, sourceAfter]
      rw [sourceSplit, firstMiddleSplit, secondMiddleSplit]
      simp [List.append_assoc]
    have firstBlockCountEquation := firstOwnerCount
    rw [sourceOwnerSplit] at firstBlockCountEquation
    simp only [List.count_append, List.count_cons] at firstBlockCountEquation
    simp [Ne.symm ownersDifferent] at firstBlockCountEquation
    have firstSourceBeforeZero :
        sourceBefore.count firstOwner = 0 := by
      omega
    have firstSourceMiddleZero :
        sourceMiddle.count firstOwner = 0 := by
      omega
    have firstSourceAfterZero :
        sourceAfter.count firstOwner = 0 := by
      omega
    have secondBlockCountEquation := secondOwnerCount
    rw [sourceOwnerSplit] at secondBlockCountEquation
    simp only [List.count_append, List.count_cons] at secondBlockCountEquation
    simp [ownersDifferent] at secondBlockCountEquation
    have secondSourceBeforeZero :
        sourceBefore.count secondOwner = 0 := by
      omega
    have secondSourceMiddleZero :
        sourceMiddle.count secondOwner = 0 := by
      omega
    have secondSourceAfterZero :
        sourceAfter.count secondOwner = 0 := by
      omega
    have firstNotSourceBefore : firstOwner ∉ sourceBefore :=
      List.count_eq_zero.mp firstSourceBeforeZero
    have firstNotSourceMiddle : firstOwner ∉ sourceMiddle :=
      List.count_eq_zero.mp firstSourceMiddleZero
    have firstNotSourceAfter : firstOwner ∉ sourceAfter :=
      List.count_eq_zero.mp firstSourceAfterZero
    have secondNotSourceBefore : secondOwner ∉ sourceBefore :=
      List.count_eq_zero.mp secondSourceBeforeZero
    have secondNotSourceMiddle : secondOwner ∉ sourceMiddle :=
      List.count_eq_zero.mp secondSourceMiddleZero
    have secondNotSourceAfter : secondOwner ∉ sourceAfter :=
      List.count_eq_zero.mp secondSourceAfterZero
    let separator := 3 * bound + 2
    let images :=
      fun letter : Nat => (substitution letter).toList
    have firstSeparatorImageMember :
        separator ∈ images firstOwner := by
      simpa only [separator, images] using firstSeparatorMember
    have secondSeparatorImageMember :
        separator ∈ images secondOwner := by
      simpa only [separator, images] using secondSeparatorMember
    have mappedList :
        word.toList.flatMap images =
          (anchor (3 * bound)).toList := by
      have listed := congrArg Word.toList mapped
      rw [Word.toList_bind] at listed
      simpa only [images] using listed
    have separatorCountEquation :=
      congrArg (List.count separator) mappedList
    rw [sourceOwnerSplit] at separatorCountEquation
    simp only [List.flatMap_append, List.flatMap_cons,
      List.count_append] at separatorCountEquation
    have anchorSeparatorCount :
        (anchor (3 * bound)).toList.count separator = 2 := by
      simpa only [separator] using
        anchor_separator_count_eq_two (3 * bound)
    rw [anchorSeparatorCount] at separatorCountEquation
    have firstImagePositive :
        1 ≤ (images firstOwner).count separator :=
      List.count_pos_iff.mpr firstSeparatorImageMember
    have secondImagePositive :
        1 ≤ (images secondOwner).count separator :=
      List.count_pos_iff.mpr secondSeparatorImageMember
    have firstImageCount :
        (images firstOwner).count separator = 1 := by
      omega
    have secondImageCount :
        (images secondOwner).count separator = 1 := by
      omega
    have sourceBeforeImageCount :
        (sourceBefore.flatMap images).count separator = 0 := by
      omega
    have sourceMiddleImageCount :
        (sourceMiddle.flatMap images).count separator = 0 := by
      omega
    have sourceAfterImageCount :
        (sourceAfter.flatMap images).count separator = 0 := by
      omega
    obtain
      ⟨firstImageBefore, firstImageAfter,
        separatorNotFirstImageBefore,
        separatorNotFirstImageAfter, firstImageSplit⟩ :=
      exists_one_occurrence_split_of_count_eq_one
        firstImageCount
    obtain
      ⟨secondImageBefore, secondImageAfter,
        separatorNotSecondImageBefore,
        separatorNotSecondImageAfter, secondImageSplit⟩ :=
      exists_one_occurrence_split_of_count_eq_one
        secondImageCount
    have separatorNotSourceBeforeImage :
        separator ∉ sourceBefore.flatMap images :=
      List.count_eq_zero.mp sourceBeforeImageCount
    have separatorNotSourceMiddleImage :
        separator ∉ sourceMiddle.flatMap images :=
      List.count_eq_zero.mp sourceMiddleImageCount
    have separatorNotSourceAfterImage :
        separator ∉ sourceAfter.flatMap images :=
      List.count_eq_zero.mp sourceAfterImageCount
    have expandedMapping :
        (sourceBefore.flatMap images ++ firstImageBefore) ++
            separator ::
              ((firstImageAfter ++ sourceMiddle.flatMap images ++
                  secondImageBefore) ++
                separator ::
                  (secondImageAfter ++
                    sourceAfter.flatMap images)) =
          List.range separator ++
            separator ::
              ((List.range separator).reverse ++
                separator :: List.range separator) := by
      calc
        _ = word.toList.flatMap images := by
          rw [sourceOwnerSplit]
          simp only [List.flatMap_append, List.flatMap_cons]
          rw [firstImageSplit, secondImageSplit]
          simp [List.append_assoc]
        _ = (anchor (3 * bound)).toList := mappedList
        _ = _ := by
          rw [anchor_toList]
          simp [separator, List.append_assoc]
    have separatorNotFirstBlock :
        separator ∉
          sourceBefore.flatMap images ++ firstImageBefore := by
      simp [separatorNotSourceBeforeImage,
        separatorNotFirstImageBefore]
    have separatorNotMiddleBlock :
        separator ∉
          firstImageAfter ++ sourceMiddle.flatMap images ++
            secondImageBefore := by
      simp [separatorNotFirstImageAfter,
        separatorNotSourceMiddleImage,
        separatorNotSecondImageBefore]
    have separatorNotAfterBlock :
        separator ∉
          secondImageAfter ++ sourceAfter.flatMap images := by
      simp [separatorNotSecondImageAfter,
        separatorNotSourceAfterImage]
    have separatorNotForward :
        separator ∉ List.range separator := by
      simp
    have separatorNotReverse :
        separator ∉ (List.range separator).reverse := by
      simp
    have firstDelimiterSplit :=
      append_cons_eq_append_cons_of_not_mem
        separatorNotFirstBlock separatorNotForward
        expandedMapping
    have secondDelimiterSplit :=
      append_cons_eq_append_cons_of_not_mem
        separatorNotMiddleBlock separatorNotReverse
        firstDelimiterSplit.2
    have firstCombinedNodup :
        (sourceBefore.flatMap images ++
          firstImageBefore).Nodup := by
      rw [firstDelimiterSplit.1]
      exact List.nodup_range
    have middleCombinedNodup :
        (firstImageAfter ++ sourceMiddle.flatMap images ++
          secondImageBefore).Nodup := by
      rw [secondDelimiterSplit.1]
      exact
        (List.reverse_perm
          (List.range separator)).nodup_iff.mpr
            List.nodup_range
    have afterCombinedNodup :
        (secondImageAfter ++
          sourceAfter.flatMap images).Nodup := by
      rw [secondDelimiterSplit.2]
      exact List.nodup_range
    have sourceBeforeImageNodup :
        (sourceBefore.flatMap images).Nodup :=
      (List.nodup_append.mp firstCombinedNodup).1
    have firstMiddleCombinedNodup :
        (firstImageAfter ++
          sourceMiddle.flatMap images).Nodup :=
      (List.nodup_append.mp middleCombinedNodup).1
    have sourceMiddleImageNodup :
        (sourceMiddle.flatMap images).Nodup :=
      (List.nodup_append.mp firstMiddleCombinedNodup).2.1
    have sourceAfterImageNodup :
        (sourceAfter.flatMap images).Nodup :=
      (List.nodup_append.mp afterCombinedNodup).2.1
    have imageNonempty :
        ∀ letter, images letter ≠ [] := by
      intro letter
      cases substitution letter
      simp [images, Word.toList]
    have sourceBeforeNodup : sourceBefore.Nodup :=
      nodup_of_flatMap_nodup_local sourceBefore images
        imageNonempty sourceBeforeImageNodup
    have sourceMiddleNodup : sourceMiddle.Nodup :=
      nodup_of_flatMap_nodup_local sourceMiddle images
        imageNonempty sourceMiddleImageNodup
    have sourceAfterNodup : sourceAfter.Nodup :=
      nodup_of_flatMap_nodup_local sourceAfter images
        imageNonempty sourceAfterImageNodup
    exact
      Or.inr
        ⟨firstOwner, secondOwner,
          sourceBefore, sourceMiddle, sourceAfter,
          sourceOwnerSplit, sourceBeforeNodup,
          sourceMiddleNodup, sourceAfterNodup,
          ownersDifferent, firstNotSourceBefore,
          firstNotSourceMiddle, firstNotSourceAfter,
          secondNotSourceBefore, secondNotSourceMiddle,
          secondNotSourceAfter⟩

/-- Every preimage of a Trahtman anchor is reconstructible from the complete
deletion marked-digraph family once the competing occurrence counts are
known exactly. -/
theorem preimage_exactCountRigidityCertificate
    {bound : Nat} {word : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound)) :
    ExactCountRigidityCertificate word := by
  intro other same exactCounts
  by_cases hasThree :
      ∃ sourceLetter,
        word.toList.count sourceLetter = 3
  · obtain ⟨sourceLetter, sourceCount⟩ := hasThree
    rcases
      preimage_three_occurrence_separator_factorization_cases
        mapped sourceCount with
      ownerCase | singletonCase
    · obtain
        ⟨owner, ownerCount, separatorMember⟩ :=
        ownerCase
      have otherOwnerCount :
          other.toList.count owner = 2 := by
        calc
          other.toList.count owner =
              word.toList.count owner :=
            exactCounts owner
          _ = 2 := ownerCount
      exact
        preimage_two_occurrence_separator_owner_rigid
          mapped same ownerCount separatorMember
          otherOwnerCount
    · obtain ⟨first, second, shape⟩ := singletonCase
      exact
        twoSingletonSeparatorNodupFactorization_rigid
          shape same
  · have noThree :
        ∀ letter, letter ∈ word.toList →
          word.toList.count letter ≠ 3 := by
      intro letter _member countThree
      exact hasThree ⟨letter, countThree⟩
    exact
      (preimage_exactCountRigidityCertificate_of_no_three_occurrence
        mapped noThree) other same exactCounts

/-- Uniform exact-count reconstruction is now complete for all bounded
anchor preimages.  The variable bound is relevant to Trahtman's endpoint,
but the reconstruction proof itself only needs the displayed anchor
factorization. -/
theorem anchorPreimageExactCountRigidity :
    AnchorPreimageExactCountRigidity := by
  intro bound word _uses substitution mapped
  exact preimage_exactCountRigidityCertificate mapped

/-- The remaining multiplicity interface can be stated without committing
to a particular local-certificate construction: every source variable that
occurs exactly twice must still occur exactly twice in a
deletion-equivalent competitor. -/
def AnchorPreimageTwoCountPreservation : Prop :=
  ∀ bound (word : Word Nat),
    WordUsesAtMost word bound →
    ∀ substitution,
      word.bind substitution = anchor (3 * bound) →
      ∀ other,
        SameDeletionMarkedDigraph word other →
        ∀ letter,
          word.toList.count letter = 2 →
          other.toList.count letter = 2

/-- Exact preservation of the count-two class implies preservation of every
source multiplicity.  Counts zero and one are deletion invariants.  A
triple-occurring source variable either exposes a twice-occurring separator
owner, which makes the whole word rigid after the count-two callback, or two
singleton separator owners, which make the whole word rigid directly. -/
theorem preimage_exact_count_preservation_of_two_count_preservation
    {bound : Nat} {word other : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    (same : SameDeletionMarkedDigraph word other)
    (preserveTwo :
      ∀ letter,
        word.toList.count letter = 2 →
        other.toList.count letter = 2) :
    ∀ letter,
      other.toList.count letter = word.toList.count letter := by
  intro letter
  have sourceBound :=
    preimage_threeLimitedList mapped letter
  by_cases sourceZero : word.toList.count letter = 0
  · have otherZero :=
      (sameDeletionMarkedDigraph_count_eq_zero_iff
        same letter).mp sourceZero
    rw [sourceZero, otherZero]
  by_cases sourceOne : word.toList.count letter = 1
  · have otherOne :=
      (sameDeletionMarkedDigraph_count_eq_one_iff
        same letter).mp sourceOne
    rw [sourceOne, otherOne]
  by_cases sourceTwo : word.toList.count letter = 2
  · rw [sourceTwo, preserveTwo letter sourceTwo]
  have sourceThree : word.toList.count letter = 3 := by
    omega
  rcases
      preimage_three_occurrence_separator_factorization_cases
        mapped sourceThree with
    ownerCase | singletonCase
  · obtain
      ⟨owner, ownerCount, separatorMember⟩ :=
      ownerCase
    have wordEquality :
        other = word :=
      preimage_two_occurrence_separator_owner_rigid
        mapped same ownerCount separatorMember
        (preserveTwo owner ownerCount)
    rw [wordEquality]
  · obtain ⟨first, second, shape⟩ := singletonCase
    have wordEquality :
        other = word :=
      twoSingletonSeparatorNodupFactorization_rigid
        shape same
    rw [wordEquality]

/-- The direct count-two interface implies uniform exact-count preservation
for every bounded anchor preimage. -/
theorem
    anchorPreimageExactCountPreservation_of_twoCountPreservation
    (preserved : AnchorPreimageTwoCountPreservation) :
    AnchorPreimageExactCountPreservation := by
  intro bound word uses substitution mapped other same letter
  exact
    preimage_exact_count_preservation_of_two_count_preservation
      mapped same
        (preserved bound word uses substitution mapped other same)
      letter

/-- Exact count-two preservation is the sole remaining pure preimage
obligation: exact-count reconstruction is unconditional. -/
theorem anchorPreimageDeletionRigidity_of_twoCountPreservation
    (preserved : AnchorPreimageTwoCountPreservation) :
    AnchorPreimageDeletionRigidity :=
  anchorPreimageDeletionRigidity_of_exactCounts
    (anchorPreimageExactCountPreservation_of_twoCountPreservation
      preserved)
    anchorPreimageExactCountRigidity

end SemigroupBasis.Nonfinite.A2One
