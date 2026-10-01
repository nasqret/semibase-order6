import SemigroupBasis.CoRoots.Order6D2D4SuffixTraceV2M3FSS

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6D2D4SuffixTrace.V2

open SemigroupBasis
open SemigroupBasis.CoRoots
open SemigroupBasis.CoRoots.Order6D2D4SuffixTrace

private theorem sortedNodup_eq_of_mem_iff
    {left right : List Nat}
    (leftSorted : left.Pairwise (· ≤ ·))
    (rightSorted : right.Pairwise (· ≤ ·))
    (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (member : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail =>
          have : head ∈ ([] : List Nat) := (member head).mpr (by simp)
          simp at this
  | cons leftHead leftTail ih =>
      cases right with
      | nil =>
          have : leftHead ∈ ([] : List Nat) :=
            (member leftHead).mp (by simp)
          simp at this
      | cons rightHead rightTail =>
          have leftHeadMem : leftHead ∈ rightHead :: rightTail :=
            (member leftHead).mp (by simp)
          have rightHeadMem : rightHead ∈ leftHead :: leftTail :=
            (member rightHead).mpr (by simp)
          have leftLeRight : leftHead ≤ rightHead := by
            simp only [List.mem_cons] at rightHeadMem
            rcases rightHeadMem with rfl | memberTail
            · exact Nat.le_refl _
            · exact (List.pairwise_cons.mp leftSorted).1 _ memberTail
          have rightLeLeft : rightHead ≤ leftHead := by
            simp only [List.mem_cons] at leftHeadMem
            rcases leftHeadMem with rfl | memberTail
            · exact Nat.le_refl _
            · exact (List.pairwise_cons.mp rightSorted).1 _ memberTail
          have headsEq : leftHead = rightHead :=
            Nat.le_antisymm leftLeRight rightLeLeft
          subst rightHead
          congr 1
          apply ih
          · exact (List.pairwise_cons.mp leftSorted).2
          · exact (List.pairwise_cons.mp rightSorted).2
          · exact (List.nodup_cons.mp leftNodup).2
          · exact (List.nodup_cons.mp rightNodup).2
          · intro letter
            have leftFresh := (List.nodup_cons.mp leftNodup).1
            have rightFresh := (List.nodup_cons.mp rightNodup).1
            constructor
            · intro memberLeft
              have letterNe : letter ≠ leftHead := by
                intro letterEq
                exact leftFresh (letterEq ▸ memberLeft)
              have memberFull : letter ∈ leftHead :: leftTail := by
                simp [memberLeft]
              have transferred := (member letter).mp memberFull
              simpa [letterNe] using transferred
            · intro memberRight
              have letterNe : letter ≠ leftHead := by
                intro letterEq
                exact rightFresh (letterEq ▸ memberRight)
              have memberFull : letter ∈ leftHead :: rightTail := by
                simp [memberRight]
              have transferred := (member letter).mpr memberFull
              simpa [letterNe] using transferred

private theorem mem_eraseDups_iff (entry : Nat) :
    ∀ entries : List Nat,
      entry ∈ entries.eraseDups ↔ entry ∈ entries
  | [] => by simp
  | head :: tail => by
      rw [List.eraseDups_cons]
      simp only [List.mem_cons]
      rw [mem_eraseDups_iff entry
        (tail.filter fun candidate => !candidate == head)]
      by_cases same : entry = head
      · subst entry
        simp
      · simp [same]
termination_by
  entries => entries.length
decreasing_by
  have filteredLength :
      (tail.filter fun candidate => !candidate == head).length ≤
        tail.length := List.filter_sublist.length_le
  simpa only [List.length_cons] using Nat.lt_succ_of_le filteredLength

private theorem nodup_eraseDups :
    ∀ entries : List Nat, entries.eraseDups.Nodup
  | [] => by simp
  | head :: tail => by
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · intro member
        have filteredMember :=
          (mem_eraseDups_iff head
            (tail.filter fun candidate => !candidate == head)).mp member
        simpa using filteredMember
      · exact nodup_eraseDups
          (tail.filter fun candidate => !candidate == head)
termination_by
  entries => entries.length
decreasing_by
  have filteredLength :
      (tail.filter fun candidate => !candidate == head).length ≤
        tail.length := List.filter_sublist.length_le
  simpa only [List.length_cons] using Nat.lt_succ_of_le filteredLength

private theorem sortedSupport_mem (letters : List Nat) (letter : Nat) :
    letter ∈ sortedSupport letters ↔ letter ∈ letters := by
  simp only [sortedSupport, List.mem_mergeSort]
  exact mem_eraseDups_iff letter letters

private theorem sortedSupport_nodup (letters : List Nat) :
    (sortedSupport letters).Nodup := by
  unfold sortedSupport
  exact
    (List.mergeSort_perm letters.eraseDups
      (fun left right : Nat => decide (left ≤ right))).nodup_iff.mpr
        (nodup_eraseDups letters)

private theorem sortedSupport_sorted (letters : List Nat) :
    (sortedSupport letters).Pairwise (· ≤ ·) := by
  unfold sortedSupport
  have sorted := List.pairwise_mergeSort
    (le := fun left right : Nat => decide (left ≤ right))
    (fun _ _ _ => by simp; omega)
    (fun _ _ => by simp; omega)
    letters.eraseDups
  exact sorted.imp (by intro _ _ relation; simpa using relation)

private theorem sortedSupport_eq_of_mem_iff
    (left right : List Nat)
    (member : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    sortedSupport left = sortedSupport right := by
  apply sortedNodup_eq_of_mem_iff
  · exact sortedSupport_sorted left
  · exact sortedSupport_sorted right
  · exact sortedSupport_nodup left
  · exact sortedSupport_nodup right
  · intro letter
    simpa [sortedSupport_mem] using member letter

private theorem descriptor_content_eq
    {left right : Word Nat}
    (base :
      S5_381Invariant.SameSimpleSequenceLastGapInitialSignature left right) :
    sortedSupport left.toList = sortedSupport right.toList := by
  apply sortedSupport_eq_of_mem_iff
  intro letter
  exact base.support letter

private theorem firstSimple_eq_some_iff
    (word : Word Nat) (letter : Nat) :
    firstSimple word.toList = some letter ↔
      S5_107.SimpleInitial word letter := by
  cases word with
  | mk head tail =>
      change
        (if (head :: tail).count head = 1 then some head else none) =
            some letter ↔
          (head :: tail).count letter = 1 ∧ head = letter
      constructor
      · intro equal
        split at equal
        next simple =>
          injection equal with headEq
          subst letter
          exact ⟨simple, rfl⟩
        next notSimple => contradiction
      · rintro ⟨countOne, headEq⟩
        subst letter
        simp [countOne]

private theorem descriptor_firstSimple_eq
    {left right : Word Nat}
    (base :
      S5_381Invariant.SameSimpleSequenceLastGapInitialSignature left right) :
    firstSimple left.toList = firstSimple right.toList := by
  apply Option.ext
  intro letter
  rw [firstSimple_eq_some_iff, firstSimple_eq_some_iff]
  exact base.initial letter

private theorem simpleLetters_mem_iff
    (word : Word Nat) (letter : Nat) :
    letter ∈ simpleLetters word.toList ↔
      S5_107.SimpleIn word letter := by
  unfold simpleLetters S5_107.SimpleIn
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · exact fun present => present.2
  · intro countOne
    refine ⟨(sortedSupport_mem word.toList letter).mpr ?_, countOne⟩
    exact List.count_pos_iff.mp (by omega)

private theorem simpleLetters_sorted (letters : List Nat) :
    (simpleLetters letters).Pairwise (· ≤ ·) := by
  exact (sortedSupport_sorted letters).filter _

private theorem simpleLetters_nodup (letters : List Nat) :
    (simpleLetters letters).Nodup := by
  exact (sortedSupport_nodup letters).filter _

private theorem descriptor_simpleLetters_eq
    {left right : Word Nat}
    (base :
      S5_381Invariant.SameSimpleSequenceLastGapInitialSignature left right) :
    simpleLetters left.toList = simpleLetters right.toList := by
  apply sortedNodup_eq_of_mem_iff
  · exact simpleLetters_sorted left.toList
  · exact simpleLetters_sorted right.toList
  · exact simpleLetters_nodup left.toList
  · exact simpleLetters_nodup right.toList
  · intro letter
    rw [simpleLetters_mem_iff, simpleLetters_mem_iff]
    exact base.simple letter

private theorem unique_split_free
    {letters before after : List Nat} {selected : Nat}
    (countOne : letters.count selected = 1)
    (split : letters = before ++ selected :: after) :
    selected ∉ before ∧ selected ∉ after := by
  have equation := countOne
  rw [split] at equation
  simp only [List.count_append, List.count_cons] at equation
  simp at equation
  have beforeZero : before.count selected = 0 := by omega
  have afterZero : after.count selected = 0 := by omega
  exact ⟨List.count_eq_zero.mp beforeZero,
    List.count_eq_zero.mp afterZero⟩

private theorem dropWhile_ne_append
    {selected : Nat} {before after : List Nat}
    (free : selected ∉ before) :
    (before ++ selected :: after).dropWhile
        (fun current => current != selected) = selected :: after := by
  induction before with
  | nil => simp
  | cons first rest ih =>
      have firstNe : first ≠ selected := by
        intro equal
        subst first
        exact free (by simp)
      have restFree : selected ∉ rest := by
        intro member
        exact free (List.Mem.tail first member)
      simp [List.dropWhile, firstNe, ih restFree]

private theorem suffixAfter_eq_of_split
    {letters before after : List Nat} {selected : Nat}
    (free : selected ∉ before)
    (split : letters = before ++ selected :: after) :
    suffixAfter letters selected = after := by
  rw [split]
  unfold suffixAfter
  rw [dropWhile_ne_append free]

private theorem firstSimpleList_eq_some_iff
    (letters : List Nat) (letter : Nat) :
    firstSimple letters = some letter ↔
      ∃ rest, letters = letter :: rest ∧ letter ∉ rest := by
  cases letters with
  | nil => simp [firstSimple]
  | cons first rest =>
      change
        (if (first :: rest).count first = 1 then some first else none) =
            some letter ↔
          ∃ suffix, first :: rest = letter :: suffix ∧ letter ∉ suffix
      constructor
      · intro equal
        split at equal
        next countOne =>
          injection equal with headEq
          subst letter
          refine ⟨rest, rfl, ?_⟩
          apply List.count_eq_zero.mp
          simp at countOne
          exact countOne
        next notOne => contradiction
      · rintro ⟨suffix, split, free⟩
        injection split with headEq tailEq
        subst letter
        subst suffix
        have countZero : rest.count first = 0 :=
          List.count_eq_zero.mpr free
        simp [countZero]

private theorem suffixFirstSimple_eq_some_iff
    (word : Word Nat) (selected letter : Nat)
    (selectedSimple : S5_107.SimpleIn word selected) :
    firstSimple (suffixAfter word.toList selected) = some letter ↔
      SimpleLastFactor word selected letter ∨
        S5_107.SimpleAdjacent word selected letter := by
  constructor
  · intro suffixFirst
    have selectedMember : selected ∈ word.toList :=
      List.count_pos_iff.mp (by
        unfold S5_107.SimpleIn at selectedSimple
        omega)
    obtain ⟨before, after, split⟩ :=
      List.mem_iff_append.mp selectedMember
    have free := unique_split_free selectedSimple split
    have suffixEq := suffixAfter_eq_of_split free.1 split
    rw [suffixEq, firstSimpleList_eq_some_iff] at suffixFirst
    obtain ⟨rest, afterEq, letterFree⟩ := suffixFirst
    have fullSplit :
        word.toList = before ++ selected :: letter :: rest := by
      rw [split, afterEq]
    by_cases letterSimple : word.toList.count letter = 1
    · exact Or.inr
        ⟨selectedSimple, letterSimple,
          (S5_107.mem_adjacentPairs_iff_exists_split
            selected letter word).mpr ⟨before, rest, fullSplit⟩⟩
    · have letterMultiple : 2 ≤ word.toList.count letter := by
        have member : letter ∈ word.toList := by
          rw [fullSplit]
          simp
        have positive := List.count_pos_iff.mpr member
        omega
      exact Or.inl
        ⟨selectedSimple, letterMultiple, before, rest,
          fullSplit, letterFree⟩
  · intro relation
    rcases relation with fsl | fss
    · rcases fsl with
        ⟨_, _, before, after, split, letterFree⟩
      have splitAtSelected :
          word.toList = before ++ selected :: (letter :: after) := by
        simpa using split
      have free := unique_split_free selectedSimple splitAtSelected
      rw [suffixAfter_eq_of_split free.1 splitAtSelected,
        firstSimpleList_eq_some_iff]
      exact ⟨after, rfl, letterFree⟩
    · rcases fss with ⟨_, letterSimple, adjacent⟩
      obtain ⟨before, after, split⟩ :=
        (S5_107.mem_adjacentPairs_iff_exists_split
          selected letter word).mp adjacent
      have splitAtSelected :
          word.toList = before ++ selected :: (letter :: after) := by
        simpa using split
      have selectedFree := unique_split_free selectedSimple splitAtSelected
      have letterAfterZero : after.count letter = 0 := by
        have equation := letterSimple
        unfold S5_107.SimpleIn at equation
        rw [split] at equation
        simp only [List.count_append, List.count_cons] at equation
        simp at equation
        omega
      rw [suffixAfter_eq_of_split selectedFree.1 splitAtSelected,
        firstSimpleList_eq_some_iff]
      exact ⟨after, rfl, List.count_eq_zero.mp letterAfterZero⟩

private def orderScanFrom (x y : Nat)
    (state : S5_793Invariant.OrderGapState) (letters : List Nat) :
    S5_793Invariant.OrderGapState :=
  letters.foldl
    (fun current letter =>
      S5_793Invariant.orderStep current
        (S5_793Invariant.orderSymbol x y letter)) state

private theorem orderScanFrom_append (x y : Nat)
    (state : S5_793Invariant.OrderGapState) (left right : List Nat) :
    orderScanFrom x y state (left ++ right) =
      orderScanFrom x y (orderScanFrom x y state left) right := by
  simp [orderScanFrom, List.foldl_append]

private theorem orderScanFrom_free
    {x y : Nat} (letters : List Nat)
    (xFree : x ∉ letters) (yFree : y ∉ letters)
    (state : S5_793Invariant.OrderGapState) :
    orderScanFrom x y state letters = state := by
  induction letters generalizing state with
  | nil => rfl
  | cons first rest ih =>
      have firstNotX : first ≠ x := by
        intro equal
        subst first
        exact xFree (by simp)
      have firstNotY : first ≠ y := by
        intro equal
        subst first
        exact yFree (by simp)
      have restXFree : x ∉ rest := by
        intro member
        exact xFree (List.Mem.tail first member)
      have restYFree : y ∉ rest := by
        intro member
        exact yFree (List.Mem.tail first member)
      simp only [orderScanFrom, List.foldl_cons]
      rw [show S5_793Invariant.orderSymbol x y first = .other by
        simp [S5_793Invariant.orderSymbol, firstNotX, firstNotY]]
      simp only [S5_793Invariant.orderStep]
      exact ih restXFree restYFree state

private theorem orderScanFrom_onlyXMany
    {x y : Nat} (letters : List Nat) (yFree : y ∉ letters) :
    orderScanFrom x y .onlyXMany letters = .onlyXMany := by
  induction letters with
  | nil => rfl
  | cons first rest ih =>
      have restFree : y ∉ rest := by
        intro member
        exact yFree (List.Mem.tail first member)
      by_cases firstX : first = x
      · subst first
        simp only [orderScanFrom, List.foldl_cons]
        rw [show S5_793Invariant.orderSymbol x y x = .x by
          simp [S5_793Invariant.orderSymbol]]
        simp only [S5_793Invariant.orderStep]
        exact ih restFree
      · have firstY : first ≠ y := by
          intro equal
          subst first
          exact yFree (by simp)
        simp only [orderScanFrom, List.foldl_cons]
        rw [show S5_793Invariant.orderSymbol x y first = .other by
          simp [S5_793Invariant.orderSymbol, firstX, firstY]]
        simp only [S5_793Invariant.orderStep]
        exact ih restFree

private theorem orderScanFrom_onlyXOne_of_x_mem
    {x y : Nat} (letters : List Nat)
    (yFree : y ∉ letters) (xMember : x ∈ letters) :
    orderScanFrom x y .onlyXOne letters = .onlyXMany := by
  induction letters with
  | nil => simp at xMember
  | cons first rest ih =>
      have restYFree : y ∉ rest := by
        intro member
        exact yFree (List.Mem.tail first member)
      by_cases firstX : first = x
      · subst first
        simp only [orderScanFrom, List.foldl_cons]
        rw [show S5_793Invariant.orderSymbol x y x = .x by
          simp [S5_793Invariant.orderSymbol]]
        simp only [S5_793Invariant.orderStep]
        exact orderScanFrom_onlyXMany rest restYFree
      · have firstY : first ≠ y := by
          intro equal
          subst first
          exact yFree (by simp)
        have restMember : x ∈ rest := by
          simpa [firstX, Ne.symm firstX] using xMember
        simp only [orderScanFrom, List.foldl_cons]
        rw [show S5_793Invariant.orderSymbol x y first = .other by
          simp [S5_793Invariant.orderSymbol, firstX, firstY]]
        simp only [S5_793Invariant.orderStep]
        exact ih restYFree restMember

private theorem orderScanFrom_empty_eq_onlyXOne
    {x y : Nat} (letters : List Nat)
    (xCount : letters.count x = 1) (yFree : y ∉ letters) :
    orderScanFrom x y .empty letters = .onlyXOne := by
  have xMember : x ∈ letters := List.count_pos_iff.mp (by omega)
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp xMember
  have free := unique_split_free xCount split
  have beforeYFree : y ∉ before := by
    intro member
    exact yFree (by rw [split]; simp [member])
  have afterYFree : y ∉ after := by
    intro member
    exact yFree (by rw [split]; simp [member])
  rw [split]
  rw [show before ++ x :: after = (before ++ [x]) ++ after by simp,
    orderScanFrom_append, orderScanFrom_append,
    orderScanFrom_free before free.1 beforeYFree .empty]
  simp only [orderScanFrom, List.foldl_cons, List.foldl_nil]
  rw [show S5_793Invariant.orderSymbol x y x = .x by
    simp [S5_793Invariant.orderSymbol]]
  simp only [S5_793Invariant.orderStep]
  exact orderScanFrom_free after free.2 afterYFree .onlyXOne

private theorem orderScanFrom_empty_eq_onlyXMany
    {x y : Nat} (letters : List Nat)
    (xMultiple : 2 ≤ letters.count x) (yFree : y ∉ letters) :
    orderScanFrom x y .empty letters = .onlyXMany := by
  induction letters with
  | nil => simp at xMultiple
  | cons first rest ih =>
      have restYFree : y ∉ rest := by
        intro member
        exact yFree (List.Mem.tail first member)
      by_cases firstX : first = x
      · subst first
        have restPositive : 0 < rest.count x := by
          simp only [List.count_cons_self] at xMultiple
          omega
        have restMember : x ∈ rest :=
          List.count_pos_iff.mp restPositive
        simp only [orderScanFrom, List.foldl_cons]
        rw [show S5_793Invariant.orderSymbol x y x = .x by
          simp [S5_793Invariant.orderSymbol]]
        simp only [S5_793Invariant.orderStep]
        exact orderScanFrom_onlyXOne_of_x_mem rest restYFree restMember
      · have firstY : first ≠ y := by
          intro equal
          subst first
          exact yFree (by simp)
        have restMultiple : 2 ≤ rest.count x := by
          simpa [firstX] using xMultiple
        simp only [orderScanFrom, List.foldl_cons]
        rw [show S5_793Invariant.orderSymbol x y first = .other by
          simp [S5_793Invariant.orderSymbol, firstX, firstY]]
        simp only [S5_793Invariant.orderStep]
        exact ih restMultiple restYFree

private def PostSelectedXState : S5_793Invariant.OrderGapState → Prop
  | .simpleYX | .xManyYOneAfterXFirst | .xManyYOneAfterYFirst => True
  | _ => False

private theorem postSelectedXState_ne_before
    {state : S5_793Invariant.OrderGapState}
    (post : PostSelectedXState state) :
    state ≠ .xManyYOneBefore := by
  cases state <;> simp_all [PostSelectedXState]

private theorem orderScanFrom_postSelectedX
    {x y : Nat} (letters : List Nat) (yFree : y ∉ letters)
    (state : S5_793Invariant.OrderGapState)
    (post : PostSelectedXState state) :
    PostSelectedXState (orderScanFrom x y state letters) := by
  induction letters generalizing state with
  | nil => simpa [orderScanFrom] using post
  | cons first rest ih =>
      have restFree : y ∉ rest := by
        intro member
        exact yFree (List.Mem.tail first member)
      by_cases firstX : first = x
      · subst first
        simp only [orderScanFrom, List.foldl_cons]
        rw [show S5_793Invariant.orderSymbol x y x = .x by
          simp [S5_793Invariant.orderSymbol]]
        apply ih restFree
        cases state <;> simp_all [PostSelectedXState,
          S5_793Invariant.orderStep]
      · have firstY : first ≠ y := by
          intro equal
          subst first
          exact yFree (by simp)
        simp only [orderScanFrom, List.foldl_cons]
        rw [show S5_793Invariant.orderSymbol x y first = .other by
          simp [S5_793Invariant.orderSymbol, firstX, firstY]]
        simp only [S5_793Invariant.orderStep]
        exact ih restFree state post

private theorem orderScanFrom_after_x_mem_ne_before
    {x y : Nat} (letters : List Nat) (yFree : y ∉ letters)
    (xMember : x ∈ letters)
    (state : S5_793Invariant.OrderGapState)
    (initial : state = .onlyYOne ∨ state = .simpleXY ∨
      state = .xManyYOneBefore) :
    orderScanFrom x y state letters ≠ .xManyYOneBefore := by
  induction letters generalizing state with
  | nil => simp at xMember
  | cons first rest ih =>
      have restYFree : y ∉ rest := by
        intro member
        exact yFree (List.Mem.tail first member)
      by_cases firstX : first = x
      · subst first
        simp only [orderScanFrom, List.foldl_cons]
        rw [show S5_793Invariant.orderSymbol x y x = .x by
          simp [S5_793Invariant.orderSymbol]]
        rcases initial with rfl | rfl | rfl
        · apply postSelectedXState_ne_before
          exact orderScanFrom_postSelectedX rest restYFree .simpleYX
            (by simp [PostSelectedXState])
        · apply postSelectedXState_ne_before
          exact orderScanFrom_postSelectedX rest restYFree
            .xManyYOneAfterXFirst (by simp [PostSelectedXState])
        · apply postSelectedXState_ne_before
          exact orderScanFrom_postSelectedX rest restYFree
            .xManyYOneAfterXFirst (by simp [PostSelectedXState])
      · have firstY : first ≠ y := by
          intro equal
          subst first
          exact yFree (by simp)
        have restMember : x ∈ rest := by
          simpa [firstX, Ne.symm firstX] using xMember
        simp only [orderScanFrom, List.foldl_cons]
        rw [show S5_793Invariant.orderSymbol x y first = .other by
          simp [S5_793Invariant.orderSymbol, firstX, firstY]]
        simp only [S5_793Invariant.orderStep]
        exact ih restYFree restMember state initial

private theorem multipleLastBeforeSimple_iff_not_mem_after
    (word : Word Nat) {multiple selected : Nat}
    {before after : List Nat}
    (multipleCount : 2 ≤ word.toList.count multiple)
    (selectedCount : word.toList.count selected = 1)
    (split : word.toList = before ++ selected :: after) :
    S5_793Invariant.MultipleLastBeforeSimple word multiple selected ↔
      multiple ∉ after := by
  have different : multiple ≠ selected := by
    intro equal
    subst selected
    omega
  have selectedFree := unique_split_free selectedCount split
  have scanDefinition :
      S5_793Invariant.orderGapScan word multiple selected =
        orderScanFrom multiple selected .empty word.toList := rfl
  constructor
  · rintro ⟨_, scanBefore⟩
    intro multipleAfter
    have beforeState :
        orderScanFrom multiple selected .empty before = .empty ∨
          orderScanFrom multiple selected .empty before = .onlyXOne ∨
          orderScanFrom multiple selected .empty before = .onlyXMany := by
      by_cases memberBefore : multiple ∈ before
      · by_cases countOne : before.count multiple = 1
        · exact Or.inr <| Or.inl <|
            orderScanFrom_empty_eq_onlyXOne before countOne selectedFree.1
        · have positive : 0 < before.count multiple :=
            List.count_pos_iff.mpr memberBefore
          have countMany : 2 ≤ before.count multiple := by omega
          exact Or.inr <| Or.inr <|
            orderScanFrom_empty_eq_onlyXMany before countMany selectedFree.1
      · exact Or.inl <|
          orderScanFrom_free before memberBefore selectedFree.1 .empty
    have scanNotBefore :
        S5_793Invariant.orderGapScan word multiple selected ≠
          .xManyYOneBefore := by
      rw [scanDefinition, split]
      rw [show before ++ selected :: after =
          (before ++ [selected]) ++ after by simp,
        orderScanFrom_append, orderScanFrom_append]
      rcases beforeState with empty | one | many
      · rw [empty]
        simp only [orderScanFrom, List.foldl_cons, List.foldl_nil]
        rw [show S5_793Invariant.orderSymbol multiple selected selected =
            .y by
          simp [S5_793Invariant.orderSymbol, Ne.symm different]]
        simp only [S5_793Invariant.orderStep]
        exact orderScanFrom_after_x_mem_ne_before after selectedFree.2
          multipleAfter .onlyYOne (Or.inl rfl)
      · rw [one]
        simp only [orderScanFrom, List.foldl_cons, List.foldl_nil]
        rw [show S5_793Invariant.orderSymbol multiple selected selected =
            .y by
          simp [S5_793Invariant.orderSymbol, Ne.symm different]]
        simp only [S5_793Invariant.orderStep]
        exact orderScanFrom_after_x_mem_ne_before after selectedFree.2
          multipleAfter .simpleXY (Or.inr <| Or.inl rfl)
      · rw [many]
        simp only [orderScanFrom, List.foldl_cons, List.foldl_nil]
        rw [show S5_793Invariant.orderSymbol multiple selected selected =
            .y by
          simp [S5_793Invariant.orderSymbol, Ne.symm different]]
        simp only [S5_793Invariant.orderStep]
        exact orderScanFrom_after_x_mem_ne_before after selectedFree.2
          multipleAfter .xManyYOneBefore (Or.inr <| Or.inr rfl)
    exact scanNotBefore scanBefore
  · intro multipleAfterFree
    refine ⟨different, ?_⟩
    have afterZero : after.count multiple = 0 :=
      List.count_eq_zero.mpr multipleAfterFree
    have beforeMany : 2 ≤ before.count multiple := by
      have equation := multipleCount
      rw [split, List.count_append,
        List.count_cons_of_ne (Ne.symm different)] at equation
      omega
    have beforeState :=
      orderScanFrom_empty_eq_onlyXMany before beforeMany selectedFree.1
    rw [scanDefinition, split]
    rw [show before ++ selected :: after =
        (before ++ [selected]) ++ after by simp,
      orderScanFrom_append, orderScanFrom_append, beforeState]
    simp only [orderScanFrom, List.foldl_cons, List.foldl_nil]
    rw [show S5_793Invariant.orderSymbol multiple selected selected = .y by
      simp [S5_793Invariant.orderSymbol, Ne.symm different]]
    simp only [S5_793Invariant.orderStep]
    exact orderScanFrom_free after multipleAfterFree selectedFree.2
      .xManyYOneBefore

/-- Under the inherited simple/multiple boundary, the D4 side condition is
exactly the negation of the frozen last-gap relation. -/
theorem someYAfterX_iff_not_multipleLastBeforeSimple
    (word : Word Nat) (x y : Nat)
    (xSimple : S5_107.SimpleIn word x)
    (yMultiple : 2 ≤ word.toList.count y) :
    SomeYAfterX word x y ↔
      ¬ S5_793Invariant.MultipleLastBeforeSimple word y x := by
  constructor
  · rintro ⟨before, after, split, yAfter⟩ lastBefore
    have yAfterFree :=
      (multipleLastBeforeSimple_iff_not_mem_after word
        yMultiple xSimple split).mp lastBefore
    exact yAfterFree yAfter
  · intro notLastBefore
    have xMember : x ∈ word.toList :=
      List.count_pos_iff.mp (by
        unfold S5_107.SimpleIn at xSimple
        omega)
    obtain ⟨before, after, split⟩ :=
      List.mem_iff_append.mp xMember
    refine ⟨before, after, split, ?_⟩
    apply Classical.byContradiction
    intro yAfterFree
    exact notLastBefore <|
      (multipleLastBeforeSimple_iff_not_mem_after word
        yMultiple xSimple split).mpr yAfterFree

private theorem simplePrecedes_iff_mem_after
    (word : Word Nat) {selected letter : Nat}
    {before after : List Nat}
    (different : selected ≠ letter)
    (selectedCount : word.toList.count selected = 1)
    (letterCount : word.toList.count letter = 1)
    (split : word.toList = before ++ selected :: after) :
    S5_793Invariant.SimplePrecedes word selected letter ↔
      letter ∈ after := by
  have selectedFree := unique_split_free selectedCount split
  have scanDefinition :
      S5_793Invariant.orderGapScan word selected letter =
        orderScanFrom selected letter .empty word.toList := rfl
  constructor
  · rintro ⟨_, scanSimple⟩
    by_cases letterAfter : letter ∈ after
    · exact letterAfter
    exfalso
    have letterMember : letter ∈ word.toList :=
      List.count_pos_iff.mp (by omega)
    have letterBefore : letter ∈ before := by
      rw [split] at letterMember
      simp only [List.mem_append, List.mem_cons] at letterMember
      rcases letterMember with beforeMember | equal | afterMember
      · exact beforeMember
      · exact False.elim (different equal.symm)
      · exact False.elim (letterAfter afterMember)
    obtain ⟨pref, middle, beforeSplit⟩ :=
      List.mem_iff_append.mp letterBefore
    have beforeLetterCount : before.count letter = 1 := by
      have equation := letterCount
      rw [split, List.count_append,
        List.count_cons_of_ne different] at equation
      have afterZero : after.count letter = 0 :=
        List.count_eq_zero.mpr letterAfter
      omega
    have letterPartsFree :=
      unique_split_free beforeLetterCount beforeSplit
    have prefSelectedFree : selected ∉ pref := by
      intro member
      exact selectedFree.1 (by rw [beforeSplit]; simp [member])
    have middleSelectedFree : selected ∉ middle := by
      intro member
      exact selectedFree.1 (by rw [beforeSplit]; simp [member])
    have prefState :
        orderScanFrom selected letter .empty pref = .empty :=
      orderScanFrom_free pref prefSelectedFree letterPartsFree.1 .empty
    have letterState :
        orderScanFrom selected letter .empty [letter] = .onlyYOne := by
      simp [orderScanFrom, S5_793Invariant.orderSymbol,
        S5_793Invariant.orderStep, Ne.symm different]
    have middleState :
        orderScanFrom selected letter .onlyYOne middle = .onlyYOne :=
      orderScanFrom_free middle middleSelectedFree
        letterPartsFree.2 .onlyYOne
    have selectedState :
        orderScanFrom selected letter .onlyYOne [selected] = .simpleYX := by
      simp [orderScanFrom, S5_793Invariant.orderSymbol,
        S5_793Invariant.orderStep]
    have afterState :
        orderScanFrom selected letter .simpleYX after = .simpleYX :=
      orderScanFrom_free after selectedFree.2 letterAfter .simpleYX
    have scanNotSimple :
        S5_793Invariant.orderGapScan word selected letter = .simpleYX := by
      rw [scanDefinition, split, beforeSplit]
      rw [show (pref ++ letter :: middle) ++ selected :: after =
          (((pref ++ [letter]) ++ middle) ++ [selected]) ++ after by
        simp [List.append_assoc]]
      rw [orderScanFrom_append, orderScanFrom_append,
        orderScanFrom_append, orderScanFrom_append]
      rw [prefState, letterState, middleState, selectedState, afterState]
    rw [scanNotSimple] at scanSimple
    contradiction
  · intro letterAfter
    have beforeLetterZero : before.count letter = 0 := by
      have equation := letterCount
      rw [split, List.count_append,
        List.count_cons_of_ne different] at equation
      have positive : 0 < after.count letter :=
        List.count_pos_iff.mpr letterAfter
      omega
    have beforeLetterFree : letter ∉ before :=
      List.count_eq_zero.mp beforeLetterZero
    have afterLetterCount : after.count letter = 1 := by
      have equation := letterCount
      rw [split, List.count_append,
        List.count_cons_of_ne different] at equation
      omega
    obtain ⟨middle, suffix, afterSplit⟩ :=
      List.mem_iff_append.mp letterAfter
    have letterPartsFree := unique_split_free afterLetterCount afterSplit
    have middleSelectedFree : selected ∉ middle := by
      intro member
      exact selectedFree.2 (by rw [afterSplit]; simp [member])
    have suffixSelectedFree : selected ∉ suffix := by
      intro member
      exact selectedFree.2 (by rw [afterSplit]; simp [member])
    have beforeState :
        orderScanFrom selected letter .empty before = .empty :=
      orderScanFrom_free before selectedFree.1 beforeLetterFree .empty
    have selectedState :
        orderScanFrom selected letter .empty [selected] = .onlyXOne := by
      simp [orderScanFrom, S5_793Invariant.orderSymbol,
        S5_793Invariant.orderStep]
    have middleState :
        orderScanFrom selected letter .onlyXOne middle = .onlyXOne :=
      orderScanFrom_free middle middleSelectedFree
        letterPartsFree.1 .onlyXOne
    have letterState :
        orderScanFrom selected letter .onlyXOne [letter] = .simpleXY := by
      simp [orderScanFrom, S5_793Invariant.orderSymbol,
        S5_793Invariant.orderStep, Ne.symm different]
    have suffixState :
        orderScanFrom selected letter .simpleXY suffix = .simpleXY :=
      orderScanFrom_free suffix suffixSelectedFree
        letterPartsFree.2 .simpleXY
    refine ⟨different, ?_⟩
    rw [scanDefinition, split, afterSplit]
    rw [show before ++ selected :: (middle ++ letter :: suffix) =
        (((before ++ [selected]) ++ middle) ++ [letter]) ++ suffix by
      simp [List.append_assoc]]
    rw [orderScanFrom_append, orderScanFrom_append,
      orderScanFrom_append, orderScanFrom_append]
    rw [beforeState, selectedState, middleState, letterState, suffixState]

private theorem descriptor_suffixContent_eq
    {left right : Word Nat}
    (base :
      S5_381Invariant.SameSimpleSequenceLastGapInitialSignature left right)
    (selected : Nat)
    (selectedSimpleLeft : S5_107.SimpleIn left selected) :
    sortedSupport (suffixAfter left.toList selected) =
      sortedSupport (suffixAfter right.toList selected) := by
  have selectedSimpleRight : S5_107.SimpleIn right selected :=
    (base.simple selected).mp selectedSimpleLeft
  have selectedLeftMember : selected ∈ left.toList :=
    List.count_pos_iff.mp (by
      unfold S5_107.SimpleIn at selectedSimpleLeft
      omega)
  have selectedRightMember : selected ∈ right.toList :=
    List.count_pos_iff.mp (by
      unfold S5_107.SimpleIn at selectedSimpleRight
      omega)
  obtain ⟨leftBefore, leftAfter, leftSplit⟩ :=
    List.mem_iff_append.mp selectedLeftMember
  obtain ⟨rightBefore, rightAfter, rightSplit⟩ :=
    List.mem_iff_append.mp selectedRightMember
  have leftFree := unique_split_free selectedSimpleLeft leftSplit
  have rightFree := unique_split_free selectedSimpleRight rightSplit
  rw [suffixAfter_eq_of_split leftFree.1 leftSplit,
    suffixAfter_eq_of_split rightFree.1 rightSplit]
  apply sortedSupport_eq_of_mem_iff
  intro letter
  by_cases same : letter = selected
  · subst letter
    simp [leftFree.2, rightFree.2]
  by_cases letterSimpleLeft : S5_107.SimpleIn left letter
  · have letterSimpleRight : S5_107.SimpleIn right letter :=
      (base.simple letter).mp letterSimpleLeft
    rw [← simplePrecedes_iff_mem_after left (Ne.symm same)
        selectedSimpleLeft letterSimpleLeft leftSplit,
      ← simplePrecedes_iff_mem_after right (Ne.symm same)
        selectedSimpleRight letterSimpleRight rightSplit]
    exact base.simpleSequence selected letter
  by_cases letterAbsentLeft : letter ∉ left.toList
  · have letterAbsentRight : letter ∉ right.toList :=
      (base.absent letter).mp letterAbsentLeft
    have leftAfterFree : letter ∉ leftAfter := by
      intro member
      exact letterAbsentLeft (by rw [leftSplit]; simp [member])
    have rightAfterFree : letter ∉ rightAfter := by
      intro member
      exact letterAbsentRight (by rw [rightSplit]; simp [member])
    simp [leftAfterFree, rightAfterFree]
  · have letterMemberLeft : letter ∈ left.toList :=
      Classical.byContradiction letterAbsentLeft
    have letterMemberRight : letter ∈ right.toList :=
      (base.support letter).mp letterMemberLeft
    have letterMultipleLeft : 2 ≤ left.toList.count letter := by
      have positive : 0 < left.toList.count letter :=
        List.count_pos_iff.mpr letterMemberLeft
      unfold S5_107.SimpleIn at letterSimpleLeft
      omega
    have letterSimpleRightFree : ¬ S5_107.SimpleIn right letter := by
      intro simpleRight
      exact letterSimpleLeft ((base.simple letter).mpr simpleRight)
    have letterMultipleRight : 2 ≤ right.toList.count letter := by
      have positive : 0 < right.toList.count letter :=
        List.count_pos_iff.mpr letterMemberRight
      unfold S5_107.SimpleIn at letterSimpleRightFree
      omega
    have absentIff : letter ∉ leftAfter ↔ letter ∉ rightAfter := by
      rw [← multipleLastBeforeSimple_iff_not_mem_after left
          letterMultipleLeft selectedSimpleLeft leftSplit,
        ← multipleLastBeforeSimple_iff_not_mem_after right
          letterMultipleRight selectedSimpleRight rightSplit]
      exact base.lastGap letter selected
    constructor
    · intro leftMember
      apply Classical.byContradiction
      intro rightFree
      exact (absentIff.mpr rightFree) leftMember
    · intro rightMember
      apply Classical.byContradiction
      intro leftFree
      exact (absentIff.mp leftFree) rightMember

private theorem descriptor_suffixFirstSimple_eq
    {left right : Word Nat}
    (base :
      S5_381Invariant.SameSimpleSequenceLastGapInitialSignature left right)
    (fsl : SameFSL left right)
    (fss : SameFSS left right)
    (selected : Nat)
    (selectedSimpleLeft : S5_107.SimpleIn left selected) :
    firstSimple (suffixAfter left.toList selected) =
      firstSimple (suffixAfter right.toList selected) := by
  have selectedSimpleRight : S5_107.SimpleIn right selected :=
    (base.simple selected).mp selectedSimpleLeft
  apply Option.ext
  intro letter
  rw [suffixFirstSimple_eq_some_iff left selected letter
      selectedSimpleLeft,
    suffixFirstSimple_eq_some_iff right selected letter
      selectedSimpleRight]
  constructor
  · intro relation
    rcases relation with lastFactor | adjacent
    · exact Or.inl ((fsl selected letter).mp lastFactor)
    · exact Or.inr ((fss selected letter).mp adjacent)
  · intro relation
    rcases relation with lastFactor | adjacent
    · exact Or.inl ((fsl selected letter).mpr lastFactor)
    · exact Or.inr ((fss selected letter).mpr adjacent)

private theorem descriptor_suffixTrace_eq
    {left right : Word Nat}
    (base :
      S5_381Invariant.SameSimpleSequenceLastGapInitialSignature left right)
    (fsl : SameFSL left right)
    (fss : SameFSS left right)
    (selected : Nat)
    (selectedSimpleLeft : S5_107.SimpleIn left selected) :
    suffixTrace left.toList selected =
      suffixTrace right.toList selected := by
  unfold suffixTrace
  dsimp
  rw [descriptor_suffixContent_eq base selected selectedSimpleLeft,
    descriptor_suffixFirstSimple_eq base fsl fss selected
      selectedSimpleLeft]

private theorem descriptor_traces_eq
    {left right : Word Nat}
    (base :
      S5_381Invariant.SameSimpleSequenceLastGapInitialSignature left right)
    (fsl : SameFSL left right)
    (fss : SameFSS left right) :
    (simpleLetters left.toList).map (suffixTrace left.toList) =
      (simpleLetters right.toList).map (suffixTrace right.toList) := by
  rw [descriptor_simpleLetters_eq base]
  apply List.map_congr_left
  intro selected selectedMember
  have selectedSimpleRight : S5_107.SimpleIn right selected :=
    (simpleLetters_mem_iff right selected).mp selectedMember
  have selectedSimpleLeft : S5_107.SimpleIn left selected :=
    (base.simple selected).mpr selectedSimpleRight
  exact descriptor_suffixTrace_eq base fsl fss selected selectedSimpleLeft

/-- The named frozen `D*` bridge: the inherited `S5_610` signature together
with equality of the two missing factor relations determines the immutable
suffix-trace descriptor literally. -/
theorem frozenDescriptor_eq_of_base_fsl_fss
    {left right : Word Nat}
    (base :
      S5_381Invariant.SameSimpleSequenceLastGapInitialSignature left right)
    (fsl : SameFSL left right)
    (fss : SameFSS left right) :
    descriptor left = descriptor right := by
  unfold descriptor
  dsimp
  rw [descriptor_content_eq base, descriptor_firstSimple_eq base,
    descriptor_traces_eq base fsl fss]

end SemigroupBasis.CoRoots.Order6D2D4SuffixTrace.V2
