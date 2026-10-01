import SemigroupBasis.Nonfinite.A2One.DeletionGraphPreimageRigidity

namespace SemigroupBasis.Nonfinite.A2One

open SemigroupBasis

/-!
General invariants extracted from the exact factorization study.

The finite certificates for bounds two and three repeatedly use variables that
occur exactly once.  The theorem below makes that observation reusable:
equality of every deletion marked digraph preserves an exact singleton
projection, not merely its support.
-/

private theorem sameMarkedDigraphList_singleton_exact
    {letter : Nat} {other : List Nat}
    (same : SameMarkedDigraphList [letter] other) :
    other = [letter] := by
  cases other with
  | nil =>
      simp [SameMarkedDigraphList] at same
  | cons head tail =>
      have headEq : head = letter := by
        simpa [SameMarkedDigraphList] using same.1.symm
      subst head
      cases tail with
      | nil => rfl
      | cons next rest =>
          have rightEdge :
              (letter, next) ∈
                adjacentPairsList (letter :: next :: rest) := by
            simp [adjacentPairsList, Word.adjacentPairsFrom]
          have leftEdge :=
            (same.2.2.2 letter next).mpr rightEdge
          simp [adjacentPairsList, Word.adjacentPairsFrom] at leftEdge

private theorem filter_true (letters : List Nat) :
    letters.filter (fun _ => true) = letters := by
  induction letters with
  | nil => rfl
  | cons first rest ih => simp [ih]

/-- Keeping every variable recovers equality of the full marked digraphs. -/
theorem sameDeletionMarkedDigraph_full
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right) :
    SameMarkedDigraphList left.toList right.toList := by
  have allKept := same (fun _ => true)
  rw [filter_true, filter_true] at allKept
  exact allKept

/-- Deletion marked-digraph equivalence preserves the complete support. -/
theorem sameDeletionMarkedDigraph_mem_iff
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    (letter : Nat) :
    letter ∈ left.toList ↔ letter ∈ right.toList :=
  (sameDeletionMarkedDigraph_full same).2.2.1 letter

/-- No fresh variable can occur in a deletion-equivalent competitor. -/
theorem sameDeletionMarkedDigraph_not_mem
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    {letter : Nat}
    (absent : letter ∉ left.toList) :
    letter ∉ right.toList := by
  intro member
  exact absent ((sameDeletionMarkedDigraph_mem_iff same letter).mpr member)

/-- If deleting all variables except `letter` leaves exactly one occurrence,
then every deletion-equivalent word also has exactly that singleton
projection. -/
theorem sameDeletionMarkedDigraph_preserves_singletonProjection
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    (letter : Nat)
    (leftProjection :
      left.toList.filter (fun value => value == letter) = [letter]) :
    right.toList.filter (fun value => value == letter) = [letter] := by
  have projected := same (fun value => value == letter)
  rw [leftProjection] at projected
  exact sameMarkedDigraphList_singleton_exact projected

/-- Exact singleton occurrence is symmetric under deletion marked-digraph
equivalence. -/
theorem sameDeletionMarkedDigraph_singletonProjection_iff
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    (letter : Nat) :
    left.toList.filter (fun value => value == letter) = [letter] ↔
      right.toList.filter (fun value => value == letter) = [letter] := by
  constructor
  · exact sameDeletionMarkedDigraph_preserves_singletonProjection same letter
  · exact sameDeletionMarkedDigraph_preserves_singletonProjection
      same.symm letter

private theorem filter_eq_nil_iff_count_eq_zero
    (letters : List Nat) (letter : Nat) :
    letters.filter (fun value => value == letter) = [] ↔
      letters.count letter = 0 := by
  induction letters with
  | nil => simp
  | cons first rest ih =>
      by_cases equality : first = letter
      · subst first
        simp
      · simp [equality, ih]

private theorem filter_eq_singleton_iff_count_eq_one
    (letters : List Nat) (letter : Nat) :
    letters.filter (fun value => value == letter) = [letter] ↔
      letters.count letter = 1 := by
  induction letters with
  | nil => simp
  | cons first rest ih =>
      by_cases equality : first = letter
      · subst first
        rw [List.filter_cons]
        simp only [beq_self_eq_true, if_true, List.count_cons_self,
          List.cons.injEq, true_and]
        rw [filter_eq_nil_iff_count_eq_zero]
        omega
      · simp [equality, ih]

/-- Deletion marked-digraph equivalence preserves whether a variable is
absent. -/
theorem sameDeletionMarkedDigraph_count_eq_zero_iff
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    (letter : Nat) :
    left.toList.count letter = 0 ↔
      right.toList.count letter = 0 := by
  constructor
  · intro leftZero
    apply List.count_eq_zero.mpr
    intro rightMember
    exact (List.count_eq_zero.mp leftZero)
      ((sameDeletionMarkedDigraph_mem_iff same letter).mpr rightMember)
  · intro rightZero
    apply List.count_eq_zero.mpr
    intro leftMember
    exact (List.count_eq_zero.mp rightZero)
      ((sameDeletionMarkedDigraph_mem_iff same letter).mp leftMember)

/-- Deletion marked-digraph equivalence preserves the variables that occur
exactly once. -/
theorem sameDeletionMarkedDigraph_count_eq_one_iff
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    (letter : Nat) :
    left.toList.count letter = 1 ↔
      right.toList.count letter = 1 := by
  rw [← filter_eq_singleton_iff_count_eq_one,
    ← filter_eq_singleton_iff_count_eq_one]
  exact sameDeletionMarkedDigraph_singletonProjection_iff same letter

/-- Consequently, deletion marked-digraph equivalence preserves the coarse
multiplicity class `at least two`. -/
theorem sameDeletionMarkedDigraph_two_le_count_iff
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    (letter : Nat) :
    2 ≤ left.toList.count letter ↔
      2 ≤ right.toList.count letter := by
  have zero :=
    sameDeletionMarkedDigraph_count_eq_zero_iff same letter
  have one :=
    sameDeletionMarkedDigraph_count_eq_one_iff same letter
  omega

/-- Every variable occurs at most twice.  This is the natural exact
multiplicity boundary below the anchor-specific triple-occurrence cases. -/
def TwoLimitedList (letters : List Nat) : Prop :=
  ∀ letter, letters.count letter ≤ 2

/-- Every variable occurs at most three times.  Anchor preimages satisfy this
coarse bound, but unlike the 2-limited case it is not by itself a rigidity
condition. -/
def ThreeLimitedList (letters : List Nat) : Prop :=
  ∀ letter, letters.count letter ≤ 3

/-- Every source word mapped nonerasingly to a Trahtman anchor is
3-limited. Each source occurrence contributes the head marker of its image,
and every anchor marker occurs at most three times. -/
theorem preimage_threeLimitedList
    {bound : Nat} {word : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound)) :
    ThreeLimitedList word.toList := by
  intro sourceLetter
  let marker := (substitution sourceLetter).head
  have markerMember :
      marker ∈ (substitution sourceLetter).toList := by
    simp [marker, Word.toList]
  have occurrenceBound :=
    count_le_flatMap_count_of_mem word.toList
      (fun letter => (substitution letter).toList)
      sourceLetter marker markerMember
  rw [← Word.toList_bind, mapped] at occurrenceBound
  exact Nat.le_trans occurrenceBound
    (anchor_count_le_three (3 * bound) marker)

/-- A contiguous nonempty factor occurs twice consecutively. -/
def HasSquareFactor (letters : List Nat) : Prop :=
  ∃ pre block post,
    block ≠ [] ∧
      letters = pre ++ block ++ block ++ post

/-- Standard square-freeness for a list word. -/
def SquareFreeList (letters : List Nat) : Prop :=
  ¬HasSquareFactor letters

private theorem flatMap_nonempty_of_nonempty
    {letters : List Nat} (nonempty : letters ≠ [])
    (images : Nat → List Nat)
    (imageNonempty : ∀ letter, images letter ≠ []) :
    letters.flatMap images ≠ [] := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
      simp only [List.flatMap_cons]
      exact
        List.append_ne_nil_of_left_ne_nil
          (imageNonempty first) (List.flatMap images rest)

/-- A nonerasing substitution preserves every adjacent square factor.
Consequently, a preimage of a square-free target is square-free. -/
theorem squareFreeList_of_flatMap_eq
    {source target : List Nat}
    (images : Nat → List Nat)
    (imageNonempty : ∀ letter, images letter ≠ [])
    (mapped : source.flatMap images = target)
    (targetSquareFree : SquareFreeList target) :
    SquareFreeList source := by
  intro sourceSquare
  rcases sourceSquare with
    ⟨pre, block, post, blockNonempty, sourceEq⟩
  apply targetSquareFree
  refine ⟨pre.flatMap images, block.flatMap images,
    post.flatMap images, ?_, ?_⟩
  · exact flatMap_nonempty_of_nonempty blockNonempty images imageNonempty
  · rw [← mapped, sourceEq]
    simp only [List.flatMap_append, List.append_assoc]

/-- Word-level specialization: every source word mapping nonerasingly to a
square-free target is itself square-free. -/
theorem squareFreeList_of_bind_eq
    {source target : Word Nat}
    (substitution : Nat → Word Nat)
    (mapped : source.bind substitution = target)
    (targetSquareFree : SquareFreeList target.toList) :
    SquareFreeList source.toList := by
  apply squareFreeList_of_flatMap_eq
    (fun letter => (substitution letter).toList)
  · intro letter
    cases substitution letter
    simp [Word.toList]
  · simpa [Word.toList_bind] using
      congrArg Word.toList mapped
  · exact targetSquareFree

private def forwardEdges (extra : Nat) : List (Nat × Nat) :=
  (List.range (extra + 1)).map fun letter => (letter, letter + 1)

private def reverseEdges (extra : Nat) : List (Nat × Nat) :=
  (List.range (extra + 1)).reverse.map
    fun letter => (letter + 1, letter)

private theorem singleton_final (letter : Nat) :
    (Word.singleton letter).final = letter := by
  rfl

private theorem singleton_adjacentPairs (letter : Nat) :
    (Word.singleton letter).adjacentPairs = [] := by
  rfl

private theorem forwardBlock_final (extra : Nat) :
    (forwardBlock extra).final = extra + 1 := by
  cases extra with
  | zero => decide
  | succ extra =>
      rw [forwardBlock, Word.final_append, singleton_final]

private theorem forwardBlock_head (extra : Nat) :
    (forwardBlock extra).head = 0 := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      simpa [forwardBlock] using ih

private theorem reverseBlock_head (extra : Nat) :
    (reverseBlock extra).head = extra + 1 := by
  cases extra with
  | zero => rfl
  | succ extra =>
      simp [reverseBlock]

private theorem reverseBlock_final (extra : Nat) :
    (reverseBlock extra).final = 0 := by
  induction extra with
  | zero => decide
  | succ extra ih =>
      rw [reverseBlock, Word.final_append, ih]

private theorem forwardBlock_adjacentPairs :
    ∀ extra,
      (forwardBlock extra).adjacentPairs = forwardEdges extra
  | 0 => by decide
  | extra + 1 => by
      rw [forwardBlock, Word.adjacentPairs_append,
        forwardBlock_adjacentPairs extra]
      simp [forwardEdges, forwardBlock_final, singleton_adjacentPairs,
        List.range_succ,
        List.map_append, Nat.add_assoc]

private theorem reverseBlock_adjacentPairs :
    ∀ extra,
      (reverseBlock extra).adjacentPairs = reverseEdges extra
  | 0 => by decide
  | extra + 1 => by
      rw [reverseBlock, Word.adjacentPairs_append,
        reverseBlock_adjacentPairs extra]
      simp [reverseEdges, reverseBlock_head, singleton_final,
        singleton_adjacentPairs, List.range_succ,
        List.reverse_append, Nat.add_assoc]

private theorem forwardEdges_nodup (extra : Nat) :
    (forwardEdges extra).Nodup := by
  apply List.nodup_range.map
  intro first second different equality
  exact different (congrArg Prod.fst equality)

private theorem reverseEdges_nodup (extra : Nat) :
    (reverseEdges extra).Nodup := by
  rw [List.nodup_iff_count]
  intro edge
  have mappedNodup :
      ((List.range (extra + 1)).map
        (fun letter => (letter + 1, letter))).Nodup := by
    apply List.nodup_range.map
    intro first second different equality
    exact different (congrArg Prod.snd equality)
  have mappedBound :=
    List.nodup_iff_count.mp mappedNodup edge
  simpa [reverseEdges, List.map_reverse] using mappedBound

private theorem mem_forwardEdges_iff
    {extra source target : Nat} :
    (source, target) ∈ forwardEdges extra ↔
      source < extra + 1 ∧ target = source + 1 := by
  constructor
  · intro member
    rcases List.mem_map.mp member with
      ⟨letter, letterMember, equality⟩
    have sourceEq := congrArg Prod.fst equality
    have targetEq := congrArg Prod.snd equality
    simp only at sourceEq targetEq
    subst source
    subst target
    exact ⟨List.mem_range.mp letterMember, rfl⟩
  · rintro ⟨sourceBound, rfl⟩
    exact List.mem_map.mpr
      ⟨source, List.mem_range.mpr sourceBound, rfl⟩

private theorem mem_reverseEdges_iff
    {extra source target : Nat} :
    (source, target) ∈ reverseEdges extra ↔
      target < extra + 1 ∧ source = target + 1 := by
  constructor
  · intro member
    rcases List.mem_map.mp member with
      ⟨letter, letterMember, equality⟩
    have sourceEq := congrArg Prod.fst equality
    have targetEq := congrArg Prod.snd equality
    simp only at sourceEq targetEq
    subst source
    subst target
    exact
      ⟨List.mem_range.mp (by simpa using letterMember), rfl⟩
  · rintro ⟨targetBound, rfl⟩
    exact List.mem_map.mpr
      ⟨target,
        (by
          simpa using
            List.mem_range.mpr targetBound :
              target ∈ (List.range (extra + 1)).reverse),
        rfl⟩

/-- Every adjacent pair in a reversed initial range is a descending
successor edge. -/
theorem adjacentPairsList_reverse_range_descending
    {length source target : Nat}
    (member :
      (source, target) ∈
        adjacentPairsList (List.range length).reverse) :
    source = target + 1 := by
  cases length with
  | zero =>
      simp [adjacentPairsList] at member
  | succ rest =>
      cases rest with
      | zero =>
          simp [adjacentPairsList, Word.adjacentPairsFrom] at member
      | succ extra =>
          have blockMember :
              (source, target) ∈
                adjacentPairsList (reverseBlock extra).toList := by
            simpa [reverseBlock_toList, Nat.add_assoc] using member
          have listedPairs :
              adjacentPairsList (reverseBlock extra).toList =
                (reverseBlock extra).adjacentPairs := by
            cases reverseBlock extra
            rfl
          rw [listedPairs, reverseBlock_adjacentPairs] at blockMember
          exact (mem_reverseEdges_iff.mp blockMember).2

private def anchorSingleEdges (extra : Nat) : List (Nat × Nat) :=
  [(extra + 1, extra + 2), (extra + 2, extra + 1)] ++
    (reverseEdges extra ++
      [(0, extra + 2), (extra + 2, 0)])

private theorem anchorSingleEdges_nodup (extra : Nat) :
    (anchorSingleEdges extra).Nodup := by
  simp only [anchorSingleEdges]
  apply List.nodup_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.nodup_cons]
    constructor
    · intro equality
      simp only [List.mem_singleton] at equality
      have first := congrArg Prod.fst equality
      have second := congrArg Prod.snd equality
      simp only at first second
      omega
    · simp
  · apply List.nodup_append.mpr
    refine ⟨reverseEdges_nodup extra, ?_, ?_⟩
    · simp only [List.nodup_cons]
      constructor
      · intro equality
        simp only [List.mem_singleton] at equality
        have first := congrArg Prod.fst equality
        have second := congrArg Prod.snd equality
        simp only at first second
        omega
      · simp
    · intro edge edgeReverse boundary edgeBoundary equality
      subst boundary
      simp at edgeBoundary
      rcases edgeBoundary with rfl | rfl
      · rw [mem_reverseEdges_iff] at edgeReverse
        omega
      · rw [mem_reverseEdges_iff] at edgeReverse
        omega
  · intro boundary boundaryPrefix edge edgeRest equality
    subst edge
    simp at boundaryPrefix
    rcases boundaryPrefix with rfl | rfl
    · simp [mem_reverseEdges_iff] at edgeRest
    · simp [mem_reverseEdges_iff] at edgeRest

private theorem forwardEdges_disjoint_anchorSingleEdges
    {extra source target : Nat}
    (forward : (source, target) ∈ forwardEdges extra) :
    (source, target) ∉ anchorSingleEdges extra := by
  rw [mem_forwardEdges_iff] at forward
  simp [anchorSingleEdges, mem_reverseEdges_iff]
  omega

private theorem anchor_adjacentPairs (extra : Nat) :
    (anchor extra).adjacentPairs =
      forwardEdges extra ++ anchorSingleEdges extra ++ forwardEdges extra := by
  simp [anchor, separator, Word.adjacentPairs_append,
    forwardBlock_adjacentPairs, reverseBlock_adjacentPairs,
    forwardBlock_final, reverseBlock_head, reverseBlock_final,
    forwardBlock_head, singleton_final, singleton_adjacentPairs,
    anchorSingleEdges, List.append_assoc]

/-- A directed adjacent pair occurs exactly twice in a Trahtman anchor
precisely when it is one of the forward indexed edges. -/
theorem anchor_adjacent_pair_count_eq_two_iff
    (extra source target : Nat) :
    (anchor extra).adjacentPairs.count (source, target) = 2 ↔
      source < extra + 1 ∧ target = source + 1 := by
  rw [← mem_forwardEdges_iff, anchor_adjacentPairs]
  simp only [List.count_append]
  have forwardCount :
      (forwardEdges extra).count (source, target) =
        if (source, target) ∈ forwardEdges extra then 1 else 0 :=
    (forwardEdges_nodup extra).count
  have singleCount :
      (anchorSingleEdges extra).count (source, target) =
        if (source, target) ∈ anchorSingleEdges extra then 1 else 0 :=
    (anchorSingleEdges_nodup extra).count
  rw [forwardCount, singleCount]
  by_cases forward : (source, target) ∈ forwardEdges extra
  · have single :
        (source, target) ∉ anchorSingleEdges extra :=
      forwardEdges_disjoint_anchorSingleEdges forward
    simp [forward, single]
  · by_cases single : (source, target) ∈ anchorSingleEdges extra
    · simp [forward, single]
    · simp [forward, single]

/-- No directed adjacent pair occurs three times in a Trahtman anchor.
Forward edges occur twice, reverse edges once, and the four separator
boundary edges once. -/
theorem anchor_adjacent_pair_count_le_two
    (extra source target : Nat) :
    (anchor extra).adjacentPairs.count (source, target) ≤ 2 := by
  rw [anchor_adjacentPairs]
  simp only [List.count_append]
  have forwardCount :
      (forwardEdges extra).count (source, target) =
        if (source, target) ∈ forwardEdges extra then 1 else 0 :=
    (forwardEdges_nodup extra).count
  have reverseCount :
      (anchorSingleEdges extra).count (source, target) =
        if (source, target) ∈ anchorSingleEdges extra then 1 else 0 :=
    (anchorSingleEdges_nodup extra).count
  rw [forwardCount, reverseCount]
  by_cases forward : (source, target) ∈ forwardEdges extra
  · have single :
        (source, target) ∉ anchorSingleEdges extra :=
      forwardEdges_disjoint_anchorSingleEdges forward
    simp [forward, single]
  · by_cases single : (source, target) ∈ anchorSingleEdges extra
    · simp [forward, single]
    · simp [forward, single]

private theorem adjacentPairsList_count_append_ge
    (left right : List Nat) (edge : Nat × Nat) :
    (adjacentPairsList left).count edge +
        (adjacentPairsList right).count edge ≤
      (adjacentPairsList (left ++ right)).count edge := by
  cases left with
  | nil => simp [adjacentPairsList]
  | cons leftHead leftTail =>
      cases right with
      | nil => simp [adjacentPairsList]
      | cons rightHead rightTail =>
          change
            (Word.adjacentPairsFrom leftHead leftTail).count edge +
                (Word.adjacentPairsFrom rightHead rightTail).count edge ≤
              (Word.adjacentPairsFrom leftHead
                (leftTail ++ rightHead :: rightTail)).count edge
          rw [Word.adjacentPairsFrom_append]
          simp only [List.count_append, List.count_cons]
          omega

private theorem adjacent_pair_count_mul_le_flatMap_count
    (source : List Nat) (images : Nat → List Nat)
    (sourceLetter : Nat) (edge : Nat × Nat) :
    source.count sourceLetter *
        (adjacentPairsList (images sourceLetter)).count edge ≤
      (adjacentPairsList (source.flatMap images)).count edge := by
  induction source with
  | nil => simp [adjacentPairsList]
  | cons first rest ih =>
      simp only [List.flatMap_cons, List.count_cons]
      have appendBound :=
        adjacentPairsList_count_append_ge
          (images first) (rest.flatMap images) edge
      by_cases equality : first = sourceLetter
      · subst first
        simp only [beq_self_eq_true, if_true]
        calc
          (rest.count sourceLetter + 1) *
                (adjacentPairsList
                  (images sourceLetter)).count edge =
              (adjacentPairsList
                  (images sourceLetter)).count edge +
                rest.count sourceLetter *
                  (adjacentPairsList
                    (images sourceLetter)).count edge := by
            rw [Nat.add_mul]
            simp [Nat.add_comm]
          _ ≤
              (adjacentPairsList
                  (images sourceLetter)).count edge +
                (adjacentPairsList
                  (rest.flatMap images)).count edge :=
            Nat.add_le_add_left ih _
          _ ≤
              (adjacentPairsList
                (images sourceLetter ++ rest.flatMap images)).count edge :=
            appendBound
      · simp only [beq_eq_false_iff_ne.mpr equality]
        exact Nat.le_trans ih
          (Nat.le_trans (Nat.le_add_left _ _) appendBound)

/-- Every internal edge in the image of an exactly twice-occurring source
variable is one of the forward indexed anchor edges. -/
theorem preimage_two_occurrence_image_edge_forward
    {bound : Nat} {word : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    {sourceLetter : Nat}
    (sourceCount : word.toList.count sourceLetter = 2)
    {edge : Nat × Nat}
    (edgeMember :
      edge ∈ (substitution sourceLetter).adjacentPairs) :
    edge.1 < 3 * bound + 1 ∧ edge.2 = edge.1 + 1 := by
  rcases edge with ⟨edgeSource, edgeTarget⟩
  have imageEdgePositive :
      1 ≤
        (substitution sourceLetter).adjacentPairs.count
          (edgeSource, edgeTarget) :=
    List.count_pos_iff.mpr edgeMember
  have repeatedEdge :=
    adjacent_pair_count_mul_le_flatMap_count word.toList
      (fun letter => (substitution letter).toList)
      sourceLetter (edgeSource, edgeTarget)
  rw [← Word.toList_bind, mapped] at repeatedEdge
  change
    word.toList.count sourceLetter *
        (substitution sourceLetter).adjacentPairs.count
          (edgeSource, edgeTarget) ≤
      (anchor (3 * bound)).adjacentPairs.count
        (edgeSource, edgeTarget) at repeatedEdge
  rw [sourceCount] at repeatedEdge
  have anchorUpper :=
    anchor_adjacent_pair_count_le_two
      (3 * bound) edgeSource edgeTarget
  have anchorCount :
      (anchor (3 * bound)).adjacentPairs.count
          (edgeSource, edgeTarget) = 2 := by
    omega
  exact
    (anchor_adjacent_pair_count_eq_two_iff
      (3 * bound) edgeSource edgeTarget).mp anchorCount

private theorem cons_eq_range'_of_adjacentPairsFrom_forward :
    ∀ (head : Nat) (tail : List Nat),
      (∀ edge ∈ Word.adjacentPairsFrom head tail,
        edge.2 = edge.1 + 1) →
      head :: tail = List.range' head (tail.length + 1)
  | head, [], _ => by simp
  | head, next :: rest, forward => by
      have nextEq : next = head + 1 := by
        have step := forward (head, next) (by
          simp [Word.adjacentPairsFrom])
        simpa using step
      subst next
      rw [List.length_cons, List.range'_succ]
      apply congrArg (List.cons head)
      apply cons_eq_range'_of_adjacentPairsFrom_forward
      intro edge edgeMember
      exact forward edge (by
        simp [Word.adjacentPairsFrom, edgeMember])

private theorem word_toList_eq_range'_of_adjacentPairs_forward
    (word : Word Nat)
    (forward :
      ∀ edge ∈ word.adjacentPairs,
        edge.2 = edge.1 + 1) :
    word.toList = List.range' word.head word.toList.length := by
  cases word with
  | mk head tail =>
      simpa [Word.toList, Word.adjacentPairs] using
        cons_eq_range'_of_adjacentPairsFrom_forward head tail forward

/-- The image of an exactly twice-occurring source variable is a consecutive
increasing interval starting at its head. -/
theorem preimage_two_occurrence_image_toList_interval
    {bound : Nat} {word : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    {sourceLetter : Nat}
    (sourceCount : word.toList.count sourceLetter = 2) :
    (substitution sourceLetter).toList =
      List.range' (substitution sourceLetter).head
        (substitution sourceLetter).toList.length := by
  apply word_toList_eq_range'_of_adjacentPairs_forward
  intro edge edgeMember
  exact
    (preimage_two_occurrence_image_edge_forward
      mapped sourceCount edgeMember).2

/-- The image of an exactly twice-occurring source variable has no repeated
letters. -/
theorem preimage_two_occurrence_image_nodup
    {bound : Nat} {word : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    {sourceLetter : Nat}
    (sourceCount : word.toList.count sourceLetter = 2) :
    (substitution sourceLetter).toList.Nodup := by
  rw [preimage_two_occurrence_image_toList_interval mapped sourceCount]
  exact List.nodup_range'

private theorem cons_eq_singleton_of_mem_of_forward_lt
    (target cutoff : Nat) (targetEq : target = cutoff + 1) :
    ∀ head tail,
      target ∈ head :: tail →
      (∀ edge ∈ Word.adjacentPairsFrom head tail,
        edge.1 < cutoff ∧ edge.2 = edge.1 + 1) →
      head :: tail = [target]
  | head, [], hmem, _ => by
      simp only [List.mem_singleton] at hmem
      subst head
      rfl
  | head, next :: tail, hmem, hedges => by
      have step : head < cutoff ∧ next = head + 1 :=
        hedges (head, next) (by simp [Word.adjacentPairsFrom])
      have tailEdges : ∀ edge ∈ Word.adjacentPairsFrom next tail,
          edge.1 < cutoff ∧ edge.2 = edge.1 + 1 := by
        intro edge hedge
        exact hedges edge (by simp [Word.adjacentPairsFrom, hedge])
      rcases List.mem_cons.mp hmem with rfl | hmem
      · omega
      · have tailEq := cons_eq_singleton_of_mem_of_forward_lt
          target cutoff targetEq next tail hmem tailEdges
        have nextEq : next = target := by
          simpa using congrArg List.head? tailEq
        omega

/-- An exactly twice-occurring source variable whose image contains the
anchor separator maps exactly to that separator. -/
theorem preimage_two_occurrence_separator_image_singleton
    {bound : Nat} {word : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    {sourceLetter : Nat}
    (sourceCount : word.toList.count sourceLetter = 2)
    (separatorMember :
      3 * bound + 2 ∈ (substitution sourceLetter).toList) :
    substitution sourceLetter =
      Word.singleton (3 * bound + 2) := by
  apply Word.toList_injective
  cases imageEq : substitution sourceLetter with
  | mk head tail =>
      apply cons_eq_singleton_of_mem_of_forward_lt
        (target := 3 * bound + 2) (cutoff := 3 * bound + 1)
      · omega
      · simpa [imageEq, Word.toList] using separatorMember
      · intro edge edgeMember
        apply preimage_two_occurrence_image_edge_forward mapped sourceCount
        simpa [imageEq, Word.adjacentPairs] using edgeMember

private theorem two_source_contributions_le_flatMap_count
    (source : List Nat) (images : Nat → List Nat)
    (firstSource secondSource marker : Nat)
    (different : firstSource ≠ secondSource) :
    source.count firstSource * (images firstSource).count marker +
        source.count secondSource * (images secondSource).count marker ≤
      (source.flatMap images).count marker := by
  induction source with
  | nil => simp
  | cons head rest ih =>
      simp only [List.flatMap_cons, List.count_append]
      by_cases headFirst : head = firstSource
      · subst head
        simp only [List.count_cons_self,
          List.count_cons_of_ne different]
        rw [Nat.add_mul]
        omega
      · by_cases headSecond : head = secondSource
        · subst head
          simp only [List.count_cons_self,
            List.count_cons_of_ne (Ne.symm different)]
          rw [Nat.add_mul]
          omega
        · rw [List.count_cons_of_ne headFirst,
            List.count_cons_of_ne headSecond]
          exact Nat.le_trans ih (Nat.le_add_left _ _)

/-- If a marker occurs in the images of two distinct source variables, both
source multiplicities contribute to its count in the flat-map image. -/
theorem two_source_count_add_le_flatMap_count_of_mem
    (source : List Nat) (images : Nat → List Nat)
    (firstSource secondSource marker : Nat)
    (different : firstSource ≠ secondSource)
    (firstMarker : marker ∈ images firstSource)
    (secondMarker : marker ∈ images secondSource) :
    source.count firstSource + source.count secondSource ≤
      (source.flatMap images).count marker := by
  have contributions :=
    two_source_contributions_le_flatMap_count source images
      firstSource secondSource marker different
  have firstPositive : 1 ≤ (images firstSource).count marker :=
    List.count_pos_iff.mpr firstMarker
  have secondPositive : 1 ≤ (images secondSource).count marker :=
    List.count_pos_iff.mpr secondMarker
  exact Nat.le_trans
    (Nat.add_le_add
      (Nat.le_mul_of_pos_right _ firstPositive)
      (Nat.le_mul_of_pos_right _ secondPositive))
    contributions

private theorem word_eq_singleton_of_adjacentPairs_eq_nil
    (word : Word Nat)
    (noEdges : word.adjacentPairs = []) :
    word = Word.singleton word.head := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => rfl
      | cons next rest =>
          simp [Word.adjacentPairs, Word.adjacentPairsFrom] at noEdges

/-- The image of a source variable occurring at least three times is forced
to be a single indexed marker. Any internal image edge would occur once in
each copy, contradicting the anchor's adjacent-pair bound. -/
theorem preimage_three_le_occurrence_image_singleton
    {bound : Nat} {word : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    {sourceLetter : Nat}
    (sourceCount : 3 ≤ word.toList.count sourceLetter) :
    substitution sourceLetter =
      Word.singleton (substitution sourceLetter).head := by
  apply word_eq_singleton_of_adjacentPairs_eq_nil
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro edge edgeMember
  have imageEdgePositive :
      1 ≤
        (substitution sourceLetter).adjacentPairs.count edge :=
    List.count_pos_iff.mpr edgeMember
  have repeatedEdge :=
    adjacent_pair_count_mul_le_flatMap_count word.toList
      (fun letter => (substitution letter).toList)
      sourceLetter edge
  rw [← Word.toList_bind, mapped] at repeatedEdge
  change
    word.toList.count sourceLetter *
        (substitution sourceLetter).adjacentPairs.count edge ≤
      (anchor (3 * bound)).adjacentPairs.count edge at repeatedEdge
  have anchorBound :=
    anchor_adjacent_pair_count_le_two
      (3 * bound) edge.1 edge.2
  have anchorBound' :
      (anchor (3 * bound)).adjacentPairs.count edge ≤ 2 := by
    simpa using anchorBound
  have repeatedEdgeThree :
      3 ≤
        word.toList.count sourceLetter *
          (substitution sourceLetter).adjacentPairs.count edge := by
    have productBound :=
      Nat.mul_le_mul sourceCount imageEdgePositive
    simpa using productBound
  omega

/-- Exact-three specialization used by the anchor-preimage case split. -/
theorem preimage_three_occurrence_image_singleton
    {bound : Nat} {word : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    {sourceLetter : Nat}
    (sourceCount : word.toList.count sourceLetter = 3) :
    substitution sourceLetter =
      Word.singleton (substitution sourceLetter).head :=
  preimage_three_le_occurrence_image_singleton mapped (by omega)

/-- A source variable occurring exactly three times maps to an indexed anchor
marker, not to the distinguished separator. -/
theorem preimage_three_occurrence_image_head_lt
    {bound : Nat} {word : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    {sourceLetter : Nat}
    (sourceCount : word.toList.count sourceLetter = 3) :
    (substitution sourceLetter).head < 3 * bound + 2 := by
  have imageSingleton :=
    preimage_three_occurrence_image_singleton mapped sourceCount
  have markerMember :
      (substitution sourceLetter).head ∈
        (substitution sourceLetter).toList := by
    rw [imageSingleton]
    simp
  have occurrenceBound :=
    count_le_flatMap_count_of_mem word.toList
      (fun letter => (substitution letter).toList)
      sourceLetter (substitution sourceLetter).head markerMember
  rw [← Word.toList_bind, mapped] at occurrenceBound
  have markerCount :
      3 ≤
        (anchor (3 * bound)).toList.count
          (substitution sourceLetter).head := by
    simpa [sourceCount] using occurrenceBound
  have notSeparator :
      (substitution sourceLetter).head ≠ 3 * bound + 2 := by
    intro equality
    rw [equality, anchor_separator_count_eq_two] at markerCount
    omega
  apply Decidable.byContradiction
  intro notIndexed
  rw [anchor_toList] at markerCount
  have separatorNotMarker :
      3 * bound + 2 ≠ (substitution sourceLetter).head :=
    Ne.symm notSeparator
  simp [notIndexed, separatorNotMarker] at markerCount

/-- A source variable occurring exactly three times exhausts all occurrences
of its indexed image marker. No distinct source variable occurring in the
source word can contain that marker in its substitution image. -/
theorem preimage_three_occurrence_image_head_not_mem_of_ne
    {bound : Nat} {word : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    {sourceLetter otherLetter : Nat}
    (sourceCount : word.toList.count sourceLetter = 3)
    (different : sourceLetter ≠ otherLetter)
    (otherMember : otherLetter ∈ word.toList) :
    (substitution sourceLetter).head ∉
      (substitution otherLetter).toList := by
  intro otherImage
  have imageSingleton :=
    preimage_three_occurrence_image_singleton mapped sourceCount
  have sourceImage :
      (substitution sourceLetter).head ∈
        (substitution sourceLetter).toList := by
    rw [imageSingleton]
    simp
  have totalBound :=
    two_source_count_add_le_flatMap_count_of_mem word.toList
      (fun letter => (substitution letter).toList)
      sourceLetter otherLetter (substitution sourceLetter).head
      different sourceImage otherImage
  rw [← Word.toList_bind, mapped] at totalBound
  have markerIndexed :=
    preimage_three_occurrence_image_head_lt mapped sourceCount
  have markerCount :
      (anchor (3 * bound)).toList.count
          (substitution sourceLetter).head = 3 :=
    anchor_indexed_count_eq_three markerIndexed
  have otherCountPositive :
      1 ≤ word.toList.count otherLetter :=
    List.count_pos_iff.mpr otherMember
  rw [sourceCount, markerCount] at totalBound
  omega

/-- Every source variable with a non-singleton image occurs at most twice.
Thus the remaining three-occurrence branch consists entirely of variables
mapped to single anchor markers. -/
theorem preimage_nonsingleton_image_count_le_two
    {bound : Nat} {word : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    {sourceLetter : Nat}
    (nonsingleton :
      substitution sourceLetter ≠
        Word.singleton (substitution sourceLetter).head) :
    word.toList.count sourceLetter ≤ 2 := by
  apply Nat.lt_succ_iff.mp
  apply Decidable.byContradiction
  intro notLess
  apply nonsingleton
  exact preimage_three_le_occurrence_image_singleton mapped (by omega)

/-- Once both words are known to be 2-limited, deletion marked-digraph
equivalence preserves exact occurrence counts, not only the
zero/one/multiple trichotomy. -/
theorem sameDeletionMarkedDigraph_count_eq_of_twoLimited
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    (leftLimited : TwoLimitedList left.toList)
    (rightLimited : TwoLimitedList right.toList)
    (letter : Nat) :
    right.toList.count letter = left.toList.count letter := by
  have leftZero :=
    sameDeletionMarkedDigraph_count_eq_zero_iff same letter
  have leftOne :=
    sameDeletionMarkedDigraph_count_eq_one_iff same letter
  have leftTwo :=
    sameDeletionMarkedDigraph_two_le_count_iff same letter
  have leftBound := leftLimited letter
  have rightBound := rightLimited letter
  omega

private theorem count_filter_le
    (letters : List Nat) (keep : Nat → Bool) (letter : Nat) :
    (letters.filter keep).count letter ≤ letters.count letter := by
  induction letters with
  | nil => simp
  | cons first rest ih =>
      by_cases kept : keep first
      · rw [List.filter_cons, if_pos kept]
        by_cases equality : first = letter
        · subst first
          simp only [List.count_cons_self]
          omega
        · simp [equality]
          exact ih
      · rw [List.filter_cons, if_neg kept]
        by_cases equality : first = letter
        · subst first
          simp only [List.count_cons_self]
          omega
        · simpa [equality] using ih

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
      have headCases : head = first ∨ head = second :=
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

private theorem list_shape_le_four
    {letters : List Nat}
    (bound : letters.length ≤ 4) :
    letters = [] ∨
      (∃ a, letters = [a]) ∨
      (∃ a b, letters = [a, b]) ∨
      (∃ a b c, letters = [a, b, c]) ∨
      ∃ a b c d, letters = [a, b, c, d] := by
  cases letters with
  | nil => exact Or.inl rfl
  | cons a rest =>
      right
      cases rest with
      | nil => exact Or.inl ⟨a, rfl⟩
      | cons b rest =>
          right
          cases rest with
          | nil => exact Or.inl ⟨a, b, rfl⟩
          | cons c rest =>
              right
              cases rest with
              | nil => exact Or.inl ⟨a, b, c, rfl⟩
              | cons d rest =>
                  right
                  cases rest with
                  | nil => exact ⟨a, b, c, d, rfl⟩
                  | cons e rest =>
                      simp at bound

private theorem count_le_succ_nonTarget_length_of_no_selfEdge :
    ∀ {target : Nat} {letters : List Nat},
      (target, target) ∉ adjacentPairsList letters →
      letters.count target ≤
        (letters.filter fun letter => letter != target).length + 1
  | target, [], _ => by simp
  | target, head :: tail, noSelf => by
      by_cases headTarget : head = target
      · subst head
        cases tail with
        | nil => simp
        | cons next rest =>
            have nextNeTarget : next ≠ target := by
              intro equality
              subst next
              exact noSelf (by
                simp [adjacentPairsList, Word.adjacentPairsFrom])
            have restNoSelf :
                (target, target) ∉ adjacentPairsList rest := by
              intro member
              apply noSelf
              cases rest with
              | nil => simp [adjacentPairsList] at member
              | cons restHead restTail =>
                  simpa [adjacentPairsList,
                    Word.adjacentPairsFrom] using
                    List.mem_cons_of_mem
                      (target, next)
                      (List.mem_cons_of_mem
                        (next, restHead)
                        member)
            have restBound :=
              count_le_succ_nonTarget_length_of_no_selfEdge
                restNoSelf
            simp [nextNeTarget, Ne.symm nextNeTarget]
            omega
      · have tailNoSelf :
            (target, target) ∉ adjacentPairsList tail := by
          intro member
          apply noSelf
          cases tail with
          | nil => simp [adjacentPairsList] at member
          | cons tailHead tailRest =>
              simpa [adjacentPairsList,
                Word.adjacentPairsFrom] using
                List.mem_cons_of_mem
                  (head, tailHead)
                  member
        have tailBound :=
          count_le_succ_nonTarget_length_of_no_selfEdge
            tailNoSelf
        simp [headTarget]
        omega

private theorem length_eq_three_counts_of_mem
    {first second third : Nat} {letters : List Nat}
    (firstNeSecond : first ≠ second)
    (firstNeThird : first ≠ third)
    (secondNeThird : second ≠ third)
    (only :
      ∀ letter, letter ∈ letters →
        letter = first ∨ letter = second ∨ letter = third) :
    letters.length =
      letters.count first + letters.count second +
        letters.count third := by
  induction letters with
  | nil => simp
  | cons head tail ih =>
      have headCases :
          head = first ∨ head = second ∨ head = third :=
        only head (by simp)
      have tailOnly :
          ∀ letter, letter ∈ tail →
            letter = first ∨ letter = second ∨ letter = third := by
        intro letter member
        exact only letter (by simp [member])
      simp only [List.length_cons, List.count_cons]
      rw [ih tailOnly]
      rcases headCases with equality | equality | equality
      · subst head
        simp [firstNeSecond, firstNeThird]
        omega
      · subst head
        simp [Ne.symm firstNeSecond, secondNeThird]
        omega
      · subst head
        simp [Ne.symm firstNeThird, Ne.symm secondNeThird]
        omega

private theorem two_singleton_separators_target_count_eq_three
    {target controller1 controller2 : Nat} {right : List Nat}
    (targetNeController1 : target ≠ controller1)
    (targetNeController2 : target ≠ controller2)
    (controller1NeController2 : controller1 ≠ controller2)
    (rightOnly :
      ∀ letter, letter ∈ right →
        letter = target ∨
          letter = controller1 ∨ letter = controller2)
    (targetLower : 2 ≤ right.count target)
    (targetUpper : right.count target ≤ 3)
    (controller1Count : right.count controller1 = 1)
    (controller2Count : right.count controller2 = 1)
    (same :
      SameMarkedDigraphList
        [target, controller1, target, controller2, target] right) :
    right.count target = 3 := by
  have targetCases :
      right.count target = 2 ∨ right.count target = 3 := by
    omega
  rcases targetCases with targetCount | targetCount
  · have rightLength :
        right.length =
          right.count target + right.count controller1 +
            right.count controller2 :=
      length_eq_three_counts_of_mem
        targetNeController1 targetNeController2
        controller1NeController2 rightOnly
    have lengthFour : right.length = 4 := by
      rw [rightLength, targetCount, controller1Count, controller2Count]
    rcases list_shape_le_four (letters := right) (by omega) with
        rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩ |
          ⟨a, b, c, rfl⟩ | ⟨a, b, c, d, rfl⟩
    · simp at lengthFour
    · simp at lengthFour
    · simp at lengthFour
    · simp at lengthFour
    · have aEq : a = target := by
        simpa [SameMarkedDigraphList] using same.1.symm
      have dEq : d = target := by
        simpa [SameMarkedDigraphList] using same.2.1.symm
      subst a
      subst d
      have bCases := rightOnly b (by simp)
      have cCases := rightOnly c (by simp)
      have edgeTargetController1 :=
        same.2.2.2 target controller1
      have edgeController1Target :=
        same.2.2.2 controller1 target
      have edgeTargetController2 :=
        same.2.2.2 target controller2
      have edgeController2Target :=
        same.2.2.2 controller2 target
      rcases bCases with bTarget | bController1 | bController2 <;>
        rcases cCases with cTarget | cController1 | cController2 <;>
        subst b <;> subst c <;>
        simp_all [SameMarkedDigraphList, adjacentPairsList,
          Word.adjacentPairsFrom, targetNeController1,
          targetNeController2, controller1NeController2,
          Ne.symm targetNeController1,
          Ne.symm targetNeController2,
          Ne.symm controller1NeController2]
  · exact targetCount

private theorem alternating_five_target_count_eq_three
    {target controller : Nat} {right : List Nat}
    (different : target ≠ controller)
    (rightOnly :
      ∀ letter, letter ∈ right →
        letter = target ∨ letter = controller)
    (targetLower : 2 ≤ right.count target)
    (targetUpper : right.count target ≤ 3)
    (controllerCount : right.count controller = 2)
    (same :
      SameMarkedDigraphList
        [target, controller, target, controller, target] right) :
    right.count target = 3 := by
  have targetCases :
      right.count target = 2 ∨ right.count target = 3 := by
    omega
  rcases targetCases with targetCount | targetCount
  · have rightLength :
        right.length =
          right.count target + right.count controller :=
      length_eq_two_counts_of_mem different rightOnly
    have lengthFour : right.length = 4 := by
      rw [rightLength, targetCount, controllerCount]
    rcases list_shape_le_four (letters := right) (by omega) with
        rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩ |
          ⟨a, b, c, rfl⟩ | ⟨a, b, c, d, rfl⟩ <;>
      simp at lengthFour <;>
      simp [List.mem_cons] at rightOnly <;>
      have edgeTargetTarget := same.2.2.2 target target <;>
      have edgeTargetController := same.2.2.2 target controller <;>
      have edgeControllerTarget := same.2.2.2 controller target <;>
      have edgeControllerController :=
        same.2.2.2 controller controller <;>
      simp [SameMarkedDigraphList, adjacentPairsList,
        Word.adjacentPairsFrom, List.head?, List.getLast?,
        List.count_nil, List.count_cons, List.mem_cons,
        Prod.mk.injEq, different, Ne.symm different] at same targetCount controllerCount rightOnly edgeTargetTarget edgeTargetController edgeControllerTarget edgeControllerController ⊢ <;>
      grind
  · exact targetCount

private theorem twoLetter_markedDigraph_eq
    {first second : Nat} {left right : List Nat}
    (different : first ≠ second)
    (leftOnly :
      ∀ letter, letter ∈ left →
        letter = first ∨ letter = second)
    (rightOnly :
      ∀ letter, letter ∈ right →
        letter = first ∨ letter = second)
    (leftLimited : TwoLimitedList left)
    (rightLimited : TwoLimitedList right)
    (sameFirstCount :
      right.count first = left.count first)
    (sameSecondCount :
      right.count second = left.count second)
    (same : SameMarkedDigraphList left right) :
    right = left := by
  have leftLength :
      left.length = left.count first + left.count second :=
    length_eq_two_counts_of_mem different leftOnly
  have rightLength :
      right.length = right.count first + right.count second :=
    length_eq_two_counts_of_mem different rightOnly
  have sameLength : right.length = left.length := by
    rw [rightLength, sameFirstCount, sameSecondCount, ← leftLength]
  have leftLengthBound : left.length ≤ 4 := by
    rw [leftLength]
    have firstBound := leftLimited first
    have secondBound := leftLimited second
    omega
  have rightLengthBound : right.length ≤ 4 := by
    rw [rightLength, sameFirstCount, sameSecondCount]
    have firstBound := leftLimited first
    have secondBound := leftLimited second
    omega
  rcases list_shape_le_four leftLengthBound with
      rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩ |
        ⟨a, b, c, rfl⟩ | ⟨a, b, c, d, rfl⟩ <;>
    rcases list_shape_le_four rightLengthBound with
      rfl | ⟨e, rfl⟩ | ⟨e, f, rfl⟩ |
        ⟨e, f, g, rfl⟩ | ⟨e, f, g, h, rfl⟩ <;>
    simp at sameLength <;>
    simp [List.mem_cons] at leftOnly rightOnly <;>
    have leftFirstBound := leftLimited first <;>
    have leftSecondBound := leftLimited second <;>
    have rightFirstBound := rightLimited first <;>
    have rightSecondBound := rightLimited second <;>
    have edgeFirstFirst := same.2.2.2 first first <;>
    have edgeFirstSecond := same.2.2.2 first second <;>
    have edgeSecondFirst := same.2.2.2 second first <;>
    have edgeSecondSecond := same.2.2.2 second second <;>
    simp [SameMarkedDigraphList, adjacentPairsList,
      Word.adjacentPairsFrom, List.head?, List.getLast?,
      List.count_nil, List.count_cons, List.mem_cons,
      Prod.mk.injEq] at sameFirstCount sameSecondCount leftFirstBound leftSecondBound rightFirstBound rightSecondBound same edgeFirstFirst edgeFirstSecond edgeSecondFirst edgeSecondSecond ⊢ <;>
    grind

private theorem filter_eq_replicate_count
    (letters : List Nat) (letter : Nat) :
    letters.filter (fun value => value == letter) =
      List.replicate (letters.count letter) letter := by
  induction letters with
  | nil => simp
  | cons first rest ih =>
      by_cases equality : first = letter
      · subst first
        simp [ih, List.replicate_succ]
      · simp [equality, ih]

private theorem filter_or_eq_eq_filter_eq_of_not_mem
    (letters : List Nat) (first second : Nat)
    (secondAbsent : second ∉ letters) :
    letters.filter
        (fun value => value == first || value == second) =
      letters.filter (fun value => value == first) := by
  apply List.filter_congr
  intro value valueMember
  have valueNeSecond : value ≠ second := by
    intro equality
    subst value
    exact secondAbsent valueMember
  simp [valueNeSecond]

private theorem anchor_indexed_separator_projection
    {extra marker : Nat}
    (indexed : marker < extra + 2) :
    (anchor extra).toList.filter
        (fun value => value == marker || value == extra + 2) =
      [marker, extra + 2, marker, extra + 2, marker] := by
  let keep :=
    fun value : Nat =>
      value == marker || value == extra + 2
  change (anchor extra).toList.filter keep = _
  have separatorAbsent :
      extra + 2 ∉ List.range (extra + 2) := by
    simp
  have forwardProjection :
      (List.range (extra + 2)).filter keep = [marker] := by
    have reduced :=
      filter_or_eq_eq_filter_eq_of_not_mem
        (List.range (extra + 2)) marker (extra + 2)
        separatorAbsent
    simpa [keep, filter_eq_replicate_count, indexed] using reduced
  have reverseProjection :
      ((List.range (extra + 2)).reverse).filter keep = [marker] := by
    simpa [List.filter_reverse, forwardProjection]
  rw [anchor_toList]
  simp only [List.filter_append, List.filter_cons, List.filter_nil]
  rw [forwardProjection, reverseProjection]
  simp [keep]

private theorem separator_mem_middle_blocks_of_projection
    {marker separator : Nat}
    (different : marker ≠ separator)
    {before middleFirst middleSecond after : List Nat}
    (beforeOnly :
      ∀ value, value ∈ before → value = separator)
    (middleFirstOnly :
      ∀ value, value ∈ middleFirst → value = separator)
    (projection :
      before ++
          marker :: (middleFirst ++
            marker :: (middleSecond ++ marker :: after)) =
        [marker, separator, marker, separator, marker]) :
    separator ∈ middleFirst ∧ separator ∈ middleSecond := by
  cases before with
  | cons first rest =>
      have firstEq : first = separator :=
        beforeOnly first (by simp)
      subst first
      have separatorEqMarker : separator = marker := by
        simpa using congrArg List.head? projection
      exact (different separatorEqMarker.symm).elim
  | nil =>
      have firstTail :
          middleFirst ++
              marker :: (middleSecond ++ marker :: after) =
            separator :: marker :: separator :: marker :: [] := by
        simpa only [List.nil_append, List.cons.injEq, true_and]
          using projection
      cases middleFirst with
      | nil =>
          have markerEqSeparator : marker = separator := by
            simpa using congrArg List.head? firstTail
          exact (different markerEqSeparator).elim
      | cons first rest =>
          have firstEq : first = separator := by
            simpa using congrArg List.head? firstTail
          subst first
          have afterFirst :
              rest ++
                  marker :: (middleSecond ++ marker :: after) =
                marker :: separator :: marker :: [] := by
            simpa only [List.cons_append, List.cons.injEq, true_and]
              using firstTail
          have restEmpty : rest = [] := by
            cases rest with
            | nil => rfl
            | cons next tail =>
                have nextEq : next = separator :=
                  middleFirstOnly next (by simp)
                subst next
                have separatorEqMarker : separator = marker := by
                  simpa using congrArg List.head? afterFirst
                exact (different separatorEqMarker.symm).elim
          subst rest
          have secondTail :
              middleSecond ++ marker :: after =
                separator :: marker :: [] := by
            simpa only [List.nil_append, List.cons.injEq, true_and]
              using afterFirst
          cases middleSecond with
          | nil =>
              have markerEqSeparator : marker = separator := by
                simpa using congrArg List.head? secondTail
              exact (different markerEqSeparator).elim
          | cons second rest =>
              have secondEq : second = separator := by
                simpa using congrArg List.head? secondTail
              subst second
              exact ⟨by simp, by simp⟩

/-- The two separator occurrences between the three copies of an indexed
marker have source-variable owners in the two corresponding source gaps.
Those owners either coincide and occur exactly twice, or are distinct
singleton variables. -/
theorem preimage_three_occurrence_separator_owners
    {bound : Nat} {word : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    {sourceLetter : Nat}
    (sourceCount : word.toList.count sourceLetter = 3) :
    ∃ before middleFirst middleSecond after
        firstOwner secondOwner,
      word.toList =
          before ++
            sourceLetter :: (middleFirst ++
              sourceLetter ::
                (middleSecond ++ sourceLetter :: after)) ∧
        sourceLetter ∉ before ∧
        sourceLetter ∉ middleFirst ∧
        sourceLetter ∉ middleSecond ∧
        sourceLetter ∉ after ∧
        firstOwner ∈ middleFirst ∧
        3 * bound + 2 ∈ (substitution firstOwner).toList ∧
        secondOwner ∈ middleSecond ∧
        3 * bound + 2 ∈ (substitution secondOwner).toList ∧
        ((firstOwner = secondOwner ∧
            word.toList.count firstOwner = 2) ∨
          (firstOwner ≠ secondOwner ∧
            word.toList.count firstOwner = 1 ∧
            word.toList.count secondOwner = 1)) := by
  obtain
    ⟨before, middleFirst, middleSecond, after,
      sourceNotBefore, sourceNotMiddleFirst,
      sourceNotMiddleSecond, sourceNotAfter, sourceSplit⟩ :=
    exists_three_occurrence_split_of_count_eq_three sourceCount
  let marker := (substitution sourceLetter).head
  let separator := 3 * bound + 2
  let images :=
    fun letter : Nat => (substitution letter).toList
  let keep :=
    fun value : Nat =>
      value == marker || value == separator
  have imageSingleton :
      images sourceLetter = [marker] := by
    simp only [images]
    rw [preimage_three_occurrence_image_singleton mapped sourceCount]
    rfl
  have markerIndexed : marker < 3 * bound + 2 := by
    simpa [marker] using
      preimage_three_occurrence_image_head_lt mapped sourceCount
  have markerNeSeparator : marker ≠ separator := by
    simp only [separator]
    omega
  have mappedList :
      word.toList.flatMap images =
        (anchor (3 * bound)).toList := by
    have listed := congrArg Word.toList mapped
    rw [Word.toList_bind] at listed
    simpa only [images] using listed
  have projection :
      (before.flatMap images).filter keep ++
          marker ::
            ((middleFirst.flatMap images).filter keep ++
              marker ::
                ((middleSecond.flatMap images).filter keep ++
                  marker :: (after.flatMap images).filter keep)) =
        [marker, separator, marker, separator, marker] := by
    calc
      _ = (word.toList.flatMap images).filter keep := by
        rw [sourceSplit]
        simp [List.flatMap_append, List.flatMap_cons, imageSingleton,
          List.filter_append, keep, List.append_assoc]
      _ = ((anchor (3 * bound)).toList).filter keep :=
        congrArg (List.filter keep) mappedList
      _ = [marker, separator, marker, separator, marker] := by
        simpa only [keep, separator] using
          (anchor_indexed_separator_projection
            (extra := 3 * bound) markerIndexed)
  have segmentOnlySeparator :
      ∀ segment : List Nat,
        sourceLetter ∉ segment →
        (∀ letter, letter ∈ segment → letter ∈ word.toList) →
        ∀ value,
          value ∈ (segment.flatMap images).filter keep →
            value = separator := by
    intro segment sourceAbsent segmentInWord value valueMember
    have imageMember := (List.mem_filter.mp valueMember).1
    have kept := (List.mem_filter.mp valueMember).2
    have valueCases :
        value = marker ∨ value = separator := by
      simpa only [keep, Bool.or_eq_true, beq_iff_eq] using kept
    rcases valueCases with valueMarker | valueSeparator
    · subst value
      rcases List.mem_flatMap.mp imageMember with
        ⟨owner, ownerMember, markerMember⟩
      have ownerDifferent : sourceLetter ≠ owner := by
        intro equality
        subst owner
        exact sourceAbsent ownerMember
      have markerAbsent :=
        preimage_three_occurrence_image_head_not_mem_of_ne
          mapped sourceCount ownerDifferent
            (segmentInWord owner ownerMember)
      exact
        (markerAbsent
          (by
            simpa only [images, marker] using markerMember)).elim
    · exact valueSeparator
  have beforeInWord :
      ∀ letter, letter ∈ before → letter ∈ word.toList := by
    intro letter member
    rw [sourceSplit]
    simp [member]
  have middleFirstInWord :
      ∀ letter, letter ∈ middleFirst → letter ∈ word.toList := by
    intro letter member
    rw [sourceSplit]
    simp [member]
  have middleSecondInWord :
      ∀ letter, letter ∈ middleSecond → letter ∈ word.toList := by
    intro letter member
    rw [sourceSplit]
    simp [member]
  have gapSeparators :
      separator ∈ (middleFirst.flatMap images).filter keep ∧
        separator ∈ (middleSecond.flatMap images).filter keep :=
    separator_mem_middle_blocks_of_projection
      (marker := marker) (separator := separator)
      markerNeSeparator
      (segmentOnlySeparator before sourceNotBefore beforeInWord)
      (segmentOnlySeparator middleFirst sourceNotMiddleFirst
        middleFirstInWord)
      projection
  have firstFlatMember :=
    (List.mem_filter.mp gapSeparators.1).1
  have secondFlatMember :=
    (List.mem_filter.mp gapSeparators.2).1
  rcases List.mem_flatMap.mp firstFlatMember with
    ⟨firstOwner, firstOwnerMember, firstSeparatorMember⟩
  rcases List.mem_flatMap.mp secondFlatMember with
    ⟨secondOwner, secondOwnerMember, secondSeparatorMember⟩
  have firstWordMember :=
    middleFirstInWord firstOwner firstOwnerMember
  have secondWordMember :=
    middleSecondInWord secondOwner secondOwnerMember
  have sourceNeFirstOwner : sourceLetter ≠ firstOwner := by
    intro equality
    subst firstOwner
    exact sourceNotMiddleFirst firstOwnerMember
  have ownerCountCases :
      (firstOwner = secondOwner ∧
          word.toList.count firstOwner = 2) ∨
        (firstOwner ≠ secondOwner ∧
          word.toList.count firstOwner = 1 ∧
          word.toList.count secondOwner = 1) := by
    by_cases ownersEqual : firstOwner = secondOwner
    · subst secondOwner
      have countLower :
          2 ≤ word.toList.count firstOwner := by
        have firstPositive :
            1 ≤ middleFirst.count firstOwner :=
          List.count_pos_iff.mpr firstOwnerMember
        have secondPositive :
            1 ≤ middleSecond.count firstOwner :=
          List.count_pos_iff.mpr secondOwnerMember
        rw [sourceSplit]
        simp [sourceNeFirstOwner, Ne.symm sourceNeFirstOwner]
        omega
      have countUpper :
          word.toList.count firstOwner ≤ 2 := by
        have contribution :=
          count_le_flatMap_count_of_mem word.toList images
            firstOwner separator firstSeparatorMember
        rw [mappedList] at contribution
        simpa only [separator, anchor_separator_count_eq_two]
          using contribution
      exact Or.inl ⟨rfl, by omega⟩
    · have totalContribution :=
        two_source_count_add_le_flatMap_count_of_mem
          word.toList images firstOwner secondOwner separator
          ownersEqual firstSeparatorMember secondSeparatorMember
      rw [mappedList] at totalContribution
      have totalBound :
          word.toList.count firstOwner +
              word.toList.count secondOwner ≤ 2 := by
        simpa only [separator, anchor_separator_count_eq_two]
          using totalContribution
      have firstPositive :
          1 ≤ word.toList.count firstOwner :=
        List.count_pos_iff.mpr firstWordMember
      have secondPositive :
          1 ≤ word.toList.count secondOwner :=
        List.count_pos_iff.mpr secondWordMember
      exact Or.inr ⟨ownersEqual, by omega, by omega⟩
  refine
    ⟨before, middleFirst, middleSecond, after,
      firstOwner, secondOwner, sourceSplit,
      sourceNotBefore, sourceNotMiddleFirst,
      sourceNotMiddleSecond, sourceNotAfter,
      firstOwnerMember, ?_, secondOwnerMember, ?_,
      ownerCountCases⟩
  · simpa only [images, separator] using firstSeparatorMember
  · simpa only [images, separator] using secondSeparatorMember

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

/-- Exact equality of each two-variable projection follows from deletion
marked-digraph equivalence once both ambient words are 2-limited. -/
theorem sameDeletionMarkedDigraph_pairProjection_eq_of_twoLimited
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    (leftLimited : TwoLimitedList left.toList)
    (rightLimited : TwoLimitedList right.toList)
    (first second : Nat) :
    right.toList.filter
        (fun value => value == first || value == second) =
      left.toList.filter
        (fun value => value == first || value == second) := by
  by_cases different : first = second
  · subst second
    have predicateEq :
        (fun value : Nat => value == first || value == first) =
          fun value => value == first := by
      funext value
      simp
    rw [predicateEq, filter_eq_replicate_count,
      filter_eq_replicate_count,
      sameDeletionMarkedDigraph_count_eq_of_twoLimited
        same leftLimited rightLimited first]
  · apply twoLetter_markedDigraph_eq different
    · intro letter member
      have kept := (List.mem_filter.mp member).2
      simpa only [Bool.or_eq_true, beq_iff_eq] using kept
    · intro letter member
      have kept := (List.mem_filter.mp member).2
      simpa only [Bool.or_eq_true, beq_iff_eq] using kept
    · intro letter
      exact Nat.le_trans
        (count_filter_le left.toList
          (fun value => value == first || value == second) letter)
        (leftLimited letter)
    · intro letter
      exact Nat.le_trans
        (count_filter_le right.toList
          (fun value => value == first || value == second) letter)
        (rightLimited letter)
    · rw [count_filter_of_kept, count_filter_of_kept,
        sameDeletionMarkedDigraph_count_eq_of_twoLimited
          same leftLimited rightLimited first]
      · simp
      · simp
    · rw [count_filter_of_kept, count_filter_of_kept,
        sameDeletionMarkedDigraph_count_eq_of_twoLimited
          same leftLimited rightLimited second]
      · simp
      · simp
    · exact same (fun value => value == first || value == second)

private theorem list_eq_of_pairProjections :
    ∀ {left right : List Nat},
      (∀ first second,
        right.filter
            (fun value => value == first || value == second) =
          left.filter
            (fun value => value == first || value == second)) →
      right = left
  | [], [], _ => rfl
  | [], head :: tail, samePairs => by
      have sameHead := samePairs head head
      simp at sameHead
  | head :: tail, [], samePairs => by
      have sameHead := samePairs head head
      simp at sameHead
  | leftHead :: leftTail, rightHead :: rightTail, samePairs => by
      have projectedHeads := samePairs leftHead rightHead
      have headsEqual :
          rightHead = leftHead := by
        have := congrArg List.head? projectedHeads
        simpa using this
      subst rightHead
      have sameTails :
          ∀ first second,
            rightTail.filter
                (fun value => value == first || value == second) =
              leftTail.filter
                (fun value => value == first || value == second) := by
        intro first second
        have projected := samePairs first second
        by_cases kept :
            leftHead == first || leftHead == second
        · simpa [kept] using projected
        · simpa [kept] using projected
      rw [list_eq_of_pairProjections sameTails]

/-- The complete deletion marked-digraph family is injective between
2-limited words.  This is the exact reconstruction theorem used after
anchor-local separators have ruled out third occurrences on the competing
word as well. -/
theorem sameDeletionMarkedDigraph_eq_of_twoLimited
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    (leftLimited : TwoLimitedList left.toList)
    (rightLimited : TwoLimitedList right.toList) :
    right = left := by
  apply Word.toList_injective
  apply list_eq_of_pairProjections
  intro first second
  exact
    sameDeletionMarkedDigraph_pairProjection_eq_of_twoLimited
      same leftLimited rightLimited first second

private theorem count_le_succ_other_count_of_no_selfEdge :
    ∀ {target controller : Nat} {letters : List Nat},
      target ≠ controller →
      (∀ letter, letter ∈ letters →
        letter = target ∨ letter = controller) →
      (target, target) ∉ adjacentPairsList letters →
      letters.count target ≤ letters.count controller + 1
  | target, controller, [], _, _, _ => by simp
  | target, controller, head :: tail, different, only, noSelf => by
      have headCases :
          head = target ∨ head = controller :=
        only head (by simp)
      have tailOnly :
          ∀ letter, letter ∈ tail →
            letter = target ∨ letter = controller := by
        intro letter member
        exact only letter (by simp [member])
      rcases headCases with headEq | headEq
      · subst head
        cases tail with
        | nil => simp [different]
        | cons next rest =>
            have nextCases :
                next = target ∨ next = controller :=
              tailOnly next (by simp)
            rcases nextCases with nextEq | nextEq
            · subst next
              exact False.elim (noSelf (by
                simp [adjacentPairsList, Word.adjacentPairsFrom]))
            · subst next
              have restOnly :
                  ∀ letter, letter ∈ rest →
                    letter = target ∨ letter = controller := by
                intro letter member
                exact tailOnly letter (by simp [member])
              have restNoSelf :
                  (target, target) ∉
                    adjacentPairsList rest := by
                intro member
                apply noSelf
                cases rest with
                | nil => simp [adjacentPairsList] at member
                | cons restHead restTail =>
                    simpa [adjacentPairsList,
                      Word.adjacentPairsFrom] using
                      List.mem_cons_of_mem
                        (target, controller)
                        (List.mem_cons_of_mem
                          (controller, restHead)
                          member)
              have restBound :=
                count_le_succ_other_count_of_no_selfEdge
                  different restOnly restNoSelf
              simpa [different, Ne.symm different,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                Nat.add_le_add_right restBound 1
      · subst head
        have tailNoSelf :
            (target, target) ∉ adjacentPairsList tail := by
          intro member
          apply noSelf
          cases tail with
          | nil => simp [adjacentPairsList] at member
          | cons tailHead tailRest =>
              simpa [adjacentPairsList,
                Word.adjacentPairsFrom] using
                List.mem_cons_of_mem
                  (controller, tailHead)
                  member
        have tailBound :=
          count_le_succ_other_count_of_no_selfEdge
            different tailOnly tailNoSelf
        simp [Ne.symm different]
        omega

private theorem count_le_other_count_of_head_controller
    {target controller : Nat} {letters : List Nat}
    (different : target ≠ controller)
    (only :
      ∀ letter, letter ∈ letters →
        letter = target ∨ letter = controller)
    (headController : letters.head? = some controller)
    (noSelf :
      (target, target) ∉ adjacentPairsList letters) :
    letters.count target ≤ letters.count controller := by
  cases letters with
  | nil => simp at headController
  | cons head tail =>
      have headEq : head = controller := by
        simpa using headController
      subst head
      have tailOnly :
          ∀ letter, letter ∈ tail →
            letter = target ∨ letter = controller := by
        intro letter member
        exact only letter (by simp [member])
      have tailNoSelf :
          (target, target) ∉ adjacentPairsList tail := by
        intro member
        apply noSelf
        cases tail with
        | nil => simp [adjacentPairsList] at member
        | cons tailHead tailRest =>
            simpa [adjacentPairsList,
              Word.adjacentPairsFrom] using
              List.mem_cons_of_mem
                (controller, tailHead)
                member
      have tailBound :=
        count_le_succ_other_count_of_no_selfEdge
          different tailOnly tailNoSelf
      simpa [different, Ne.symm different] using tailBound

private theorem selfEdge_iff_adjacent_pair :
    ∀ (letters : List Nat) (letter : Nat),
      (letter, letter) ∈ adjacentPairsList letters ↔
        ∃ pre post,
          letters = pre ++ letter :: letter :: post
  | [], _ => by simp [adjacentPairsList]
  | [head], letter => by
      constructor
      · simp [adjacentPairsList, Word.adjacentPairsFrom]
      · rintro ⟨pre, post, split⟩
        have lengths := congrArg List.length split
        simp at lengths
        omega
  | first :: second :: rest, letter => by
      rw [show
        adjacentPairsList (first :: second :: rest) =
          (first, second) ::
            adjacentPairsList (second :: rest) by
          rfl]
      rw [List.mem_cons, selfEdge_iff_adjacent_pair]
      constructor
      · intro occurrence
        rcases occurrence with pairEq | ⟨pre, post, split⟩
        · have firstEq : first = letter := by
            exact (congrArg Prod.fst pairEq).symm
          have secondEq : second = letter := by
            exact (congrArg Prod.snd pairEq).symm
          subst first
          subst second
          exact ⟨[], rest, rfl⟩
        · exact ⟨first :: pre, post, by simp [split]⟩
      · rintro ⟨pre, post, split⟩
        cases pre with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at split
            rcases split with ⟨firstEq, secondEq, restEq⟩
            subst first
            subst second
            subst rest
            exact Or.inl rfl
        | cons preHead preTail =>
            right
            refine ⟨preTail, post, ?_⟩
            simp only [List.cons_append, List.cons.injEq] at split
            exact split.2

private theorem noSelfEdge_reverse
    {letters : List Nat} {letter : Nat}
    (noSelf :
      (letter, letter) ∉ adjacentPairsList letters) :
    (letter, letter) ∉ adjacentPairsList letters.reverse := by
  intro reversedEdge
  obtain ⟨pre, post, reversedSplit⟩ :=
    (selfEdge_iff_adjacent_pair letters.reverse letter).mp
      reversedEdge
  apply noSelf
  apply (selfEdge_iff_adjacent_pair letters letter).mpr
  refine ⟨post.reverse, pre.reverse, ?_⟩
  have originalSplit := congrArg List.reverse reversedSplit
  simpa [List.reverse_append, List.append_assoc] using
    originalSplit

private theorem count_le_other_count_of_last_controller
    {target controller : Nat} {letters : List Nat}
    (different : target ≠ controller)
    (only :
      ∀ letter, letter ∈ letters →
        letter = target ∨ letter = controller)
    (lastController : letters.getLast? = some controller)
    (noSelf :
      (target, target) ∉ adjacentPairsList letters) :
    letters.count target ≤ letters.count controller := by
  have reverseOnly :
      ∀ letter, letter ∈ letters.reverse →
        letter = target ∨ letter = controller := by
    intro letter member
    exact only letter (by simpa using member)
  have reverseHead :
      letters.reverse.head? = some controller := by
    simpa using lastController
  have reverseBound :=
    count_le_other_count_of_head_controller
      different reverseOnly reverseHead
      (noSelfEdge_reverse noSelf)
  simpa using reverseBound

/-- A deletion projection with no target self-edge bounds the target
multiplicity by one more than the controller multiplicity.  This is the
basic singleton-separator propagation step. -/
theorem sameDeletionMarkedDigraph_count_le_succ_controller
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    {target controller : Nat}
    (different : target ≠ controller)
    (sourceNoSelf :
      (target, target) ∉
        adjacentPairsList
          (left.toList.filter
            (fun value =>
              value == target || value == controller))) :
    right.toList.count target ≤
      right.toList.count controller + 1 := by
  let keep :=
    fun value : Nat =>
      value == target || value == controller
  have marked := same keep
  have rightNoSelf :
      (target, target) ∉
        adjacentPairsList (right.toList.filter keep) := by
    intro member
    exact sourceNoSelf ((marked.2.2.2 target target).mpr member)
  have rightOnly :
      ∀ letter, letter ∈ right.toList.filter keep →
        letter = target ∨ letter = controller := by
    intro letter member
    have kept := (List.mem_filter.mp member).2
    simpa only [keep, Bool.or_eq_true, beq_iff_eq] using kept
  have projectedBound :=
    count_le_succ_other_count_of_no_selfEdge
      different rightOnly rightNoSelf
  change
    (right.toList.filter keep).count target ≤
      (right.toList.filter keep).count controller + 1 at projectedBound
  rw [count_filter_of_kept, count_filter_of_kept] at projectedBound
  · exact projectedBound
  · simp [keep]
  · simp [keep]

/-- If the controller is also the marked head of the two-letter projection,
the extra `+1` disappears.  This supports overlapping local separator
chains after the first singleton has been established. -/
theorem sameDeletionMarkedDigraph_count_le_controller_of_head
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    {target controller : Nat}
    (different : target ≠ controller)
    (sourceHead :
      (left.toList.filter
        (fun value =>
          value == target || value == controller)).head? =
        some controller)
    (sourceNoSelf :
      (target, target) ∉
        adjacentPairsList
          (left.toList.filter
            (fun value =>
              value == target || value == controller))) :
    right.toList.count target ≤
      right.toList.count controller := by
  let keep :=
    fun value : Nat =>
      value == target || value == controller
  have marked := same keep
  have rightHead :
      (right.toList.filter keep).head? =
        some controller := by
    exact marked.1.symm.trans sourceHead
  have rightNoSelf :
      (target, target) ∉
        adjacentPairsList (right.toList.filter keep) := by
    intro member
    exact sourceNoSelf ((marked.2.2.2 target target).mpr member)
  have rightOnly :
      ∀ letter, letter ∈ right.toList.filter keep →
        letter = target ∨ letter = controller := by
    intro letter member
    have kept := (List.mem_filter.mp member).2
    simpa only [keep, Bool.or_eq_true, beq_iff_eq] using kept
  have projectedBound :=
    count_le_other_count_of_head_controller
      different rightOnly rightHead rightNoSelf
  change
    (right.toList.filter keep).count target ≤
      (right.toList.filter keep).count controller at projectedBound
  rw [count_filter_of_kept, count_filter_of_kept] at projectedBound
  · exact projectedBound
  · simp [keep]
  · simp [keep]

/-- Last-marked counterpart of
`sameDeletionMarkedDigraph_count_le_controller_of_head`. -/
theorem sameDeletionMarkedDigraph_count_le_controller_of_last
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    {target controller : Nat}
    (different : target ≠ controller)
    (sourceLast :
      (left.toList.filter
        (fun value =>
          value == target || value == controller)).getLast? =
        some controller)
    (sourceNoSelf :
      (target, target) ∉
        adjacentPairsList
          (left.toList.filter
            (fun value =>
              value == target || value == controller))) :
    right.toList.count target ≤
      right.toList.count controller := by
  let keep :=
    fun value : Nat =>
      value == target || value == controller
  have marked := same keep
  have rightLast :
      (right.toList.filter keep).getLast? =
        some controller := by
    exact marked.2.1.symm.trans sourceLast
  have rightNoSelf :
      (target, target) ∉
        adjacentPairsList (right.toList.filter keep) := by
    intro member
    exact sourceNoSelf ((marked.2.2.2 target target).mpr member)
  have rightOnly :
      ∀ letter, letter ∈ right.toList.filter keep →
        letter = target ∨ letter = controller := by
    intro letter member
    have kept := (List.mem_filter.mp member).2
    simpa only [keep, Bool.or_eq_true, beq_iff_eq] using kept
  have projectedBound :=
    count_le_other_count_of_last_controller
      different rightOnly rightLast rightNoSelf
  change
    (right.toList.filter keep).count target ≤
      (right.toList.filter keep).count controller at projectedBound
  rw [count_filter_of_kept, count_filter_of_kept] at projectedBound
  · exact projectedBound
  · simp [keep]
  · simp [keep]

/-- A reusable local multiplicity certificate.

* `singleton` records an exactly once-occurring variable;
* `singletonSeparator` uses such a variable to obtain the first
  `≤ 2` bound;
* `headController` and `lastController` propagate `≤ 2` along overlapping
  two-letter projections.

This is precisely the certificate shape used by the bound-six
no-global-pivot example. -/
inductive LocalTwoLimitedCertificate
    (word : Word Nat) : Nat → Prop
  | singleton (letter : Nat)
      (countOne : word.toList.count letter = 1) :
      LocalTwoLimitedCertificate word letter
  | singletonSeparator (target controller : Nat)
      (different : target ≠ controller)
      (controllerCountOne :
        word.toList.count controller = 1)
      (noSelf :
        (target, target) ∉
          adjacentPairsList
            (word.toList.filter
              (fun value =>
                value == target || value == controller))) :
      LocalTwoLimitedCertificate word target
  | headController (target controller : Nat)
      (different : target ≠ controller)
      (controllerCertificate :
        LocalTwoLimitedCertificate word controller)
      (headMarked :
        (word.toList.filter
          (fun value =>
            value == target || value == controller)).head? =
          some controller)
      (noSelf :
        (target, target) ∉
          adjacentPairsList
            (word.toList.filter
              (fun value =>
                value == target || value == controller))) :
      LocalTwoLimitedCertificate word target
  | lastController (target controller : Nat)
      (different : target ≠ controller)
      (controllerCertificate :
        LocalTwoLimitedCertificate word controller)
      (lastMarked :
        (word.toList.filter
          (fun value =>
            value == target || value == controller)).getLast? =
          some controller)
      (noSelf :
        (target, target) ∉
          adjacentPairsList
            (word.toList.filter
              (fun value =>
                value == target || value == controller))) :
      LocalTwoLimitedCertificate word target

/-- Local control certificates are stable enough under deletion
marked-digraph equivalence to force the certified variable to occur at most
twice on the competing side. -/
theorem LocalTwoLimitedCertificate.right_count_le_two
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    {letter : Nat}
    (certificate : LocalTwoLimitedCertificate left letter) :
    right.toList.count letter ≤ 2 := by
  induction certificate with
  | singleton letter countOne =>
      have rightOne :=
        (sameDeletionMarkedDigraph_count_eq_one_iff same letter).mp
          countOne
      omega
  | singletonSeparator target controller different
      controllerCountOne noSelf =>
      have rightControllerOne :=
        (sameDeletionMarkedDigraph_count_eq_one_iff
          same controller).mp controllerCountOne
      have targetBound :=
        sameDeletionMarkedDigraph_count_le_succ_controller
          same different noSelf
      omega
  | headController target controller different
      controllerCertificate headMarked noSelf ih =>
      have targetBound :=
        sameDeletionMarkedDigraph_count_le_controller_of_head
          same different headMarked noSelf
      omega
  | lastController target controller different
      controllerCertificate lastMarked noSelf ih =>
      have targetBound :=
        sameDeletionMarkedDigraph_count_le_controller_of_last
          same different lastMarked noSelf
      omega

/-- A certified source variable that occurs twice also occurs exactly twice
on every deletion-equivalent competing side. -/
theorem LocalTwoLimitedCertificate.right_count_eq_two
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    {letter : Nat}
    (certificate : LocalTwoLimitedCertificate left letter)
    (leftCountTwo : left.toList.count letter = 2) :
    right.toList.count letter = 2 := by
  have lower :
      2 ≤ right.toList.count letter :=
    (sameDeletionMarkedDigraph_two_le_count_iff
      same letter).mp (by omega)
  have upper := certificate.right_count_le_two same
  omega

/-- A local multiplicity certificate for the triple-occurrence branch.

The only constructor that introduces an extra occurrence,
`succOfTwoController`, requires a 2-limited controller.  Head- and
last-marked propagation introduce no `+1`, so they may recursively use a
3-limited controller. -/
inductive LocalThreeLimitedCertificate
    (word : Word Nat) : Nat → Prop
  | ofTwoLimited (letter : Nat)
      (certificate : LocalTwoLimitedCertificate word letter) :
      LocalThreeLimitedCertificate word letter
  | succOfTwoController (target controller : Nat)
      (different : target ≠ controller)
      (controllerCertificate :
        LocalTwoLimitedCertificate word controller)
      (noSelf :
        (target, target) ∉
          adjacentPairsList
            (word.toList.filter
              (fun value =>
                value == target || value == controller))) :
      LocalThreeLimitedCertificate word target
  | headController (target controller : Nat)
      (different : target ≠ controller)
      (controllerCertificate :
        LocalThreeLimitedCertificate word controller)
      (headMarked :
        (word.toList.filter
          (fun value =>
            value == target || value == controller)).head? =
          some controller)
      (noSelf :
        (target, target) ∉
          adjacentPairsList
            (word.toList.filter
              (fun value =>
                value == target || value == controller))) :
      LocalThreeLimitedCertificate word target
  | lastController (target controller : Nat)
      (different : target ≠ controller)
      (controllerCertificate :
        LocalThreeLimitedCertificate word controller)
      (lastMarked :
        (word.toList.filter
          (fun value =>
            value == target || value == controller)).getLast? =
          some controller)
      (noSelf :
        (target, target) ∉
          adjacentPairsList
            (word.toList.filter
              (fun value =>
                value == target || value == controller))) :
      LocalThreeLimitedCertificate word target

/-- Local 3-limited certificates bound the corresponding competing
multiplicity by three. -/
theorem LocalThreeLimitedCertificate.right_count_le_three
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    {letter : Nat}
    (certificate : LocalThreeLimitedCertificate left letter) :
    right.toList.count letter ≤ 3 := by
  induction certificate with
  | ofTwoLimited letter certificate =>
      have := certificate.right_count_le_two same
      omega
  | succOfTwoController target controller different
      controllerCertificate noSelf =>
      have controllerBound :=
        controllerCertificate.right_count_le_two same
      have targetBound :=
        sameDeletionMarkedDigraph_count_le_succ_controller
          same different noSelf
      omega
  | headController target controller different
      controllerCertificate headMarked noSelf ih =>
      have targetBound :=
        sameDeletionMarkedDigraph_count_le_controller_of_head
          same different headMarked noSelf
      omega
  | lastController target controller different
      controllerCertificate lastMarked noSelf ih =>
      have targetBound :=
        sameDeletionMarkedDigraph_count_le_controller_of_last
          same different lastMarked noSelf
      omega

/-- An alternating five-letter source projection transfers an exact triple
multiplicity when its controller has a local 2-limited certificate. -/
theorem right_count_eq_three_of_alternating_projection
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    {target controller : Nat}
    (different : target ≠ controller)
    (controllerCertificate :
      LocalTwoLimitedCertificate left controller)
    (projection :
      left.toList.filter
          (fun value =>
            value == target || value == controller) =
        [target, controller, target, controller, target]) :
    right.toList.count target = 3 := by
  let keep :=
    fun value : Nat =>
      value == target || value == controller
  have leftTargetCount :
      left.toList.count target = 3 := by
    have counted :=
      congrArg (fun letters => letters.count target) projection
    change
      (left.toList.filter keep).count target =
        [target, controller, target, controller, target].count target
      at counted
    rw [count_filter_of_kept] at counted
    · simpa [different, Ne.symm different] using counted
    · simp [keep]
  have leftControllerCount :
      left.toList.count controller = 2 := by
    have counted :=
      congrArg (fun letters => letters.count controller) projection
    change
      (left.toList.filter keep).count controller =
        [target, controller, target, controller, target].count controller
      at counted
    rw [count_filter_of_kept] at counted
    · simpa [different, Ne.symm different] using counted
    · simp [keep]
  have rightControllerCount :
      right.toList.count controller = 2 :=
    controllerCertificate.right_count_eq_two
      same leftControllerCount
  have targetLower :
      2 ≤ right.toList.count target :=
    (sameDeletionMarkedDigraph_two_le_count_iff
      same target).mp (by omega)
  have sourceNoSelf :
      (target, target) ∉
        adjacentPairsList (left.toList.filter keep) := by
    rw [projection]
    simp [adjacentPairsList, Word.adjacentPairsFrom, different]
  have targetUpper :
      right.toList.count target ≤ 3 := by
    have bound :=
      sameDeletionMarkedDigraph_count_le_succ_controller
        same different sourceNoSelf
    omega
  have marked := same keep
  rw [projection] at marked
  have rightOnly :
      ∀ letter, letter ∈ right.toList.filter keep →
        letter = target ∨ letter = controller := by
    intro letter member
    have kept := (List.mem_filter.mp member).2
    simpa only [keep, Bool.or_eq_true, beq_iff_eq] using kept
  have projectedTargetCount :
      (right.toList.filter keep).count target =
        right.toList.count target := by
    apply count_filter_of_kept
    simp [keep]
  have projectedControllerCount :
      (right.toList.filter keep).count controller =
        right.toList.count controller := by
    apply count_filter_of_kept
    simp [keep]
  have projectedExact :
      (right.toList.filter keep).count target = 3 := by
    apply alternating_five_target_count_eq_three
      different rightOnly
    · rwa [projectedTargetCount]
    · rwa [projectedTargetCount]
    · rwa [projectedControllerCount]
    · exact marked
  rwa [projectedTargetCount] at projectedExact

/-- Two distinct singleton separators between three source occurrences force
the target variable to occur exactly three times on every deletion-equivalent
word. -/
theorem right_count_eq_three_of_two_singleton_separators
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    {target controller1 controller2 : Nat}
    (targetNeController1 : target ≠ controller1)
    (targetNeController2 : target ≠ controller2)
    (controller1NeController2 : controller1 ≠ controller2)
    (controller1Count : left.toList.count controller1 = 1)
    (controller2Count : left.toList.count controller2 = 1)
    (projection :
      left.toList.filter
          (fun value =>
            value == target ||
              value == controller1 || value == controller2) =
        [target, controller1, target, controller2, target]) :
    right.toList.count target = 3 := by
  let keep :=
    fun value : Nat =>
      value == target ||
        value == controller1 || value == controller2
  have leftTargetCount :
      left.toList.count target = 3 := by
    have counted :=
      congrArg (fun letters => letters.count target) projection
    change
      (left.toList.filter keep).count target =
        [target, controller1, target, controller2, target].count target
      at counted
    rw [count_filter_of_kept] at counted
    · simpa [targetNeController1, targetNeController2,
        Ne.symm targetNeController1,
        Ne.symm targetNeController2] using counted
    · simp [keep]
  have rightController1Count :
      right.toList.count controller1 = 1 :=
    (sameDeletionMarkedDigraph_count_eq_one_iff
      same controller1).mp controller1Count
  have rightController2Count :
      right.toList.count controller2 = 1 :=
    (sameDeletionMarkedDigraph_count_eq_one_iff
      same controller2).mp controller2Count
  have targetLower :
      2 ≤ right.toList.count target :=
    (sameDeletionMarkedDigraph_two_le_count_iff
      same target).mp (by omega)
  have marked := same keep
  rw [projection] at marked
  have rightOnly :
      ∀ letter, letter ∈ right.toList.filter keep →
        letter = target ∨
          letter = controller1 ∨ letter = controller2 := by
    intro letter member
    have kept := (List.mem_filter.mp member).2
    have cases :
        (letter = target ∨ letter = controller1) ∨
          letter = controller2 := by
      simpa only [keep, Bool.or_eq_true, beq_iff_eq] using kept
    rcases cases with (equality | equality) | equality
    · exact Or.inl equality
    · exact Or.inr (Or.inl equality)
    · exact Or.inr (Or.inr equality)
  have projectedTargetCount :
      (right.toList.filter keep).count target =
        right.toList.count target := by
    apply count_filter_of_kept
    simp [keep]
  have projectedController1Count :
      (right.toList.filter keep).count controller1 =
        right.toList.count controller1 := by
    apply count_filter_of_kept
    simp [keep]
  have projectedController2Count :
      (right.toList.filter keep).count controller2 =
        right.toList.count controller2 := by
    apply count_filter_of_kept
    simp [keep]
  have sourceNoSelf :
      (target, target) ∉
        adjacentPairsList
          [target, controller1, target, controller2, target] := by
    simp [adjacentPairsList, Word.adjacentPairsFrom,
      targetNeController1, targetNeController2]
  have rightNoSelf :
      (target, target) ∉
        adjacentPairsList (right.toList.filter keep) := by
    intro member
    exact sourceNoSelf ((marked.2.2.2 target target).mpr member)
  have nonTargetOnly :
      ∀ letter,
        letter ∈
            (right.toList.filter keep).filter
              (fun value => value != target) →
          letter = controller1 ∨ letter = controller2 := by
    intro letter member
    have filtered := List.mem_filter.mp member
    have letterNeTarget : letter ≠ target := by
      simpa using filtered.2
    rcases rightOnly letter filtered.1 with
      equality | equality | equality
    · exact False.elim (letterNeTarget equality)
    · exact Or.inl equality
    · exact Or.inr equality
  have nonTargetLength :
      ((right.toList.filter keep).filter
          (fun value => value != target)).length =
        (right.toList.filter keep).count controller1 +
          (right.toList.filter keep).count controller2 := by
    have raw :=
      length_eq_two_counts_of_mem
        controller1NeController2 nonTargetOnly
    have controller1Kept :
        (fun value : Nat => value != target) controller1 = true := by
      simp [Ne.symm targetNeController1]
    have controller2Kept :
        (fun value : Nat => value != target) controller2 = true := by
      simp [Ne.symm targetNeController2]
    have filteredController1Count :
        ((right.toList.filter keep).filter
            (fun value => value != target)).count controller1 =
          (right.toList.filter keep).count controller1 :=
      count_filter_of_kept
        (right.toList.filter keep)
        (fun value => value != target) controller1 controller1Kept
    have filteredController2Count :
        ((right.toList.filter keep).filter
            (fun value => value != target)).count controller2 =
          (right.toList.filter keep).count controller2 :=
      count_filter_of_kept
        (right.toList.filter keep)
        (fun value => value != target) controller2 controller2Kept
    rw [filteredController1Count, filteredController2Count] at raw
    exact raw
  have targetUpper :
      right.toList.count target ≤ 3 := by
    have projectedBound :=
      count_le_succ_nonTarget_length_of_no_selfEdge rightNoSelf
    rw [nonTargetLength, projectedTargetCount,
      projectedController1Count, projectedController2Count,
      rightController1Count, rightController2Count] at projectedBound
    omega
  have projectedExact :
      (right.toList.filter keep).count target = 3 := by
    apply two_singleton_separators_target_count_eq_three
      targetNeController1 targetNeController2
      controller1NeController2 rightOnly
    · rwa [projectedTargetCount]
    · rwa [projectedTargetCount]
    · rwa [projectedController1Count]
    · rwa [projectedController2Count]
    · exact marked
  rwa [projectedTargetCount] at projectedExact

private theorem filter_eq_replicate_count_of_memwise_eq
    (letters : List Nat) (keep : Nat → Bool) (letter : Nat)
    (predicateEq :
      ∀ value, value ∈ letters →
        keep value = (value == letter)) :
    letters.filter keep =
      List.replicate (letters.count letter) letter := by
  calc
    letters.filter keep =
        letters.filter (fun value => value == letter) := by
      apply List.filter_congr
      intro value valueMember
      exact predicateEq value valueMember
    _ = List.replicate (letters.count letter) letter :=
      filter_eq_replicate_count letters letter

/-- A triple-occurrence anchor source variable remains triple-occurring in
every deletion-equivalent word once the only unresolved equal-owner branch
has local 2-limited control.

The callback is used only when the two extracted separator occurrences have
the same source owner. Distinct owners are forced to be singleton variables,
so the two-singleton transfer theorem applies without additional input. -/
theorem
    preimage_three_occurrence_right_count_eq_three_of_separator_owner_control
    {bound : Nat} {word other : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    {sourceLetter : Nat}
    (sourceCount : word.toList.count sourceLetter = 3)
    (same : SameDeletionMarkedDigraph word other)
    (separatorOwnerControl :
      ∀ {owner : Nat},
        owner ∈ word.toList →
        word.toList.count owner = 2 →
        3 * bound + 2 ∈ (substitution owner).toList →
        LocalTwoLimitedCertificate word owner) :
    other.toList.count sourceLetter = 3 := by
  obtain
    ⟨before, middleFirst, middleSecond, after,
      firstOwner, secondOwner, sourceSplit,
      sourceNotBefore, sourceNotMiddleFirst,
      sourceNotMiddleSecond, sourceNotAfter,
      firstOwnerMember, firstSeparatorMember,
      secondOwnerMember, secondSeparatorMember, ownerCases⟩ :=
    preimage_three_occurrence_separator_owners mapped sourceCount
  have sourceNeFirstOwner : sourceLetter ≠ firstOwner := by
    intro equality
    subst firstOwner
    exact sourceNotMiddleFirst firstOwnerMember
  have sourceNeSecondOwner : sourceLetter ≠ secondOwner := by
    intro equality
    subst secondOwner
    exact sourceNotMiddleSecond secondOwnerMember
  rcases ownerCases with
    ⟨ownersEqual, firstOwnerCount⟩ |
      ⟨ownersDifferent, firstOwnerCount, secondOwnerCount⟩
  · subst secondOwner
    have firstOwnerWordMember : firstOwner ∈ word.toList := by
      rw [sourceSplit]
      simp [firstOwnerMember]
    have firstOwnerCertificate :
        LocalTwoLimitedCertificate word firstOwner :=
      separatorOwnerControl firstOwnerWordMember
        firstOwnerCount firstSeparatorMember
    have ownerCounts := firstOwnerCount
    rw [sourceSplit] at ownerCounts
    simp [sourceNeFirstOwner, Ne.symm sourceNeFirstOwner] at ownerCounts
    have firstMiddlePositive :
        1 ≤ middleFirst.count firstOwner :=
      List.count_pos_iff.mpr firstOwnerMember
    have secondMiddlePositive :
        1 ≤ middleSecond.count firstOwner :=
      List.count_pos_iff.mpr secondOwnerMember
    have beforeOwnerCount : before.count firstOwner = 0 := by
      omega
    have firstMiddleOwnerCount :
        middleFirst.count firstOwner = 1 := by
      omega
    have secondMiddleOwnerCount :
        middleSecond.count firstOwner = 1 := by
      omega
    have afterOwnerCount : after.count firstOwner = 0 := by
      omega
    let keep :=
      fun value : Nat =>
        value == sourceLetter || value == firstOwner
    have beforeFilter : before.filter keep = [] := by
      have reduced :=
        filter_eq_replicate_count_of_memwise_eq
          before keep firstOwner (by
            intro value valueMember
            have valueNeSource : value ≠ sourceLetter := by
              intro equality
              subst value
              exact sourceNotBefore valueMember
            simp [keep, valueNeSource])
      simpa [beforeOwnerCount] using reduced
    have firstMiddleFilter :
        middleFirst.filter keep = [firstOwner] := by
      have reduced :=
        filter_eq_replicate_count_of_memwise_eq
          middleFirst keep firstOwner (by
            intro value valueMember
            have valueNeSource : value ≠ sourceLetter := by
              intro equality
              subst value
              exact sourceNotMiddleFirst valueMember
            simp [keep, valueNeSource])
      simpa [firstMiddleOwnerCount] using reduced
    have secondMiddleFilter :
        middleSecond.filter keep = [firstOwner] := by
      have reduced :=
        filter_eq_replicate_count_of_memwise_eq
          middleSecond keep firstOwner (by
            intro value valueMember
            have valueNeSource : value ≠ sourceLetter := by
              intro equality
              subst value
              exact sourceNotMiddleSecond valueMember
            simp [keep, valueNeSource])
      simpa [secondMiddleOwnerCount] using reduced
    have afterFilter : after.filter keep = [] := by
      have reduced :=
        filter_eq_replicate_count_of_memwise_eq
          after keep firstOwner (by
            intro value valueMember
            have valueNeSource : value ≠ sourceLetter := by
              intro equality
              subst value
              exact sourceNotAfter valueMember
            simp [keep, valueNeSource])
      simpa [afterOwnerCount] using reduced
    have projection :
        word.toList.filter keep =
          [sourceLetter, firstOwner, sourceLetter,
            firstOwner, sourceLetter] := by
      rw [sourceSplit]
      simp [List.filter_append, beforeFilter,
        firstMiddleFilter, secondMiddleFilter, afterFilter, keep]
    apply right_count_eq_three_of_alternating_projection
      same sourceNeFirstOwner firstOwnerCertificate
    simpa only [keep] using projection
  · have firstOwnerCounts := firstOwnerCount
    rw [sourceSplit] at firstOwnerCounts
    simp [sourceNeFirstOwner, Ne.symm sourceNeFirstOwner]
      at firstOwnerCounts
    have secondOwnerCounts := secondOwnerCount
    rw [sourceSplit] at secondOwnerCounts
    simp [sourceNeSecondOwner, Ne.symm sourceNeSecondOwner]
      at secondOwnerCounts
    have firstMiddlePositive :
        1 ≤ middleFirst.count firstOwner :=
      List.count_pos_iff.mpr firstOwnerMember
    have secondMiddlePositive :
        1 ≤ middleSecond.count secondOwner :=
      List.count_pos_iff.mpr secondOwnerMember
    have beforeFirstCount : before.count firstOwner = 0 := by
      omega
    have firstMiddleFirstCount :
        middleFirst.count firstOwner = 1 := by
      omega
    have secondMiddleFirstCount :
        middleSecond.count firstOwner = 0 := by
      omega
    have afterFirstCount : after.count firstOwner = 0 := by
      omega
    have beforeSecondCount : before.count secondOwner = 0 := by
      omega
    have firstMiddleSecondCount :
        middleFirst.count secondOwner = 0 := by
      omega
    have secondMiddleSecondCount :
        middleSecond.count secondOwner = 1 := by
      omega
    have afterSecondCount : after.count secondOwner = 0 := by
      omega
    have beforeSecondAbsent : secondOwner ∉ before :=
      List.count_eq_zero.mp beforeSecondCount
    have firstMiddleSecondAbsent : secondOwner ∉ middleFirst :=
      List.count_eq_zero.mp firstMiddleSecondCount
    have secondMiddleFirstAbsent : firstOwner ∉ middleSecond :=
      List.count_eq_zero.mp secondMiddleFirstCount
    have afterSecondAbsent : secondOwner ∉ after :=
      List.count_eq_zero.mp afterSecondCount
    let keep :=
      fun value : Nat =>
        value == sourceLetter ||
          value == firstOwner || value == secondOwner
    have beforeFilter : before.filter keep = [] := by
      have reduced :=
        filter_eq_replicate_count_of_memwise_eq
          before keep firstOwner (by
            intro value valueMember
            have valueNeSource : value ≠ sourceLetter := by
              intro equality
              subst value
              exact sourceNotBefore valueMember
            have valueNeSecond : value ≠ secondOwner := by
              intro equality
              subst value
              exact beforeSecondAbsent valueMember
            simp only [keep]
            rw [beq_eq_false_iff_ne.mpr valueNeSource,
              beq_eq_false_iff_ne.mpr valueNeSecond]
            simp)
      simpa [beforeFirstCount] using reduced
    have firstMiddleFilter :
        middleFirst.filter keep = [firstOwner] := by
      have reduced :=
        filter_eq_replicate_count_of_memwise_eq
          middleFirst keep firstOwner (by
            intro value valueMember
            have valueNeSource : value ≠ sourceLetter := by
              intro equality
              subst value
              exact sourceNotMiddleFirst valueMember
            have valueNeSecond : value ≠ secondOwner := by
              intro equality
              subst value
              exact firstMiddleSecondAbsent valueMember
            simp only [keep]
            rw [beq_eq_false_iff_ne.mpr valueNeSource,
              beq_eq_false_iff_ne.mpr valueNeSecond]
            simp)
      simpa [firstMiddleFirstCount] using reduced
    have secondMiddleFilter :
        middleSecond.filter keep = [secondOwner] := by
      have reduced :=
        filter_eq_replicate_count_of_memwise_eq
          middleSecond keep secondOwner (by
            intro value valueMember
            have valueNeSource : value ≠ sourceLetter := by
              intro equality
              subst value
              exact sourceNotMiddleSecond valueMember
            have valueNeFirst : value ≠ firstOwner := by
              intro equality
              subst value
              exact secondMiddleFirstAbsent valueMember
            simp [keep, valueNeSource, valueNeFirst])
      simpa [secondMiddleSecondCount] using reduced
    have afterFilter : after.filter keep = [] := by
      have reduced :=
        filter_eq_replicate_count_of_memwise_eq
          after keep firstOwner (by
            intro value valueMember
            have valueNeSource : value ≠ sourceLetter := by
              intro equality
              subst value
              exact sourceNotAfter valueMember
            have valueNeSecond : value ≠ secondOwner := by
              intro equality
              subst value
              exact afterSecondAbsent valueMember
            simp only [keep]
            rw [beq_eq_false_iff_ne.mpr valueNeSource,
              beq_eq_false_iff_ne.mpr valueNeSecond]
            simp)
      simpa [afterFirstCount] using reduced
    have projection :
        word.toList.filter keep =
          [sourceLetter, firstOwner, sourceLetter,
            secondOwner, sourceLetter] := by
      rw [sourceSplit]
      simp [List.filter_append, beforeFilter,
        firstMiddleFilter, secondMiddleFilter, afterFilter, keep]
    apply right_count_eq_three_of_two_singleton_separators
      same sourceNeFirstOwner sourceNeSecondOwner ownersDifferent
      firstOwnerCount secondOwnerCount
    simpa only [keep] using projection

/-- Exact source multiplicities are preserved for a fixed anchor preimage
when every exactly twice-occurring source variable has a local 2-limited
certificate. -/
theorem preimage_exact_count_preservation_of_two_occurrence_control
    {bound : Nat} {word other : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    (same : SameDeletionMarkedDigraph word other)
    (twoOccurrenceControl :
      ∀ letter,
        letter ∈ word.toList →
        word.toList.count letter = 2 →
        LocalTwoLimitedCertificate word letter) :
    ∀ letter,
      other.toList.count letter = word.toList.count letter := by
  intro letter
  have sourceLimited : ThreeLimitedList word.toList :=
    preimage_threeLimitedList mapped
  have sourceBound :=
    sourceLimited letter
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
  · have sourceMember : letter ∈ word.toList := by
      apply List.count_pos_iff.mp
      omega
    have certificate :=
      twoOccurrenceControl letter sourceMember sourceTwo
    have otherTwo :=
      certificate.right_count_eq_two same sourceTwo
    rw [sourceTwo, otherTwo]
  have sourceThree : word.toList.count letter = 3 := by
    omega
  have otherThree :=
    preimage_three_occurrence_right_count_eq_three_of_separator_owner_control
      mapped sourceThree same (by
        intro owner ownerMember ownerCount _separatorMember
        exact
          twoOccurrenceControl owner ownerMember ownerCount)
  rw [sourceThree, otherThree]

/-- A 2-limited source covered by local control certificates is rigid.
The certificates first prove that every deletion-equivalent competitor is
also 2-limited; exact reconstruction then follows from the two-variable
projection theorem. -/
theorem sameDeletionMarkedDigraph_eq_of_localTwoLimitedCover
    {left right : Word Nat}
    (same : SameDeletionMarkedDigraph left right)
    (leftLimited : TwoLimitedList left.toList)
    (covered :
      ∀ letter, letter ∈ left.toList →
        LocalTwoLimitedCertificate left letter) :
    right = left := by
  apply sameDeletionMarkedDigraph_eq_of_twoLimited same leftLimited
  intro letter
  by_cases member : letter ∈ left.toList
  · exact (covered letter member).right_count_le_two same
  · have leftZero :
        left.toList.count letter = 0 :=
      List.count_eq_zero.mpr member
    have rightZero :=
      (sameDeletionMarkedDigraph_count_eq_zero_iff
        same letter).mp leftZero
    omega

/-- The structural class isolated by the exact bound-two and bound-three
factorization searches.  The pivot occurs exactly once, and every other
variable occurs at most once on either side of it.  Thus a repeated variable
has one occurrence on each side of the pivot. -/
def SingletonPivotFactorization
    (pivot : Nat) (letters : List Nat) : Prop :=
  ∃ left right,
    letters = left ++ pivot :: right ∧
      left.Nodup ∧ right.Nodup ∧
      pivot ∉ left ∧ pivot ∉ right

/-- A corrected two-separator structural milestone.  The two separator
occurrences divide the word into three duplicate-free blocks, none of which
contains the separator. -/
def TwoSeparatorNodupFactorization
    (separator : Nat) (letters : List Nat) : Prop :=
  ∃ before middle after,
    letters =
      before ++ separator :: (middle ++ separator :: after) ∧
      before.Nodup ∧ middle.Nodup ∧ after.Nodup ∧
      separator ∉ before ∧ separator ∉ middle ∧ separator ∉ after

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
      have leftAbsence : separator ≠ leftHead ∧ separator ∉ left := by
        simpa only [List.mem_cons, not_or] using separatorNotLeft
      have rightAbsence : separator ≠ rightHead ∧ separator ∉ right := by
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

private theorem nodup_of_flatMap_nodup
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

/-- If an exactly twice-occurring source variable owns an anchor separator,
its two occurrences divide the source into three duplicate-free blocks. -/
theorem preimage_two_occurrence_separator_owner_factorization
    {bound : Nat} {word : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    {owner : Nat}
    (ownerCount : word.toList.count owner = 2)
    (separatorMember :
      3 * bound + 2 ∈ (substitution owner).toList) :
    TwoSeparatorNodupFactorization owner word.toList := by
  obtain
    ⟨before, middle, after, ownerNotBefore, ownerNotMiddle,
      ownerNotAfter, sourceSplit⟩ :=
    exists_two_occurrence_split_of_count_eq_two ownerCount
  let images :=
    fun letter : Nat => (substitution letter).toList
  have ownerImage :=
    preimage_two_occurrence_separator_image_singleton
      mapped ownerCount separatorMember
  have ownerImageList :
      images owner = [3 * bound + 2] := by
    simp only [images]
    rw [ownerImage]
    rfl
  have mappedList :
      word.toList.flatMap images =
        (anchor (3 * bound)).toList := by
    have listed := congrArg Word.toList mapped
    rw [Word.toList_bind] at listed
    simpa only [images] using listed
  have separatorCountSum :
      (before.flatMap images).count (3 * bound + 2) +
          (middle.flatMap images).count (3 * bound + 2) +
          (after.flatMap images).count (3 * bound + 2) =
        0 := by
    have countEquality :=
      congrArg (List.count (3 * bound + 2)) mappedList
    rw [sourceSplit] at countEquality
    simp only [List.flatMap_append, List.flatMap_cons, ownerImageList,
      List.count_append, List.count_cons_self, List.count_nil] at countEquality
    rw [anchor_separator_count_eq_two] at countEquality
    omega
  have separatorNotBeforeImage :
      3 * bound + 2 ∉ before.flatMap images := by
    apply List.count_eq_zero.mp
    omega
  have separatorNotMiddleImage :
      3 * bound + 2 ∉ middle.flatMap images := by
    apply List.count_eq_zero.mp
    omega
  have separatorNotAfterImage :
      3 * bound + 2 ∉ after.flatMap images := by
    apply List.count_eq_zero.mp
    omega
  have expandedMapping :
      before.flatMap images ++
          (3 * bound + 2) ::
            (middle.flatMap images ++
              (3 * bound + 2) :: after.flatMap images) =
        List.range (3 * bound + 2) ++
          (3 * bound + 2) ::
            ((List.range (3 * bound + 2)).reverse ++
              (3 * bound + 2) :: List.range (3 * bound + 2)) := by
    calc
      _ = word.toList.flatMap images := by
        rw [sourceSplit]
        simp [List.flatMap_append, List.flatMap_cons, ownerImageList]
      _ = (anchor (3 * bound)).toList := mappedList
      _ = _ := by
        rw [anchor_toList]
        simp [List.append_assoc]
  have separatorNotForward :
      3 * bound + 2 ∉ List.range (3 * bound + 2) := by
    simp
  have separatorNotReverse :
      3 * bound + 2 ∉
        (List.range (3 * bound + 2)).reverse := by
    simp
  have firstSplit :=
    append_cons_eq_append_cons_of_not_mem
      separatorNotBeforeImage separatorNotForward expandedMapping
  have secondSplit :=
    append_cons_eq_append_cons_of_not_mem
      separatorNotMiddleImage separatorNotReverse firstSplit.2
  have imageNonempty :
      ∀ letter, images letter ≠ [] := by
    intro letter
    cases substitution letter
    simp [images, Word.toList]
  have beforeImageNodup :
      (before.flatMap images).Nodup := by
    rw [firstSplit.1]
    exact List.nodup_range
  have middleImageNodup :
      (middle.flatMap images).Nodup := by
    rw [secondSplit.1]
    exact
      (List.reverse_perm
        (List.range (3 * bound + 2))).nodup_iff.mpr
          List.nodup_range
  have afterImageNodup :
      (after.flatMap images).Nodup := by
    rw [secondSplit.2]
    exact List.nodup_range
  exact
    ⟨before, middle, after, sourceSplit,
      nodup_of_flatMap_nodup before images imageNonempty beforeImageNodup,
      nodup_of_flatMap_nodup middle images imageNonempty middleImageNodup,
      nodup_of_flatMap_nodup after images imageNonempty afterImageNodup,
      ownerNotBefore, ownerNotMiddle, ownerNotAfter⟩

/-- The two occurrences of a source variable owning the distinguished
separator cut the mapped word into the two forward anchor blocks and the
intervening reverse block.  This is the quantitative form of
`preimage_two_occurrence_separator_owner_factorization`; later multiplicity
arguments use the exact reverse-block image rather than only its nodup
consequence. -/
theorem preimage_two_occurrence_separator_owner_mapped_blocks
    {bound : Nat} {word : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    {owner : Nat}
    (ownerCount : word.toList.count owner = 2)
    (separatorMember :
      3 * bound + 2 ∈ (substitution owner).toList) :
    ∃ before middle after,
      word.toList =
          before ++ owner :: (middle ++ owner :: after) ∧
        owner ∉ before ∧ owner ∉ middle ∧ owner ∉ after ∧
        before.flatMap
            (fun letter => (substitution letter).toList) =
          List.range (3 * bound + 2) ∧
        middle.flatMap
            (fun letter => (substitution letter).toList) =
          (List.range (3 * bound + 2)).reverse ∧
        after.flatMap
            (fun letter => (substitution letter).toList) =
          List.range (3 * bound + 2) := by
  obtain
    ⟨before, middle, after, ownerNotBefore, ownerNotMiddle,
      ownerNotAfter, sourceSplit⟩ :=
    exists_two_occurrence_split_of_count_eq_two ownerCount
  let images :=
    fun letter : Nat => (substitution letter).toList
  have ownerImage :=
    preimage_two_occurrence_separator_image_singleton
      mapped ownerCount separatorMember
  have ownerImageList :
      images owner = [3 * bound + 2] := by
    simp only [images]
    rw [ownerImage]
    rfl
  have mappedList :
      word.toList.flatMap images =
        (anchor (3 * bound)).toList := by
    have listed := congrArg Word.toList mapped
    rw [Word.toList_bind] at listed
    simpa only [images] using listed
  have separatorCountSum :
      (before.flatMap images).count (3 * bound + 2) +
          (middle.flatMap images).count (3 * bound + 2) +
          (after.flatMap images).count (3 * bound + 2) =
        0 := by
    have countEquality :=
      congrArg (List.count (3 * bound + 2)) mappedList
    rw [sourceSplit] at countEquality
    simp only [List.flatMap_append, List.flatMap_cons, ownerImageList,
      List.count_append, List.count_cons_self, List.count_nil] at countEquality
    rw [anchor_separator_count_eq_two] at countEquality
    omega
  have separatorNotBeforeImage :
      3 * bound + 2 ∉ before.flatMap images := by
    apply List.count_eq_zero.mp
    omega
  have separatorNotMiddleImage :
      3 * bound + 2 ∉ middle.flatMap images := by
    apply List.count_eq_zero.mp
    omega
  have separatorNotAfterImage :
      3 * bound + 2 ∉ after.flatMap images := by
    apply List.count_eq_zero.mp
    omega
  have expandedMapping :
      before.flatMap images ++
          (3 * bound + 2) ::
            (middle.flatMap images ++
              (3 * bound + 2) :: after.flatMap images) =
        List.range (3 * bound + 2) ++
          (3 * bound + 2) ::
            ((List.range (3 * bound + 2)).reverse ++
              (3 * bound + 2) :: List.range (3 * bound + 2)) := by
    calc
      _ = word.toList.flatMap images := by
        rw [sourceSplit]
        simp [List.flatMap_append, List.flatMap_cons, ownerImageList]
      _ = (anchor (3 * bound)).toList := mappedList
      _ = _ := by
        rw [anchor_toList]
        simp [List.append_assoc]
  have separatorNotForward :
      3 * bound + 2 ∉ List.range (3 * bound + 2) := by
    simp
  have separatorNotReverse :
      3 * bound + 2 ∉
        (List.range (3 * bound + 2)).reverse := by
    simp
  have firstSplit :=
    append_cons_eq_append_cons_of_not_mem
      separatorNotBeforeImage separatorNotForward expandedMapping
  have secondSplit :=
    append_cons_eq_append_cons_of_not_mem
      separatorNotMiddleImage separatorNotReverse firstSplit.2
  exact
    ⟨before, middle, after, sourceSplit,
      ownerNotBefore, ownerNotMiddle, ownerNotAfter,
      firstSplit.1, secondSplit.1, secondSplit.2⟩

/-- A two-separator duplicate-free factorization has exactly the two
displayed separator occurrences. -/
theorem twoSeparatorNodupFactorization_separator_count_eq_two
    {separator : Nat} {letters : List Nat}
    (shape : TwoSeparatorNodupFactorization separator letters) :
    letters.count separator = 2 := by
  rcases shape with
    ⟨before, middle, after, split, _beforeNodup, _middleNodup,
      _afterNodup, separatorNotBefore, separatorNotMiddle,
      separatorNotAfter⟩
  rw [split]
  simp [List.count_eq_zero.mpr separatorNotBefore,
    List.count_eq_zero.mpr separatorNotMiddle,
    List.count_eq_zero.mpr separatorNotAfter]

private theorem filter_eq_singleton_of_nodup
    {letters : List Nat} {letter : Nat}
    (nodup : letters.Nodup)
    (member : letter ∈ letters) :
    letters.filter (fun value => value == letter) = [letter] := by
  induction letters with
  | nil => simp at member
  | cons first rest ih =>
      simp only [List.nodup_cons] at nodup
      simp only [List.mem_cons] at member
      by_cases equality : first = letter
      · subst first
        have restFilter :
            rest.filter (fun value => value == letter) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro value valueMember
          simp only [beq_iff_eq]
          intro valueEq
          subst value
          exact nodup.1 valueMember
        simp [restFilter]
      · have tailMember : letter ∈ rest := by
          rcases member with equality' | tailMember
          · exact False.elim (equality equality'.symm)
          · exact tailMember
        simp [equality, ih nodup.2 tailMember]

private theorem filter_eq_nil_of_not_mem
    {letters : List Nat} {letter : Nat}
    (absent : letter ∉ letters) :
    letters.filter (fun value => value == letter) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro value valueMember
  simp only [beq_iff_eq]
  intro equality
  subst value
  exact absent valueMember

private theorem twoSeparator_blockProjection
    {separator target : Nat} {block : List Nat}
    (blockNodup : block.Nodup)
    (separatorNotBlock : separator ∉ block) :
    block.filter
        (fun value => value == target || value == separator) =
      if target ∈ block then [target] else [] := by
  rw [show
    block.filter
        (fun value => value == target || value == separator) =
      block.filter (fun value => value == target) by
        apply List.filter_congr
        intro value valueMember
        have valueNotSeparator : value ≠ separator := by
          intro equality
          subst value
          exact separatorNotBlock valueMember
        simp [valueNotSeparator]]
  by_cases member : target ∈ block
  · rw [if_pos member]
    exact filter_eq_singleton_of_nodup blockNodup member
  · rw [if_neg member]
    exact filter_eq_nil_of_not_mem member

/-- For a target distinct from the separator, the two-letter projection of a
two-separator duplicate-free factorization has no target self-edge. -/
theorem twoSeparatorNodupFactorization_pairProjection_no_selfEdge
    {separator target : Nat} {letters : List Nat}
    (shape : TwoSeparatorNodupFactorization separator letters)
    (different : target ≠ separator) :
    (target, target) ∉
      adjacentPairsList
        (letters.filter
          (fun value => value == target || value == separator)) := by
  rcases shape with
    ⟨before, middle, after, split, beforeNodup, middleNodup,
      afterNodup, separatorNotBefore, separatorNotMiddle,
      separatorNotAfter⟩
  have beforeFilter :=
    twoSeparator_blockProjection
      (target := target) beforeNodup separatorNotBefore
  have middleFilter :=
    twoSeparator_blockProjection
      (target := target) middleNodup separatorNotMiddle
  have afterFilter :=
    twoSeparator_blockProjection
      (target := target) afterNodup separatorNotAfter
  rw [split, List.filter_append, List.filter_cons,
    List.filter_append, List.filter_cons]
  simp only [beq_self_eq_true, Bool.or_true, if_true]
  rw [beforeFilter, middleFilter, afterFilter]
  by_cases beforeMember : target ∈ before <;>
    by_cases middleMember : target ∈ middle <;>
      by_cases afterMember : target ∈ after <;>
        simp [beforeMember, middleMember, afterMember, different,
          adjacentPairsList, Word.adjacentPairsFrom]

/-- A singleton-pivot factorization gives the exact projection onto the pivot
and one other variable.  The four possible results record whether the other
variable occurs on the left, on the right, or on both sides. -/
theorem singletonPivot_pairProjection
    {pivot letter : Nat} {letters left right : List Nat}
    (split : letters = left ++ pivot :: right)
    (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (pivotNotLeft : pivot ∉ left)
    (pivotNotRight : pivot ∉ right) :
    letters.filter (fun value => value == letter || value == pivot) =
      (if letter ∈ left then [letter] else []) ++ [pivot] ++
        (if letter ∈ right then [letter] else []) := by
  rw [split, List.filter_append, List.filter_cons]
  have pivotBool : (pivot == letter || pivot == pivot) = true := by
    simp
  rw [if_pos pivotBool]
  have leftFilter :
      left.filter (fun value => value == letter || value == pivot) =
        if letter ∈ left then [letter] else [] := by
    rw [show
      left.filter (fun value => value == letter || value == pivot) =
        left.filter (fun value => value == letter) by
          apply List.filter_congr
          intro value valueMember
          have valueNotPivot : value ≠ pivot := by
            intro equality
            subst value
            exact pivotNotLeft valueMember
          simp [valueNotPivot]]
    by_cases member : letter ∈ left
    · rw [if_pos member]
      exact filter_eq_singleton_of_nodup leftNodup member
    · rw [if_neg member]
      exact filter_eq_nil_of_not_mem member
  have rightFilter :
      right.filter (fun value => value == letter || value == pivot) =
        if letter ∈ right then [letter] else [] := by
    rw [show
      right.filter (fun value => value == letter || value == pivot) =
        right.filter (fun value => value == letter) by
          apply List.filter_congr
          intro value valueMember
          have valueNotPivot : value ≠ pivot := by
            intro equality
            subst value
            exact pivotNotRight valueMember
          simp [valueNotPivot]]
    by_cases member : letter ∈ right
    · rw [if_pos member]
      exact filter_eq_singleton_of_nodup rightNodup member
    · rw [if_neg member]
      exact filter_eq_nil_of_not_mem member
  rw [leftFilter, rightFilter]
  simp

private theorem nodup_eq_of_pairProjection_head :
    ∀ {left right : List Nat},
      left.Nodup →
      right.Nodup →
      (∀ letter, letter ∈ left ↔ letter ∈ right) →
      (∀ first second,
        first ≠ second →
        first ∈ left →
        second ∈ left →
        (left.filter
            (fun value => value == first || value == second)).head? =
          (right.filter
            (fun value => value == first || value == second)).head?) →
      left = right
  | [], [], _, _, _, _ => rfl
  | [], first :: rest, _, _, sameMembers, _ => by
      have : first ∈ ([] : List Nat) :=
        (sameMembers first).mpr (by simp)
      simp at this
  | first :: rest, [], _, _, sameMembers, _ => by
      have : first ∈ ([] : List Nat) :=
        (sameMembers first).mp (by simp)
      simp at this
  | first :: leftRest, second :: rightRest,
      leftNodup, rightNodup, sameMembers, sameHeads => by
      simp only [List.nodup_cons] at leftNodup rightNodup
      have headsEqual : first = second := by
        apply Decidable.byContradiction
        intro different
        have firstMember : first ∈ first :: leftRest := by simp
        have secondMember : second ∈ first :: leftRest :=
          (sameMembers second).mpr (by simp)
        have pairHeads :=
          sameHeads first second different firstMember secondMember
        simp [different] at pairHeads
      subst second
      have tailMembers :
          ∀ letter, letter ∈ leftRest ↔ letter ∈ rightRest := by
        intro letter
        have notFirstLeft : first ∉ leftRest := by
          exact leftNodup.1
        have notFirstRight : first ∉ rightRest := by
          exact rightNodup.1
        constructor
        · intro member
          have inRight :
              letter ∈ first :: rightRest :=
            (sameMembers letter).mp (by simp [member])
          simp only [List.mem_cons] at inRight
          rcases inRight with equality | tailMember
          · subst first
            exact False.elim (notFirstLeft member)
          · exact tailMember
        · intro member
          have inLeft :
              letter ∈ first :: leftRest :=
            (sameMembers letter).mpr (by simp [member])
          simp only [List.mem_cons] at inLeft
          rcases inLeft with equality | tailMember
          · subst first
            exact False.elim (notFirstRight member)
          · exact tailMember
      have tailHeads :
          ∀ firstLetter secondLetter,
            firstLetter ≠ secondLetter →
            firstLetter ∈ leftRest →
            secondLetter ∈ leftRest →
            (leftRest.filter
                (fun value =>
                  value == firstLetter || value == secondLetter)).head? =
              (rightRest.filter
                (fun value =>
                  value == firstLetter || value == secondLetter)).head? := by
        intro firstLetter secondLetter different
          firstMember secondMember
        have firstNotHead : firstLetter ≠ first := by
          intro equality
          subst firstLetter
          have absent : first ∉ leftRest := by
            exact leftNodup.1
          exact absent firstMember
        have secondNotHead : secondLetter ≠ first := by
          intro equality
          subst secondLetter
          have absent : first ∉ leftRest := by
            exact leftNodup.1
          exact absent secondMember
        have inherited :=
          sameHeads firstLetter secondLetter different
            (by simp [firstMember]) (by simp [secondMember])
        simpa [Ne.symm firstNotHead, Ne.symm secondNotHead] using inherited
      have tailEq :=
        nodup_eq_of_pairProjection_head
          leftNodup.2 rightNodup.2 tailMembers tailHeads
      rw [tailEq]

private theorem nodup_eq_of_pairProjection_last
    {left right : List Nat}
    (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (sameMembers : ∀ letter, letter ∈ left ↔ letter ∈ right)
    (sameLasts :
      ∀ first second,
        first ≠ second →
        first ∈ left →
        second ∈ left →
        (left.filter
            (fun value => value == first || value == second)).getLast? =
          (right.filter
            (fun value => value == first || value == second)).getLast?) :
    left = right := by
  apply List.reverse_inj.mp
  apply nodup_eq_of_pairProjection_head
  · exact (List.reverse_perm left).nodup_iff.mpr leftNodup
  · exact (List.reverse_perm right).nodup_iff.mpr rightNodup
  · intro letter
    simp [sameMembers letter]
  · intro first second different firstMember secondMember
    have original :=
      sameLasts first second different
        (by simpa using firstMember) (by simpa using secondMember)
    simpa [List.filter_reverse, List.head?_reverse] using original

/-- The head of a pivot-pair projection records membership on the left side
of a singleton-pivot factorization. -/
theorem singletonPivot_left_mem_iff
    {pivot letter : Nat} {letters left right : List Nat}
    (split : letters = left ++ pivot :: right)
    (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (pivotNotLeft : pivot ∉ left)
    (pivotNotRight : pivot ∉ right)
    (different : letter ≠ pivot) :
    letter ∈ left ↔
      (letters.filter
        (fun value => value == letter || value == pivot)).head? =
          some letter := by
  rw [singletonPivot_pairProjection split leftNodup rightNodup
    pivotNotLeft pivotNotRight]
  by_cases member : letter ∈ left
  · simp [member]
  · simp [member, Ne.symm different]

/-- The last letter of a pivot-pair projection records membership on the
right side of a singleton-pivot factorization. -/
theorem singletonPivot_right_mem_iff
    {pivot letter : Nat} {letters left right : List Nat}
    (split : letters = left ++ pivot :: right)
    (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (pivotNotLeft : pivot ∉ left)
    (pivotNotRight : pivot ∉ right)
    (different : letter ≠ pivot) :
    letter ∈ right ↔
      (letters.filter
        (fun value => value == letter || value == pivot)).getLast? =
          some letter := by
  rw [singletonPivot_pairProjection split leftNodup rightNodup
    pivotNotLeft pivotNotRight]
  by_cases member : letter ∈ right
  · simp [member]
  · simp [member, Ne.symm different]

private theorem pairProjection_head_of_left
    {pivot first second : Nat} {letters left right : List Nat}
    (split : letters = left ++ pivot :: right)
    (pivotNeFirst : pivot ≠ first)
    (pivotNeSecond : pivot ≠ second)
    (firstMember : first ∈ left) :
    (letters.filter
        (fun value => value == first || value == second)).head? =
      (left.filter
        (fun value => value == first || value == second)).head? := by
  rw [split, List.filter_append, List.filter_cons]
  simp only [beq_eq_false_iff_ne.mpr pivotNeFirst,
    beq_eq_false_iff_ne.mpr pivotNeSecond, Bool.false_or]
  rw [if_neg (by decide)]
  rw [List.head?_append]
  have firstProjected :
      first ∈
        left.filter
          (fun value => value == first || value == second) := by
    exact List.mem_filter.mpr ⟨firstMember, by simp⟩
  cases equation :
      left.filter
        (fun value => value == first || value == second) with
  | nil =>
      rw [equation] at firstProjected
      simp at firstProjected
  | cons head tail =>
      simp

private theorem getLast?_eq_some_of_cons
    (head : Nat) :
    ∀ tail : List Nat,
      ∃ last, (head :: tail).getLast? = some last
  | [] => ⟨head, rfl⟩
  | next :: rest => by
      simpa using getLast?_eq_some_of_cons next rest

private theorem pairProjection_last_of_right
    {pivot first second : Nat} {letters left right : List Nat}
    (split : letters = left ++ pivot :: right)
    (pivotNeFirst : pivot ≠ first)
    (pivotNeSecond : pivot ≠ second)
    (firstMember : first ∈ right) :
    (letters.filter
        (fun value => value == first || value == second)).getLast? =
      (right.filter
        (fun value => value == first || value == second)).getLast? := by
  rw [split, List.filter_append, List.filter_cons]
  simp only [beq_eq_false_iff_ne.mpr pivotNeFirst,
    beq_eq_false_iff_ne.mpr pivotNeSecond, Bool.false_or]
  rw [if_neg (by decide)]
  rw [List.getLast?_append]
  have firstProjected :
      first ∈
        right.filter
          (fun value => value == first || value == second) := by
    exact List.mem_filter.mpr ⟨firstMember, by simp⟩
  cases equation :
      right.filter
        (fun value => value == first || value == second) with
  | nil =>
      rw [equation] at firstProjected
      simp at firstProjected
  | cons head tail =>
      obtain ⟨last, lastEq⟩ :=
        getLast?_eq_some_of_cons head tail
      rw [lastEq]
      simp

/-- Deletion marked-digraph equality is injective on the complete
singleton-pivot double-occurrence class. -/
theorem singletonPivotFactorization_eq
    {pivot : Nat} {leftWord rightWord : Word Nat}
    (leftShape :
      SingletonPivotFactorization pivot leftWord.toList)
    (rightShape :
      SingletonPivotFactorization pivot rightWord.toList)
    (same : SameDeletionMarkedDigraph leftWord rightWord) :
    rightWord = leftWord := by
  rcases leftShape with
    ⟨leftBefore, leftAfter, leftSplit, leftBeforeNodup,
      leftAfterNodup, pivotNotLeftBefore, pivotNotLeftAfter⟩
  rcases rightShape with
    ⟨rightBefore, rightAfter, rightSplit, rightBeforeNodup,
      rightAfterNodup, pivotNotRightBefore, pivotNotRightAfter⟩
  have beforeMembers :
      ∀ letter, letter ∈ leftBefore ↔ letter ∈ rightBefore := by
    intro letter
    by_cases equality : letter = pivot
    · subst letter
      simp [pivotNotLeftBefore, pivotNotRightBefore]
    · have marked :=
        same (fun value => value == letter || value == pivot)
      rw [singletonPivot_left_mem_iff leftSplit leftBeforeNodup
          leftAfterNodup pivotNotLeftBefore pivotNotLeftAfter equality,
        singletonPivot_left_mem_iff rightSplit rightBeforeNodup
          rightAfterNodup pivotNotRightBefore pivotNotRightAfter equality]
      rw [marked.1]
  have afterMembers :
      ∀ letter, letter ∈ leftAfter ↔ letter ∈ rightAfter := by
    intro letter
    by_cases equality : letter = pivot
    · subst letter
      simp [pivotNotLeftAfter, pivotNotRightAfter]
    · have marked :=
        same (fun value => value == letter || value == pivot)
      rw [singletonPivot_right_mem_iff leftSplit leftBeforeNodup
          leftAfterNodup pivotNotLeftBefore pivotNotLeftAfter equality,
        singletonPivot_right_mem_iff rightSplit rightBeforeNodup
          rightAfterNodup pivotNotRightBefore pivotNotRightAfter equality]
      rw [marked.2.1]
  have beforePairHeads :
      ∀ first second,
        first ≠ second →
        first ∈ leftBefore →
        second ∈ leftBefore →
        (leftBefore.filter
            (fun value => value == first || value == second)).head? =
          (rightBefore.filter
            (fun value => value == first || value == second)).head? := by
    intro first second different firstMember secondMember
    have firstNotPivot : pivot ≠ first := by
      intro equality
      subst first
      exact pivotNotLeftBefore firstMember
    have secondNotPivot : pivot ≠ second := by
      intro equality
      subst second
      exact pivotNotLeftBefore secondMember
    have rightFirstMember : first ∈ rightBefore :=
      (beforeMembers first).mp firstMember
    have marked :=
      same (fun value => value == first || value == second)
    have markedHead := marked.1
    rw [pairProjection_head_of_left leftSplit firstNotPivot
          secondNotPivot firstMember,
        pairProjection_head_of_left rightSplit firstNotPivot
          secondNotPivot rightFirstMember] at markedHead
    exact markedHead
  have afterPairLasts :
      ∀ first second,
        first ≠ second →
        first ∈ leftAfter →
        second ∈ leftAfter →
        (leftAfter.filter
            (fun value => value == first || value == second)).getLast? =
          (rightAfter.filter
            (fun value => value == first || value == second)).getLast? := by
    intro first second different firstMember secondMember
    have firstNotPivot : pivot ≠ first := by
      intro equality
      subst first
      exact pivotNotLeftAfter firstMember
    have secondNotPivot : pivot ≠ second := by
      intro equality
      subst second
      exact pivotNotLeftAfter secondMember
    have rightFirstMember : first ∈ rightAfter :=
      (afterMembers first).mp firstMember
    have marked :=
      same (fun value => value == first || value == second)
    have markedLast := marked.2.1
    rw [pairProjection_last_of_right leftSplit firstNotPivot
          secondNotPivot firstMember,
        pairProjection_last_of_right rightSplit firstNotPivot
          secondNotPivot rightFirstMember] at markedLast
    exact markedLast
  have beforeEq :=
    nodup_eq_of_pairProjection_head leftBeforeNodup rightBeforeNodup
      beforeMembers beforePairHeads
  have afterEq :=
    nodup_eq_of_pairProjection_last leftAfterNodup rightAfterNodup
      afterMembers afterPairLasts
  apply Word.toList_injective
  rw [leftSplit, rightSplit, beforeEq, afterEq]

/-- A singleton projection determines a unique occurrence split. -/
private theorem split_of_singletonProjection :
    ∀ {pivot : Nat} {letters : List Nat},
      letters.filter (fun value => value == pivot) = [pivot] →
      ∃ before after,
        letters = before ++ pivot :: after ∧
          pivot ∉ before ∧ pivot ∉ after
  | pivot, [], projection => by simp at projection
  | pivot, first :: rest, projection => by
      by_cases equality : first = pivot
      · subst first
        have restProjection :
            rest.filter (fun value => value == pivot) = [] := by
          simpa using projection
        have absent : pivot ∉ rest := by
          intro member
          have filteredMember :
              pivot ∈ rest.filter (fun value => value == pivot) :=
            List.mem_filter.mpr ⟨member, by simp⟩
          rw [restProjection] at filteredMember
          simp at filteredMember
        exact ⟨[], rest, rfl, by simp, absent⟩
      · have restProjection :
            rest.filter (fun value => value == pivot) = [pivot] := by
          simpa [equality] using projection
        obtain ⟨before, after, split, pivotNotBefore, pivotNotAfter⟩ :=
          split_of_singletonProjection restProjection
        refine ⟨first :: before, after, ?_, ?_, pivotNotAfter⟩
        · simp [split]
        · simp [Ne.symm equality, pivotNotBefore]

private theorem split_pairProjection
    {pivot letter : Nat} {letters before after : List Nat}
    (split : letters = before ++ pivot :: after)
    (pivotNotBefore : pivot ∉ before)
    (pivotNotAfter : pivot ∉ after) :
    letters.filter (fun value => value == letter || value == pivot) =
      before.filter (fun value => value == letter) ++ [pivot] ++
        after.filter (fun value => value == letter) := by
  rw [split, List.filter_append, List.filter_cons]
  have beforeFilter :
      before.filter (fun value => value == letter || value == pivot) =
        before.filter (fun value => value == letter) := by
    apply List.filter_congr
    intro value valueMember
    have valueNotPivot : value ≠ pivot := by
      intro equality
      subst value
      exact pivotNotBefore valueMember
    simp [valueNotPivot]
  have afterFilter :
      after.filter (fun value => value == letter || value == pivot) =
        after.filter (fun value => value == letter) := by
    apply List.filter_congr
    intro value valueMember
    have valueNotPivot : value ≠ pivot := by
      intro equality
      subst value
      exact pivotNotAfter valueMember
    simp [valueNotPivot]
  rw [beforeFilter, afterFilter]
  simp

private theorem adjacentPairsList_append_left
    {firstList suffix : List Nat} {edge : Nat × Nat}
    (member : edge ∈ adjacentPairsList firstList) :
    edge ∈ adjacentPairsList (firstList ++ suffix) := by
  cases firstList with
  | nil => simp [adjacentPairsList] at member
  | cons head tail =>
      cases suffix with
      | nil => simpa using member
      | cons next rest =>
          change edge ∈
            Word.adjacentPairsFrom head (tail ++ next :: rest)
          change edge ∈ Word.adjacentPairsFrom head tail at member
          rw [Word.adjacentPairsFrom_append]
          exact List.mem_append_left _ member

private theorem adjacentPairsList_append_right
    {firstList suffix : List Nat} {edge : Nat × Nat}
    (member : edge ∈ adjacentPairsList suffix) :
    edge ∈ adjacentPairsList (firstList ++ suffix) := by
  cases firstList with
  | nil => simpa using member
  | cons head tail =>
      cases suffix with
      | nil => simp [adjacentPairsList] at member
      | cons next rest =>
          change edge ∈
            Word.adjacentPairsFrom head (tail ++ next :: rest)
          change edge ∈ Word.adjacentPairsFrom next rest at member
          rw [Word.adjacentPairsFrom_append]
          exact List.mem_append_right _
            (List.mem_cons_of_mem _ member)

private theorem selfEdge_of_count_ge_two :
    ∀ {letters : List Nat} {letter : Nat},
      2 ≤ letters.count letter →
      (letter, letter) ∈
        adjacentPairsList
          (letters.filter (fun value => value == letter))
  | [], _, countBound => by simp at countBound
  | first :: rest, letter, countBound => by
      by_cases equality : first = letter
      · subst first
        have tailPositive : 1 ≤ rest.count letter := by
          simp only [List.count_cons_self] at countBound
          omega
        have tailMember : letter ∈ rest :=
          List.count_pos_iff.mp (by omega)
        have filteredMember :
            letter ∈ rest.filter (fun value => value == letter) :=
          List.mem_filter.mpr ⟨tailMember, by simp⟩
        cases equation :
            rest.filter (fun value => value == letter) with
        | nil =>
            rw [equation] at filteredMember
            simp at filteredMember
        | cons next remaining =>
            have nextEq : next = letter := by
              have nextFiltered :
                  next ∈ rest.filter (fun value => value == letter) := by
                rw [equation]
                simp
              exact beq_iff_eq.mp (List.mem_filter.mp nextFiltered).2
            subst next
            simp [adjacentPairsList, Word.adjacentPairsFrom, equation]
      · have tailBound : 2 ≤ rest.count letter := by
          simpa [equality] using countBound
        simpa [equality] using
          selfEdge_of_count_ge_two tailBound

private theorem singletonPivot_pairProjection_no_selfEdge
    {pivot letter : Nat} {letters left right : List Nat}
    (split : letters = left ++ pivot :: right)
    (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (pivotNotLeft : pivot ∉ left)
    (pivotNotRight : pivot ∉ right) :
    (letter, letter) ∉
      adjacentPairsList
        (letters.filter
          (fun value => value == letter || value == pivot)) := by
  rw [singletonPivot_pairProjection split leftNodup rightNodup
    pivotNotLeft pivotNotRight]
  by_cases equality : letter = pivot
  · subst letter
    simp [pivotNotLeft, pivotNotRight, adjacentPairsList,
      Word.adjacentPairsFrom]
  · by_cases leftMember : letter ∈ left <;>
      by_cases rightMember : letter ∈ right <;>
        simp [leftMember, rightMember, equality, adjacentPairsList,
          Word.adjacentPairsFrom]

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
        have := bounded first
        simp only [List.count_cons_self] at this
        omega
      · apply ih
        intro letter
        have fullBound := bounded letter
        by_cases equality : first = letter
        · subst first
          simp only [List.count_cons_self] at fullBound
          omega
        · simpa [equality] using fullBound

/-- The singleton-pivot structural class is inherited by every word with the
same complete deletion marked-digraph family. -/
theorem singletonPivotFactorization_of_same
    {pivot : Nat} {leftWord rightWord : Word Nat}
    (leftShape :
      SingletonPivotFactorization pivot leftWord.toList)
    (same : SameDeletionMarkedDigraph leftWord rightWord) :
    SingletonPivotFactorization pivot rightWord.toList := by
  rcases leftShape with
    ⟨leftBefore, leftAfter, leftSplit, leftBeforeNodup,
      leftAfterNodup, pivotNotLeftBefore, pivotNotLeftAfter⟩
  have leftPivotProjection :
      leftWord.toList.filter (fun value => value == pivot) = [pivot] := by
    rw [leftSplit, List.filter_append, List.filter_cons]
    have beforeEmpty :=
      filter_eq_nil_of_not_mem pivotNotLeftBefore
    have afterEmpty :=
      filter_eq_nil_of_not_mem pivotNotLeftAfter
    rw [beforeEmpty, afterEmpty]
    simp
  have rightPivotProjection :
      rightWord.toList.filter (fun value => value == pivot) = [pivot] :=
    sameDeletionMarkedDigraph_preserves_singletonProjection
      same pivot leftPivotProjection
  obtain ⟨rightBefore, rightAfter, rightSplit,
      pivotNotRightBefore, pivotNotRightAfter⟩ :=
    split_of_singletonProjection rightPivotProjection
  have rightBeforeBound :
      ∀ letter, rightBefore.count letter ≤ 1 := by
    intro letter
    by_cases equality : letter = pivot
    · subst letter
      simp [List.count_eq_zero.mpr pivotNotRightBefore]
    · apply Nat.lt_succ_iff.mp
      apply Decidable.byContradiction
      intro notLess
      have countBound : 2 ≤ rightBefore.count letter := by omega
      have localEdge :=
        selfEdge_of_count_ge_two countBound
      have rightProjection :=
        split_pairProjection rightSplit pivotNotRightBefore
          pivotNotRightAfter (letter := letter)
      have fullEdge :
          (letter, letter) ∈
            adjacentPairsList
              (rightWord.toList.filter
                (fun value => value == letter || value == pivot)) := by
        rw [rightProjection]
        exact adjacentPairsList_append_left
          (adjacentPairsList_append_left localEdge)
      have marked :=
        same (fun value => value == letter || value == pivot)
      have leftEdge := (marked.2.2.2 letter letter).mpr fullEdge
      exact
        (singletonPivot_pairProjection_no_selfEdge leftSplit
          leftBeforeNodup leftAfterNodup pivotNotLeftBefore
          pivotNotLeftAfter) leftEdge
  have rightAfterBound :
      ∀ letter, rightAfter.count letter ≤ 1 := by
    intro letter
    by_cases equality : letter = pivot
    · subst letter
      simp [List.count_eq_zero.mpr pivotNotRightAfter]
    · apply Nat.lt_succ_iff.mp
      apply Decidable.byContradiction
      intro notLess
      have countBound : 2 ≤ rightAfter.count letter := by omega
      have localEdge :=
        selfEdge_of_count_ge_two countBound
      have rightProjection :=
        split_pairProjection rightSplit pivotNotRightBefore
          pivotNotRightAfter (letter := letter)
      have fullEdge :
          (letter, letter) ∈
            adjacentPairsList
              (rightWord.toList.filter
                (fun value => value == letter || value == pivot)) := by
        rw [rightProjection]
        exact adjacentPairsList_append_right
          (firstList :=
            rightBefore.filter (fun value => value == letter) ++ [pivot])
          localEdge
      have marked :=
        same (fun value => value == letter || value == pivot)
      have leftEdge := (marked.2.2.2 letter letter).mpr fullEdge
      exact
        (singletonPivot_pairProjection_no_selfEdge leftSplit
          leftBeforeNodup leftAfterNodup pivotNotLeftBefore
          pivotNotLeftAfter) leftEdge
  exact ⟨rightBefore, rightAfter, rightSplit,
    nodup_of_count_le_one rightBeforeBound,
    nodup_of_count_le_one rightAfterBound,
    pivotNotRightBefore, pivotNotRightAfter⟩

/-- A source singleton-pivot factorization alone suffices for exact
deletion-signature rigidity. -/
theorem singletonPivotFactorization_rigid
    {pivot : Nat} {leftWord rightWord : Word Nat}
    (leftShape :
      SingletonPivotFactorization pivot leftWord.toList)
    (same : SameDeletionMarkedDigraph leftWord rightWord) :
    rightWord = leftWord :=
  singletonPivotFactorization_eq leftShape
    (singletonPivotFactorization_of_same leftShape same) same

private theorem twoSeparator_split_pairProjection
    {separator letter : Nat}
    {letters before middle after : List Nat}
    (split :
      letters =
        before ++ separator :: (middle ++ separator :: after))
    (separatorNotBefore : separator ∉ before)
    (separatorNotMiddle : separator ∉ middle)
    (separatorNotAfter : separator ∉ after) :
    letters.filter
        (fun value => value == letter || value == separator) =
      before.filter (fun value => value == letter) ++
        separator ::
          (middle.filter (fun value => value == letter) ++
            separator :: after.filter (fun value => value == letter)) := by
  rw [split, List.filter_append, List.filter_cons,
    List.filter_append, List.filter_cons]
  have beforeFilter :=
    filter_or_eq_eq_filter_eq_of_not_mem
      before letter separator separatorNotBefore
  have middleFilter :=
    filter_or_eq_eq_filter_eq_of_not_mem
      middle letter separator separatorNotMiddle
  have afterFilter :=
    filter_or_eq_eq_filter_eq_of_not_mem
      after letter separator separatorNotAfter
  rw [beforeFilter, middleFilter, afterFilter]
  simp

private theorem twoSeparator_pairProjection
    {separator target : Nat}
    {letters before middle after : List Nat}
    (split :
      letters =
        before ++ separator :: (middle ++ separator :: after))
    (beforeNodup : before.Nodup)
    (middleNodup : middle.Nodup)
    (afterNodup : after.Nodup)
    (separatorNotBefore : separator ∉ before)
    (separatorNotMiddle : separator ∉ middle)
    (separatorNotAfter : separator ∉ after) :
    letters.filter
        (fun value => value == target || value == separator) =
      (if target ∈ before then [target] else []) ++
        separator ::
          ((if target ∈ middle then [target] else []) ++
            separator :: (if target ∈ after then [target] else [])) := by
  rw [split, List.filter_append, List.filter_cons,
    List.filter_append, List.filter_cons]
  have beforeFilter :=
    twoSeparator_blockProjection
      (target := target) beforeNodup separatorNotBefore
  have middleFilter :=
    twoSeparator_blockProjection
      (target := target) middleNodup separatorNotMiddle
  have afterFilter :=
    twoSeparator_blockProjection
      (target := target) afterNodup separatorNotAfter
  rw [beforeFilter, middleFilter, afterFilter]
  simp

private theorem filter_or_or_eq_eq_filter_or_eq_of_not_mem
    (letters : List Nat) (first second third : Nat)
    (thirdAbsent : third ∉ letters) :
    letters.filter
        (fun value =>
          value == first || value == second || value == third) =
      letters.filter
        (fun value => value == first || value == second) := by
  apply List.filter_congr
  intro value valueMember
  have valueNeThird : value ≠ third := by
    intro equality
    subst value
    exact thirdAbsent valueMember
  simp [valueNeThird]

private theorem twoSeparator_before_mem_iff_head_eq
    {separator target : Nat}
    {letters before middle after : List Nat}
    (split :
      letters =
        before ++ separator :: (middle ++ separator :: after))
    (beforeNodup : before.Nodup)
    (middleNodup : middle.Nodup)
    (afterNodup : after.Nodup)
    (separatorNotBefore : separator ∉ before)
    (separatorNotMiddle : separator ∉ middle)
    (separatorNotAfter : separator ∉ after)
    (different : target ≠ separator) :
    target ∈ before ↔
      (letters.filter
        (fun value => value == target || value == separator)).head? =
          some target := by
  rw [twoSeparator_pairProjection split beforeNodup middleNodup
    afterNodup separatorNotBefore separatorNotMiddle separatorNotAfter]
  by_cases beforeMember : target ∈ before <;>
    by_cases middleMember : target ∈ middle <;>
      by_cases afterMember : target ∈ after <;>
        simp_all [Ne.symm different]

private theorem twoSeparator_middle_mem_iff_no_separator_selfEdge
    {separator target : Nat}
    {letters before middle after : List Nat}
    (split :
      letters =
        before ++ separator :: (middle ++ separator :: after))
    (beforeNodup : before.Nodup)
    (middleNodup : middle.Nodup)
    (afterNodup : after.Nodup)
    (separatorNotBefore : separator ∉ before)
    (separatorNotMiddle : separator ∉ middle)
    (separatorNotAfter : separator ∉ after)
    (different : target ≠ separator) :
    target ∈ middle ↔
      (separator, separator) ∉
        adjacentPairsList
          (letters.filter
            (fun value => value == target || value == separator)) := by
  rw [twoSeparator_pairProjection split beforeNodup middleNodup
    afterNodup separatorNotBefore separatorNotMiddle separatorNotAfter]
  by_cases beforeMember : target ∈ before <;>
    by_cases middleMember : target ∈ middle <;>
      by_cases afterMember : target ∈ after <;>
        simp_all [adjacentPairsList, Word.adjacentPairsFrom,
          Ne.symm different]

private theorem twoSeparator_after_mem_iff_last_eq
    {separator target : Nat}
    {letters before middle after : List Nat}
    (split :
      letters =
        before ++ separator :: (middle ++ separator :: after))
    (beforeNodup : before.Nodup)
    (middleNodup : middle.Nodup)
    (afterNodup : after.Nodup)
    (separatorNotBefore : separator ∉ before)
    (separatorNotMiddle : separator ∉ middle)
    (separatorNotAfter : separator ∉ after)
    (different : target ≠ separator) :
    target ∈ after ↔
      (letters.filter
        (fun value => value == target || value == separator)).getLast? =
          some target := by
  rw [twoSeparator_pairProjection split beforeNodup middleNodup
    afterNodup separatorNotBefore separatorNotMiddle separatorNotAfter]
  by_cases beforeMember : target ∈ before <;>
    by_cases middleMember : target ∈ middle <;>
      by_cases afterMember : target ∈ after <;>
        simp_all [Ne.symm different]

private theorem nodup_two_letter_shape
    {first second : Nat}
    (different : first ≠ second) :
    ∀ {letters : List Nat},
      letters.Nodup →
      (∀ letter, letter ∈ letters →
        letter = first ∨ letter = second) →
      letters = [] ∨ letters = [first] ∨ letters = [second] ∨
        letters = [first, second] ∨ letters = [second, first]
  | [], _, _ => by simp
  | head :: tail, nodup, only => by
      simp only [List.nodup_cons] at nodup
      have headCases :
          head = first ∨ head = second :=
        only head (by simp)
      have tailOnly :
          ∀ letter, letter ∈ tail →
            letter = first ∨ letter = second := by
        intro letter member
        exact only letter (by simp [member])
      have tailShape :=
        nodup_two_letter_shape different nodup.2 tailOnly
      rcases headCases with rfl | rfl <;>
        rcases tailShape with rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Ne.symm different]

private theorem nodup_two_letter_shape_of_both_mem
    {first second : Nat} {letters : List Nat}
    (different : first ≠ second)
    (nodup : letters.Nodup)
    (only :
      ∀ letter, letter ∈ letters →
        letter = first ∨ letter = second)
    (firstMember : first ∈ letters)
    (secondMember : second ∈ letters) :
    letters = [first, second] ∨
      letters = [second, first] := by
  rcases nodup_two_letter_shape different nodup only with
    rfl | rfl | rfl | rfl | rfl <;>
      simp_all [Ne.symm different]

private theorem twoSeparator_middle_pair_head_eq
    {separator first second : Nat}
    {before leftMiddle rightMiddle after : List Nat}
    (firstNeSecond : first ≠ second)
    (separatorNeFirst : separator ≠ first)
    (separatorNeSecond : separator ≠ second)
    (beforeNodup : before.Nodup)
    (leftMiddleNodup : leftMiddle.Nodup)
    (rightMiddleNodup : rightMiddle.Nodup)
    (afterNodup : after.Nodup)
    (beforeOnly :
      ∀ letter, letter ∈ before →
        letter = first ∨ letter = second)
    (leftMiddleOnly :
      ∀ letter, letter ∈ leftMiddle →
        letter = first ∨ letter = second)
    (rightMiddleOnly :
      ∀ letter, letter ∈ rightMiddle →
        letter = first ∨ letter = second)
    (afterOnly :
      ∀ letter, letter ∈ after →
        letter = first ∨ letter = second)
    (leftFirstMember : first ∈ leftMiddle)
    (leftSecondMember : second ∈ leftMiddle)
    (rightFirstMember : first ∈ rightMiddle)
    (rightSecondMember : second ∈ rightMiddle)
    (marked :
      SameMarkedDigraphList
        (before ++ separator :: (leftMiddle ++ separator :: after))
        (before ++ separator :: (rightMiddle ++ separator :: after))) :
    leftMiddle.head? = rightMiddle.head? := by
  have markedHead := marked.1
  have markedLast := marked.2.1
  have edgeSeparatorSeparator :=
    marked.2.2.2 separator separator
  have edgeSeparatorFirst :=
    marked.2.2.2 separator first
  have edgeSeparatorSecond :=
    marked.2.2.2 separator second
  have edgeFirstSeparator :=
    marked.2.2.2 first separator
  have edgeFirstFirst :=
    marked.2.2.2 first first
  have edgeFirstSecond :=
    marked.2.2.2 first second
  have edgeSecondSeparator :=
    marked.2.2.2 second separator
  have edgeSecondFirst :=
    marked.2.2.2 second first
  have edgeSecondSecond :=
    marked.2.2.2 second second
  have beforeShape :=
    nodup_two_letter_shape firstNeSecond beforeNodup beforeOnly
  have leftMiddleShape :=
    nodup_two_letter_shape_of_both_mem firstNeSecond
      leftMiddleNodup leftMiddleOnly leftFirstMember leftSecondMember
  have rightMiddleShape :=
    nodup_two_letter_shape_of_both_mem firstNeSecond
      rightMiddleNodup rightMiddleOnly rightFirstMember rightSecondMember
  have afterShape :=
    nodup_two_letter_shape firstNeSecond afterNodup afterOnly
  rcases leftMiddleShape with rfl | rfl
  · rcases rightMiddleShape with rfl | rfl
    · rfl
    · exfalso
      rcases beforeShape with rfl | rfl | rfl | rfl | rfl <;>
        rcases afterShape with rfl | rfl | rfl | rfl | rfl <;>
          simp_all [adjacentPairsList,
            Word.adjacentPairsFrom, List.head?, List.getLast?,
            Prod.mk.injEq, Ne.symm firstNeSecond,
            Ne.symm separatorNeFirst, Ne.symm separatorNeSecond] <;>
          grind
  · rcases rightMiddleShape with rfl | rfl
    · exfalso
      rcases beforeShape with rfl | rfl | rfl | rfl | rfl <;>
        rcases afterShape with rfl | rfl | rfl | rfl | rfl <;>
          simp_all [adjacentPairsList,
            Word.adjacentPairsFrom, List.head?, List.getLast?,
            Prod.mk.injEq, Ne.symm firstNeSecond,
            Ne.symm separatorNeFirst, Ne.symm separatorNeSecond] <;>
          grind
    · rfl

/-- A two-separator duplicate-free factorization is rigid once a
deletion-equivalent competitor is known to retain exactly two separators. -/
theorem twoSeparatorNodupFactorization_rigid
    {separator : Nat} {left right : Word Nat}
    (leftShape :
      TwoSeparatorNodupFactorization separator left.toList)
    (same : SameDeletionMarkedDigraph left right)
    (rightSeparatorCount :
      right.toList.count separator = 2) :
    right = left := by
  rcases leftShape with
    ⟨leftBefore, leftMiddle, leftAfter, leftSplit,
      leftBeforeNodup, leftMiddleNodup, leftAfterNodup,
      separatorNotLeftBefore, separatorNotLeftMiddle,
      separatorNotLeftAfter⟩
  obtain
    ⟨rightBefore, rightMiddle, rightAfter,
      separatorNotRightBefore, separatorNotRightMiddle,
      separatorNotRightAfter, rightSplit⟩ :=
    exists_two_occurrence_split_of_count_eq_two rightSeparatorCount
  have rightBeforeBound :
      ∀ letter, rightBefore.count letter ≤ 1 := by
    intro letter
    by_cases equality : letter = separator
    · subst letter
      simp [List.count_eq_zero.mpr separatorNotRightBefore]
    · apply Nat.lt_succ_iff.mp
      apply Decidable.byContradiction
      intro notLess
      have countBound : 2 ≤ rightBefore.count letter := by omega
      have localEdge :=
        selfEdge_of_count_ge_two countBound
      have rightProjection :=
        twoSeparator_split_pairProjection rightSplit
          separatorNotRightBefore separatorNotRightMiddle
          separatorNotRightAfter (letter := letter)
      have fullEdge :
          (letter, letter) ∈
            adjacentPairsList
              (right.toList.filter
                (fun value =>
                  value == letter || value == separator)) := by
        rw [rightProjection]
        exact adjacentPairsList_append_left localEdge
      have marked :=
        same (fun value =>
          value == letter || value == separator)
      have leftEdge :=
        (marked.2.2.2 letter letter).mpr fullEdge
      exact
        (twoSeparatorNodupFactorization_pairProjection_no_selfEdge
          (separator := separator)
          (target := letter)
          ⟨leftBefore, leftMiddle, leftAfter, leftSplit,
            leftBeforeNodup, leftMiddleNodup, leftAfterNodup,
            separatorNotLeftBefore, separatorNotLeftMiddle,
            separatorNotLeftAfter⟩ equality) leftEdge
  have rightMiddleBound :
      ∀ letter, rightMiddle.count letter ≤ 1 := by
    intro letter
    by_cases equality : letter = separator
    · subst letter
      simp [List.count_eq_zero.mpr separatorNotRightMiddle]
    · apply Nat.lt_succ_iff.mp
      apply Decidable.byContradiction
      intro notLess
      have countBound : 2 ≤ rightMiddle.count letter := by omega
      have localEdge :=
        selfEdge_of_count_ge_two countBound
      have rightProjection :=
        twoSeparator_split_pairProjection rightSplit
          separatorNotRightBefore separatorNotRightMiddle
          separatorNotRightAfter (letter := letter)
      have fullEdge :
          (letter, letter) ∈
            adjacentPairsList
              (right.toList.filter
                (fun value =>
                  value == letter || value == separator)) := by
        rw [rightProjection]
        have middleEdge :
            (letter, letter) ∈
              adjacentPairsList
                (rightMiddle.filter (fun value => value == letter) ++
                  separator ::
                    rightAfter.filter (fun value => value == letter)) :=
          adjacentPairsList_append_left localEdge
        have embedded :=
          adjacentPairsList_append_right
            (firstList :=
              rightBefore.filter (fun value => value == letter) ++
                [separator])
            middleEdge
        simpa [List.append_assoc] using embedded
      have marked :=
        same (fun value =>
          value == letter || value == separator)
      have leftEdge :=
        (marked.2.2.2 letter letter).mpr fullEdge
      exact
        (twoSeparatorNodupFactorization_pairProjection_no_selfEdge
          (separator := separator)
          (target := letter)
          ⟨leftBefore, leftMiddle, leftAfter, leftSplit,
            leftBeforeNodup, leftMiddleNodup, leftAfterNodup,
            separatorNotLeftBefore, separatorNotLeftMiddle,
            separatorNotLeftAfter⟩ equality) leftEdge
  have rightAfterBound :
      ∀ letter, rightAfter.count letter ≤ 1 := by
    intro letter
    by_cases equality : letter = separator
    · subst letter
      simp [List.count_eq_zero.mpr separatorNotRightAfter]
    · apply Nat.lt_succ_iff.mp
      apply Decidable.byContradiction
      intro notLess
      have countBound : 2 ≤ rightAfter.count letter := by omega
      have localEdge :=
        selfEdge_of_count_ge_two countBound
      have rightProjection :=
        twoSeparator_split_pairProjection rightSplit
          separatorNotRightBefore separatorNotRightMiddle
          separatorNotRightAfter (letter := letter)
      have fullEdge :
          (letter, letter) ∈
            adjacentPairsList
              (right.toList.filter
                (fun value =>
                  value == letter || value == separator)) := by
        rw [rightProjection]
        have embedded :=
          adjacentPairsList_append_right
            (firstList :=
              rightBefore.filter (fun value => value == letter) ++
                [separator] ++
                  rightMiddle.filter (fun value => value == letter) ++
                    [separator])
            localEdge
        simpa [List.append_assoc] using embedded
      have marked :=
        same (fun value =>
          value == letter || value == separator)
      have leftEdge :=
        (marked.2.2.2 letter letter).mpr fullEdge
      exact
        (twoSeparatorNodupFactorization_pairProjection_no_selfEdge
          (separator := separator)
          (target := letter)
          ⟨leftBefore, leftMiddle, leftAfter, leftSplit,
            leftBeforeNodup, leftMiddleNodup, leftAfterNodup,
            separatorNotLeftBefore, separatorNotLeftMiddle,
            separatorNotLeftAfter⟩ equality) leftEdge
  have rightBeforeNodup :=
    nodup_of_count_le_one rightBeforeBound
  have rightMiddleNodup :=
    nodup_of_count_le_one rightMiddleBound
  have rightAfterNodup :=
    nodup_of_count_le_one rightAfterBound
  have blockMembers :
      ∀ letter,
        (letter ∈ leftBefore ↔ letter ∈ rightBefore) ∧
        (letter ∈ leftMiddle ↔ letter ∈ rightMiddle) ∧
        (letter ∈ leftAfter ↔ letter ∈ rightAfter) := by
    intro letter
    by_cases equality : letter = separator
    · subst letter
      simp [separatorNotLeftBefore, separatorNotLeftMiddle,
        separatorNotLeftAfter, separatorNotRightBefore,
        separatorNotRightMiddle, separatorNotRightAfter]
    · have marked :=
        same (fun value =>
          value == letter || value == separator)
      constructor
      · rw [twoSeparator_before_mem_iff_head_eq leftSplit
            leftBeforeNodup leftMiddleNodup leftAfterNodup
            separatorNotLeftBefore separatorNotLeftMiddle
            separatorNotLeftAfter equality,
          twoSeparator_before_mem_iff_head_eq rightSplit
            rightBeforeNodup rightMiddleNodup rightAfterNodup
            separatorNotRightBefore separatorNotRightMiddle
            separatorNotRightAfter equality]
        rw [marked.1]
      constructor
      · rw [twoSeparator_middle_mem_iff_no_separator_selfEdge leftSplit
            leftBeforeNodup leftMiddleNodup leftAfterNodup
            separatorNotLeftBefore separatorNotLeftMiddle
            separatorNotLeftAfter equality,
          twoSeparator_middle_mem_iff_no_separator_selfEdge rightSplit
            rightBeforeNodup rightMiddleNodup rightAfterNodup
            separatorNotRightBefore separatorNotRightMiddle
            separatorNotRightAfter equality]
        exact not_congr (marked.2.2.2 separator separator)
      · rw [twoSeparator_after_mem_iff_last_eq leftSplit
            leftBeforeNodup leftMiddleNodup leftAfterNodup
            separatorNotLeftBefore separatorNotLeftMiddle
            separatorNotLeftAfter equality,
          twoSeparator_after_mem_iff_last_eq rightSplit
            rightBeforeNodup rightMiddleNodup rightAfterNodup
            separatorNotRightBefore separatorNotRightMiddle
            separatorNotRightAfter equality]
        rw [marked.2.1]
  have beforeMembers :
      ∀ letter, letter ∈ leftBefore ↔ letter ∈ rightBefore :=
    fun letter => (blockMembers letter).1
  have middleMembers :
      ∀ letter, letter ∈ leftMiddle ↔ letter ∈ rightMiddle :=
    fun letter => (blockMembers letter).2.1
  have afterMembers :
      ∀ letter, letter ∈ leftAfter ↔ letter ∈ rightAfter :=
    fun letter => (blockMembers letter).2.2
  have beforePairHeads :
      ∀ first second,
        first ≠ second →
        first ∈ leftBefore →
        second ∈ leftBefore →
        (leftBefore.filter
            (fun value => value == first || value == second)).head? =
          (rightBefore.filter
            (fun value => value == first || value == second)).head? := by
    intro first second different firstMember secondMember
    have separatorNeFirst : separator ≠ first := by
      intro equality
      subst first
      exact separatorNotLeftBefore firstMember
    have separatorNeSecond : separator ≠ second := by
      intro equality
      subst second
      exact separatorNotLeftBefore secondMember
    have rightFirstMember : first ∈ rightBefore :=
      (beforeMembers first).mp firstMember
    have marked :=
      same (fun value => value == first || value == second)
    have markedHead := marked.1
    rw [pairProjection_head_of_left leftSplit separatorNeFirst
          separatorNeSecond firstMember,
        pairProjection_head_of_left rightSplit separatorNeFirst
          separatorNeSecond rightFirstMember] at markedHead
    exact markedHead
  have leftSecondSplit :
      left.toList =
        (leftBefore ++ separator :: leftMiddle) ++
          separator :: leftAfter := by
    rw [leftSplit]
    simp [List.append_assoc]
  have rightSecondSplit :
      right.toList =
        (rightBefore ++ separator :: rightMiddle) ++
          separator :: rightAfter := by
    rw [rightSplit]
    simp [List.append_assoc]
  have afterPairLasts :
      ∀ first second,
        first ≠ second →
        first ∈ leftAfter →
        second ∈ leftAfter →
        (leftAfter.filter
            (fun value => value == first || value == second)).getLast? =
          (rightAfter.filter
            (fun value => value == first || value == second)).getLast? := by
    intro first second different firstMember secondMember
    have separatorNeFirst : separator ≠ first := by
      intro equality
      subst first
      exact separatorNotLeftAfter firstMember
    have separatorNeSecond : separator ≠ second := by
      intro equality
      subst second
      exact separatorNotLeftAfter secondMember
    have rightFirstMember : first ∈ rightAfter :=
      (afterMembers first).mp firstMember
    have marked :=
      same (fun value => value == first || value == second)
    have markedLast := marked.2.1
    rw [pairProjection_last_of_right leftSecondSplit separatorNeFirst
          separatorNeSecond firstMember,
        pairProjection_last_of_right rightSecondSplit separatorNeFirst
          separatorNeSecond rightFirstMember] at markedLast
    exact markedLast
  have beforeEq :=
    nodup_eq_of_pairProjection_head leftBeforeNodup rightBeforeNodup
      beforeMembers beforePairHeads
  have afterEq :=
    nodup_eq_of_pairProjection_last leftAfterNodup rightAfterNodup
      afterMembers afterPairLasts
  have middlePairHeads :
      ∀ first second,
        first ≠ second →
        first ∈ leftMiddle →
        second ∈ leftMiddle →
        (leftMiddle.filter
            (fun value => value == first || value == second)).head? =
          (rightMiddle.filter
            (fun value => value == first || value == second)).head? := by
    intro first second different firstMember secondMember
    have separatorNeFirst : separator ≠ first := by
      intro equality
      subst first
      exact separatorNotLeftMiddle firstMember
    have separatorNeSecond : separator ≠ second := by
      intro equality
      subst second
      exact separatorNotLeftMiddle secondMember
    have rightFirstMember : first ∈ rightMiddle :=
      (middleMembers first).mp firstMember
    have rightSecondMember : second ∈ rightMiddle :=
      (middleMembers second).mp secondMember
    let keep :=
      fun value : Nat =>
        value == first || value == second || value == separator
    have leftProjection :
        left.toList.filter keep =
          leftBefore.filter
              (fun value => value == first || value == second) ++
            separator ::
              (leftMiddle.filter
                  (fun value => value == first || value == second) ++
                separator ::
                  leftAfter.filter
                    (fun value =>
                      value == first || value == second)) := by
      rw [leftSplit, List.filter_append, List.filter_cons,
        List.filter_append, List.filter_cons]
      simp only [keep, beq_self_eq_true, Bool.or_true, if_true]
      rw [filter_or_or_eq_eq_filter_or_eq_of_not_mem
          leftBefore first second separator separatorNotLeftBefore,
        filter_or_or_eq_eq_filter_or_eq_of_not_mem
          leftMiddle first second separator separatorNotLeftMiddle,
        filter_or_or_eq_eq_filter_or_eq_of_not_mem
          leftAfter first second separator separatorNotLeftAfter]
    have rightProjection :
        right.toList.filter keep =
          rightBefore.filter
              (fun value => value == first || value == second) ++
            separator ::
              (rightMiddle.filter
                  (fun value => value == first || value == second) ++
                separator ::
                  rightAfter.filter
                    (fun value =>
                      value == first || value == second)) := by
      rw [rightSplit, List.filter_append, List.filter_cons,
        List.filter_append, List.filter_cons]
      simp only [keep, beq_self_eq_true, Bool.or_true, if_true]
      rw [filter_or_or_eq_eq_filter_or_eq_of_not_mem
          rightBefore first second separator separatorNotRightBefore,
        filter_or_or_eq_eq_filter_or_eq_of_not_mem
          rightMiddle first second separator separatorNotRightMiddle,
        filter_or_or_eq_eq_filter_or_eq_of_not_mem
          rightAfter first second separator separatorNotRightAfter]
    have marked := same keep
    rw [leftProjection, rightProjection, ← beforeEq, ← afterEq] at marked
    apply twoSeparator_middle_pair_head_eq
      (before :=
        leftBefore.filter
          (fun value => value == first || value == second))
      (leftMiddle :=
        leftMiddle.filter
          (fun value => value == first || value == second))
      (rightMiddle :=
        rightMiddle.filter
          (fun value => value == first || value == second))
      (after :=
        leftAfter.filter
          (fun value => value == first || value == second))
      different separatorNeFirst separatorNeSecond
    · exact List.filter_sublist.nodup leftBeforeNodup
    · exact List.filter_sublist.nodup leftMiddleNodup
    · exact List.filter_sublist.nodup rightMiddleNodup
    · exact List.filter_sublist.nodup leftAfterNodup
    · intro letter member
      have kept :
          (letter == first || letter == second) = true :=
        (List.mem_filter.mp member).2
      simpa only [Bool.or_eq_true, beq_iff_eq] using kept
    · intro letter member
      have kept :
          (letter == first || letter == second) = true :=
        (List.mem_filter.mp member).2
      simpa only [Bool.or_eq_true, beq_iff_eq] using kept
    · intro letter member
      have kept :
          (letter == first || letter == second) = true :=
        (List.mem_filter.mp member).2
      simpa only [Bool.or_eq_true, beq_iff_eq] using kept
    · intro letter member
      have kept :
          (letter == first || letter == second) = true :=
        (List.mem_filter.mp member).2
      simpa only [Bool.or_eq_true, beq_iff_eq] using kept
    · exact List.mem_filter.mpr ⟨firstMember, by simp⟩
    · exact List.mem_filter.mpr ⟨secondMember, by simp⟩
    · exact List.mem_filter.mpr ⟨rightFirstMember, by simp⟩
    · exact List.mem_filter.mpr ⟨rightSecondMember, by simp⟩
    · exact marked
  have middleEq :=
    nodup_eq_of_pairProjection_head leftMiddleNodup rightMiddleNodup
      middleMembers middlePairHeads
  apply Word.toList_injective
  rw [leftSplit, rightSplit, beforeEq, middleEq, afterEq]

/-- An exactly twice-occurring source variable that owns the distinguished
anchor separator is a direct rigidity witness once its competing
multiplicity is known.  This packages the corrected factorization theorem
with its reconstruction theorem and avoids reopening the alternating
triple-occurrence argument in the equal-owner branch. -/
theorem preimage_two_occurrence_separator_owner_rigid
    {bound : Nat} {word other : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    (same : SameDeletionMarkedDigraph word other)
    {owner : Nat}
    (ownerCount : word.toList.count owner = 2)
    (separatorMember :
      3 * bound + 2 ∈ (substitution owner).toList)
    (otherOwnerCount : other.toList.count owner = 2) :
    other = word := by
  exact
    twoSeparatorNodupFactorization_rigid
      (preimage_two_occurrence_separator_owner_factorization
        mapped ownerCount separatorMember)
      same otherOwnerCount

/-- A natural word-equation reconstruction candidate.  The explicit
bound-six counterexample below shows that this proposition is too strong:
factorizations of the anchor need not have a common singleton pivot. -/
def AnchorFactorizationReconstruction : Prop :=
  ∀ bound (word : Word Nat),
    WordUsesAtMost word bound →
    ∀ substitution,
      word.bind substitution = anchor (3 * bound) →
      ∃ pivot,
        SingletonPivotFactorization pivot word.toList

/-- A fixed source word is rigid for the complete family of deletion marked
digraphs.  This is the correct local target: it permits several overlapping
local pivots instead of requiring one global pivot. -/
def DeletionGraphRigidWord (word : Word Nat) : Prop :=
  ∀ other,
    SameDeletionMarkedDigraph word other →
    other = word

/-- Source-specific reconstruction once all competing multiplicities have a
uniform bound.  A generic bound-three reconstruction theorem is false, so
triple-occurrence anchor preimages must supply this additional certificate. -/
def BoundedMultiplicityRigidityCertificate
    (bound : Nat) (word : Word Nat) : Prop :=
  ∀ other,
    SameDeletionMarkedDigraph word other →
    (∀ letter, other.toList.count letter ≤ bound) →
    other = word

/-- A source word is reconstructible from its deletion marked digraphs once
the exact multiplicity of every variable is known.  This separates the two
uniform Trahtman obligations: multiplicity preservation and reconstruction
from those preserved multiplicities. -/
def ExactCountRigidityCertificate (word : Word Nat) : Prop :=
  ∀ other,
    SameDeletionMarkedDigraph word other →
    (∀ letter,
      other.toList.count letter = word.toList.count letter) →
    other = word

/-- A 2-limited source is reconstructible once every competing variable has
the same exact multiplicity. -/
theorem exactCountRigidityCertificate_of_twoLimited
    {word : Word Nat}
    (sourceLimited : TwoLimitedList word.toList) :
    ExactCountRigidityCertificate word := by
  intro other same exactCounts
  apply sameDeletionMarkedDigraph_eq_of_twoLimited
    same sourceLimited
  intro letter
  rw [exactCounts letter]
  exact sourceLimited letter

/-- An anchor preimage with no triple-occurring source variable lies in the
2-limited exact-count reconstruction branch. -/
theorem
    preimage_exactCountRigidityCertificate_of_no_three_occurrence
    {bound : Nat} {word : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    (noThree :
      ∀ letter, letter ∈ word.toList →
        word.toList.count letter ≠ 3) :
    ExactCountRigidityCertificate word := by
  apply exactCountRigidityCertificate_of_twoLimited
  intro letter
  have countBound := preimage_threeLimitedList mapped letter
  by_cases member : letter ∈ word.toList
  · have countNeThree := noThree letter member
    omega
  · rw [List.count_eq_zero.mpr member]
    omega

/-- A source-specific bound-three reconstruction certificate, together with
local multiplicity certificates for every source variable, proves full
deletion-graph rigidity. -/
theorem deletionGraphRigidWord_of_localThreeLimitedCover
    {word : Word Nat}
    (rigidity : BoundedMultiplicityRigidityCertificate 3 word)
    (covered :
      ∀ letter, letter ∈ word.toList →
        LocalThreeLimitedCertificate word letter) :
    DeletionGraphRigidWord word := by
  intro other same
  apply rigidity other same
  intro letter
  by_cases member : letter ∈ word.toList
  · exact (covered letter member).right_count_le_three same
  · have leftZero :
        word.toList.count letter = 0 :=
      List.count_eq_zero.mpr member
    have rightZero :=
      (sameDeletionMarkedDigraph_count_eq_zero_iff
        same letter).mp leftZero
    omega

/-- A 2-limited source is rigid as soon as the anchor-specific argument
shows that deletion-equivalent competitors remain 2-limited.  The exact
word reconstruction is discharged by
`sameDeletionMarkedDigraph_eq_of_twoLimited`; no pivot is needed here. -/
theorem deletionGraphRigidWord_of_twoLimited_preservation
    {word : Word Nat}
    (sourceLimited : TwoLimitedList word.toList)
    (preserved :
      ∀ other,
        SameDeletionMarkedDigraph word other →
        TwoLimitedList other.toList) :
    DeletionGraphRigidWord word := by
  intro other same
  exact sameDeletionMarkedDigraph_eq_of_twoLimited
    same sourceLimited (preserved other same)

/-- Corrected anchor-preimage reconstruction boundary.  A proof may use
different local separators for different repeated variables; only the final
deletion-graph rigidity of each actual preimage is required. -/
def AnchorPreimageDeletionRigidity : Prop :=
  ∀ bound (word : Word Nat),
    WordUsesAtMost word bound →
    ∀ substitution,
      word.bind substitution = anchor (3 * bound) →
      DeletionGraphRigidWord word

/-- A concrete local-certificate endpoint for anchor preimages.

Every actual preimage of the anchor must be 2-limited, and every variable in
that preimage must have a local control certificate.  Unlike the false global
singleton-pivot condition, different variables may use different overlapping
controllers. -/
def AnchorPreimageLocalTwoLimitedCover : Prop :=
  ∀ bound (word : Word Nat),
    WordUsesAtMost word bound →
    ∀ substitution,
      word.bind substitution = anchor (3 * bound) →
      TwoLimitedList word.toList ∧
        ∀ letter, letter ∈ word.toList →
          LocalTwoLimitedCertificate word letter

/-- The corrected anchor endpoint split into its two triple-occurrence
obligations: local multiplicity bounds and source-specific reconstruction
under those bounds. -/
def AnchorPreimageLocalThreeLimitedRigidity : Prop :=
  ∀ bound (word : Word Nat),
    WordUsesAtMost word bound →
    ∀ substitution,
      word.bind substitution = anchor (3 * bound) →
      BoundedMultiplicityRigidityCertificate 3 word ∧
        ∀ letter, letter ∈ word.toList →
          LocalThreeLimitedCertificate word letter

/-- Uniform local control of every exactly twice-occurring variable in every
bounded anchor preimage. These are precisely the certificates additionally
needed by the equal-separator-owner triple-occurrence branch. -/
def AnchorPreimageTwoOccurrenceControl : Prop :=
  ∀ bound (word : Word Nat),
    WordUsesAtMost word bound →
    ∀ substitution,
      word.bind substitution = anchor (3 * bound) →
      ∀ letter,
        letter ∈ word.toList →
        word.toList.count letter = 2 →
        LocalTwoLimitedCertificate word letter

/-- Exact multiplicities are preserved across every deletion-equivalent
competitor of every bounded anchor preimage. -/
def AnchorPreimageExactCountPreservation : Prop :=
  ∀ bound (word : Word Nat),
    WordUsesAtMost word bound →
    ∀ substitution,
      word.bind substitution = anchor (3 * bound) →
      ∀ other,
        SameDeletionMarkedDigraph word other →
        ∀ letter,
          other.toList.count letter = word.toList.count letter

/-- Every bounded anchor preimage is reconstructible from its deletion
marked digraphs and exact variable multiplicities. -/
def AnchorPreimageExactCountRigidity : Prop :=
  ∀ bound (word : Word Nat),
    WordUsesAtMost word bound →
    ∀ substitution,
      word.bind substitution = anchor (3 * bound) →
      ExactCountRigidityCertificate word

/-- Uniform control of the exactly twice-occurring source variables implies
uniform exact-count preservation for all source multiplicity classes. -/
theorem
    anchorPreimageExactCountPreservation_of_twoOccurrenceControl
    (controlled : AnchorPreimageTwoOccurrenceControl) :
    AnchorPreimageExactCountPreservation := by
  intro bound word uses substitution mapped other same letter
  exact
    preimage_exact_count_preservation_of_two_occurrence_control
      mapped same
        (controlled bound word uses substitution mapped)
      letter

/-- A local 2-limited cover for every anchor preimage proves the corrected
anchor-preimage rigidity boundary. -/
theorem anchorPreimageDeletionRigidity_of_localTwoLimitedCover
    (covered : AnchorPreimageLocalTwoLimitedCover) :
    AnchorPreimageDeletionRigidity := by
  intro bound word uses substitution mapped
  obtain ⟨sourceLimited, localCover⟩ :=
    covered bound word uses substitution mapped
  intro other same
  exact sameDeletionMarkedDigraph_eq_of_localTwoLimitedCover
    same sourceLimited localCover

/-- Local bound-three certificates plus source-specific bounded
reconstruction prove the corrected anchor-preimage rigidity boundary. -/
theorem anchorPreimageDeletionRigidity_of_localThreeLimitedRigidity
    (covered : AnchorPreimageLocalThreeLimitedRigidity) :
    AnchorPreimageDeletionRigidity := by
  intro bound word uses substitution mapped
  obtain ⟨rigidity, localCover⟩ :=
    covered bound word uses substitution mapped
  exact deletionGraphRigidWord_of_localThreeLimitedCover
    rigidity localCover

/-- Uniform exact-count preservation and exact-count reconstruction compose
to the corrected anchor-preimage deletion-rigidity boundary. -/
theorem anchorPreimageDeletionRigidity_of_exactCounts
    (preserved : AnchorPreimageExactCountPreservation)
    (rigid : AnchorPreimageExactCountRigidity) :
    AnchorPreimageDeletionRigidity := by
  intro bound word uses substitution mapped
  intro other same
  exact
    rigid bound word uses substitution mapped other same
      (preserved bound word uses substitution mapped other same)

/-- The corrected factorization boundary is exactly the original pure
preimage-rigidity endpoint, with the fixed-word obligation factored out. -/
theorem anchorPreimageDeletionRigidity_iff :
    AnchorPreimageDeletionRigidity ↔
      BoundedDeletionGraphPreimageRigidity := by
  rfl

/-- A global singleton pivot remains a sufficient local rigidity
certificate, but the bound-six counterexample below shows it is not a
necessary one. -/
theorem deletionGraphRigidWord_of_singletonPivot
    {pivot : Nat} {word : Word Nat}
    (shape : SingletonPivotFactorization pivot word.toList) :
    DeletionGraphRigidWord word := by
  intro other same
  exact singletonPivotFactorization_rigid shape same

/-- The now-refuted global singleton-pivot candidate would imply the
corrected endpoint.  This implication is retained to document the valid
downstream argument separately from its false antecedent. -/
theorem boundedDeletionGraphPreimageRigidity_of_factorizationReconstruction
    (reconstruct : AnchorFactorizationReconstruction) :
    BoundedDeletionGraphPreimageRigidity := by
  intro bound word uses substitution mapped other same
  obtain ⟨pivot, shape⟩ :=
    reconstruct bound word uses substitution mapped
  exact singletonPivotFactorization_rigid shape same

/-- Any direct multi-pivot or block-local proof of the corrected
factorization boundary closes the `A₂¹` preimage-rigidity endpoint. -/
theorem boundedDeletionGraphPreimageRigidity_of_anchorPreimageDeletionRigidity
    (rigid : AnchorPreimageDeletionRigidity) :
    BoundedDeletionGraphPreimageRigidity :=
  anchorPreimageDeletionRigidity_iff.mp rigid

/-- The local-cover criterion is sufficient for the original bounded
preimage-rigidity statement used by the Trahtman endpoint. -/
theorem boundedDeletionGraphPreimageRigidity_of_localTwoLimitedCover
    (covered : AnchorPreimageLocalTwoLimitedCover) :
    BoundedDeletionGraphPreimageRigidity :=
  boundedDeletionGraphPreimageRigidity_of_anchorPreimageDeletionRigidity
    (anchorPreimageDeletionRigidity_of_localTwoLimitedCover covered)

/-- The triple-aware local criterion is sufficient for the original bounded
preimage-rigidity statement used by the Trahtman endpoint. -/
theorem boundedDeletionGraphPreimageRigidity_of_localThreeLimitedRigidity
    (covered : AnchorPreimageLocalThreeLimitedRigidity) :
    BoundedDeletionGraphPreimageRigidity :=
  boundedDeletionGraphPreimageRigidity_of_anchorPreimageDeletionRigidity
    (anchorPreimageDeletionRigidity_of_localThreeLimitedRigidity covered)

/-! ## Exact boundary of the factorization candidate

At bound six, put

`u = a x z x c y z y d`

and map its variables to

* `a ↦ 0 ... 18`,
* `x ↦ 19`,
* `z ↦ 20`,
* `c ↦ 18 ... 1`,
* `y ↦ 0`,
* `d ↦ 1 ... 19`.

Then `u` maps to `anchor 18`.  The two occurrences of `x` lie strictly
before both occurrences of `y`, while `z` occurs between them.  The only
singleton variables are `a`, `c`, and `d`; none lies inside every repeated
variable interval.  Thus no singleton-pivot factorization exists.
-/

private def factorizationCounterexampleSource : Word Nat :=
  ⟨0, [1, 2, 1, 3, 4, 2, 4, 5]⟩

private def factorizationCounterexampleSubstitution : Nat → Word Nat
  | 0 => ⟨0, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]⟩
  | 1 => Word.singleton 19
  | 2 => Word.singleton 20
  | 3 => ⟨18, [17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1]⟩
  | 4 => Word.singleton 0
  | 5 => ⟨1, [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]⟩
  | _ => Word.singleton 0

private theorem factorizationCounterexample_uses :
    WordUsesAtMost factorizationCounterexampleSource 6 := by
  refine ⟨[0, 1, 2, 3, 4, 5], by decide, ?_⟩
  intro letter member
  change letter ∈ [0, 1, 2, 1, 3, 4, 2, 4, 5] at member
  change letter ∈ [0, 1, 2, 3, 4, 5]
  simp at member ⊢
  rcases member with
    equality | equality | equality | equality | equality |
      equality | equality | equality | equality <;>
    subst letter <;> simp

set_option maxHeartbeats 1000000 in
private theorem factorizationCounterexample_maps :
    factorizationCounterexampleSource.bind
        factorizationCounterexampleSubstitution =
      anchor 18 := by
  apply Word.toList_injective
  change
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
      17, 18, 19, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8,
      7, 6, 5, 4, 3, 2, 1, 0, 20, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
      11, 12, 13, 14, 15, 16, 17, 18, 19] =
        (anchor 18).toList
  rw [anchor_toList]
  decide

private theorem factorizationCounterexample_noPivot
    (pivot : Nat) :
    ¬SingletonPivotFactorization pivot
      factorizationCounterexampleSource.toList := by
  rintro ⟨left, right, split, leftNodup, rightNodup,
    pivotNotLeft, pivotNotRight⟩
  have pivotMember :
      pivot ∈ factorizationCounterexampleSource.toList := by
    rw [split]
    simp
  have pivotBound : pivot ≤ 5 := by
    change pivot ∈ [0, 1, 2, 1, 3, 4, 2, 4, 5] at pivotMember
    simp at pivotMember
    rcases pivotMember with
      equality | equality | equality | equality | equality |
        equality | equality | equality | equality
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have pivotCases :
      pivot = 0 ∨ pivot = 1 ∨ pivot = 2 ∨ pivot = 3 ∨
        pivot = 4 ∨ pivot = 5 := by
    omega
  rcases pivotCases with
    pivotEq | pivotEq | pivotEq | pivotEq | pivotEq | pivotEq <;>
      subst pivot
  · have projection :=
      singletonPivot_pairProjection split leftNodup rightNodup
        pivotNotLeft pivotNotRight (letter := 1)
    have concrete :
        factorizationCounterexampleSource.toList.filter
            (fun value => value == 1 || value == 0) =
          [0, 1, 1] := by
      decide
    rw [concrete] at projection
    by_cases leftMember : 1 ∈ left <;>
      by_cases rightMember : 1 ∈ right <;>
        simp [leftMember, rightMember] at projection
  · have projection :=
      singletonPivot_pairProjection split leftNodup rightNodup
        pivotNotLeft pivotNotRight (letter := 4)
    have concrete :
        factorizationCounterexampleSource.toList.filter
            (fun value => value == 4 || value == 1) =
          [1, 1, 4, 4] := by
      decide
    rw [concrete] at projection
    by_cases leftMember : 4 ∈ left <;>
      by_cases rightMember : 4 ∈ right <;>
        simp [leftMember, rightMember] at projection
  · have projection :=
      singletonPivot_pairProjection split leftNodup rightNodup
        pivotNotLeft pivotNotRight (letter := 1)
    have concrete :
        factorizationCounterexampleSource.toList.filter
            (fun value => value == 1 || value == 2) =
          [1, 2, 1, 2] := by
      decide
    rw [concrete] at projection
    by_cases leftMember : 1 ∈ left <;>
      by_cases rightMember : 1 ∈ right <;>
        simp [leftMember, rightMember] at projection
  · have projection :=
      singletonPivot_pairProjection split leftNodup rightNodup
        pivotNotLeft pivotNotRight (letter := 1)
    have concrete :
        factorizationCounterexampleSource.toList.filter
            (fun value => value == 1 || value == 3) =
          [1, 1, 3] := by
      decide
    rw [concrete] at projection
    by_cases leftMember : 1 ∈ left <;>
      by_cases rightMember : 1 ∈ right <;>
        simp [leftMember, rightMember] at projection
  · have projection :=
      singletonPivot_pairProjection split leftNodup rightNodup
        pivotNotLeft pivotNotRight (letter := 1)
    have concrete :
        factorizationCounterexampleSource.toList.filter
            (fun value => value == 1 || value == 4) =
          [1, 1, 4, 4] := by
      decide
    rw [concrete] at projection
    by_cases leftMember : 1 ∈ left <;>
      by_cases rightMember : 1 ∈ right <;>
        simp [leftMember, rightMember] at projection
  · have projection :=
      singletonPivot_pairProjection split leftNodup rightNodup
        pivotNotLeft pivotNotRight (letter := 4)
    have concrete :
        factorizationCounterexampleSource.toList.filter
            (fun value => value == 4 || value == 5) =
          [4, 4, 5] := by
      decide
    rw [concrete] at projection
    by_cases leftMember : 4 ∈ left <;>
      by_cases rightMember : 4 ∈ right <;>
        simp [leftMember, rightMember] at projection

private theorem factorizationCounterexample_twoLimited :
    TwoLimitedList factorizationCounterexampleSource.toList := by
  intro letter
  change
    [0, 1, 2, 1, 3, 4, 2, 4, 5].count letter ≤ 2
  simp only [List.count_cons, List.count_nil]
  grind

private theorem factorizationCounterexample_localCover
    (letter : Nat)
    (member : letter ∈ factorizationCounterexampleSource.toList) :
    LocalTwoLimitedCertificate
      factorizationCounterexampleSource letter := by
  change letter ∈ [0, 1, 2, 1, 3, 4, 2, 4, 5] at member
  simp at member
  rcases member with
    equality | equality | equality | equality | equality |
      equality | equality | equality | equality <;>
    subst letter
  · exact .singleton 0 (by decide)
  · have zCertificate :
        LocalTwoLimitedCertificate
          factorizationCounterexampleSource 2 :=
      .singletonSeparator 2 3
        (by decide) (by decide) (by decide)
    exact .lastController 1 2
      (by decide) zCertificate (by decide) (by decide)
  · exact .singletonSeparator 2 3
      (by decide) (by decide) (by decide)
  · have zCertificate :
        LocalTwoLimitedCertificate
          factorizationCounterexampleSource 2 :=
      .singletonSeparator 2 3
        (by decide) (by decide) (by decide)
    exact .lastController 1 2
      (by decide) zCertificate (by decide) (by decide)
  · exact .singleton 3 (by decide)
  · have zCertificate :
        LocalTwoLimitedCertificate
          factorizationCounterexampleSource 2 :=
      .singletonSeparator 2 3
        (by decide) (by decide) (by decide)
    exact .headController 4 2
      (by decide) zCertificate (by decide) (by decide)
  · exact .singletonSeparator 2 3
      (by decide) (by decide) (by decide)
  · have zCertificate :
        LocalTwoLimitedCertificate
          factorizationCounterexampleSource 2 :=
      .singletonSeparator 2 3
        (by decide) (by decide) (by decide)
    exact .headController 4 2
      (by decide) zCertificate (by decide) (by decide)
  · exact .singleton 5 (by decide)

/-- The bound-six counterexample to the global-pivot proposal is nevertheless
deletion rigid.  Its local control chain is

`c (singleton) -> z -> x` and `c (singleton) -> z -> y`.

The `z/x` projection is tail-marked, while the `z/y` projection is
head-marked.  This is the first fully checked example where overlapping
local separators replace a nonexistent global pivot. -/
theorem factorizationCounterexample_deletionGraphRigid :
    DeletionGraphRigidWord factorizationCounterexampleSource := by
  intro other same
  exact sameDeletionMarkedDigraph_eq_of_localTwoLimitedCover
    same factorizationCounterexample_twoLimited
      factorizationCounterexample_localCover

/-- The proposed unrestricted singleton-pivot reconstruction is false. -/
theorem not_anchorFactorizationReconstruction :
    ¬AnchorFactorizationReconstruction := by
  intro reconstruct
  obtain ⟨pivot, shape⟩ :=
    reconstruct 6 factorizationCounterexampleSource
      factorizationCounterexample_uses
      factorizationCounterexampleSubstitution
      factorizationCounterexample_maps
  exact factorizationCounterexample_noPivot pivot shape

/-! ## Exact boundary of the 2-limited local-cover criterion

The exact bound-four search supplies an anchor preimage with a triple
variable:

`u = a b c d a c a b`.

Map `a` to the singleton marker `0`, `b` to `1 ... 13`, `c` to the
separator `14`, and `d` to `13 ... 1`.  Then `u` maps to `anchor 12`, while
`a` occurs three times.  Consequently the local 2-limited cover above is a
useful sufficient fragment, but it cannot be the uniform Trahtman endpoint.
-/

private def tripleOccurrenceSource : Word Nat :=
  ⟨0, [1, 2, 3, 0, 2, 0, 1]⟩

private def tripleOccurrenceSubstitution : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => ⟨1, [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]⟩
  | 2 => Word.singleton 14
  | 3 => ⟨13, [12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1]⟩
  | _ => Word.singleton 0

private theorem tripleOccurrenceSource_uses :
    WordUsesAtMost tripleOccurrenceSource 4 := by
  refine ⟨[0, 1, 2, 3], by decide, ?_⟩
  intro letter member
  change letter ∈ [0, 1, 2, 3, 0, 2, 0, 1] at member
  change letter ∈ [0, 1, 2, 3]
  simp at member ⊢
  rcases member with
    equality | equality | equality | equality |
      equality | equality | equality | equality <;>
    subst letter <;> simp

set_option maxHeartbeats 1000000 in
private theorem tripleOccurrenceSource_maps :
    tripleOccurrenceSource.bind tripleOccurrenceSubstitution =
      anchor 12 := by
  apply Word.toList_injective
  change
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 13, 12,
      11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 14, 0, 1, 2, 3, 4, 5,
      6, 7, 8, 9, 10, 11, 12, 13] =
        (anchor 12).toList
  rw [anchor_toList]
  decide

private theorem tripleOccurrenceSource_not_twoLimited :
    ¬TwoLimitedList tripleOccurrenceSource.toList := by
  intro limited
  have countBound := limited 0
  change [0, 1, 2, 3, 0, 2, 0, 1].count 0 ≤ 2 at countBound
  simp at countBound

private theorem tripleOccurrenceSource_localThreeLimitedCover
    (letter : Nat)
    (member : letter ∈ tripleOccurrenceSource.toList) :
    LocalThreeLimitedCertificate tripleOccurrenceSource letter := by
  change letter ∈ [0, 1, 2, 3, 0, 2, 0, 1] at member
  simp at member
  rcases member with
    equality | equality | equality | equality |
      equality | equality | equality | equality <;>
    subst letter
  · have controllerCertificate :
        LocalTwoLimitedCertificate tripleOccurrenceSource 2 :=
      .singletonSeparator 2 3
        (by decide) (by decide) (by decide)
    exact .succOfTwoController 0 2
      (by decide) controllerCertificate (by decide)
  · exact .ofTwoLimited 1
      (.singletonSeparator 1 3
        (by decide) (by decide) (by decide))
  · exact .ofTwoLimited 2
      (.singletonSeparator 2 3
        (by decide) (by decide) (by decide))
  · exact .ofTwoLimited 3 (.singleton 3 (by decide))
  · have controllerCertificate :
        LocalTwoLimitedCertificate tripleOccurrenceSource 2 :=
      .singletonSeparator 2 3
        (by decide) (by decide) (by decide)
    exact .succOfTwoController 0 2
      (by decide) controllerCertificate (by decide)
  · exact .ofTwoLimited 2
      (.singletonSeparator 2 3
        (by decide) (by decide) (by decide))
  · have controllerCertificate :
        LocalTwoLimitedCertificate tripleOccurrenceSource 2 :=
      .singletonSeparator 2 3
        (by decide) (by decide) (by decide)
    exact .succOfTwoController 0 2
      (by decide) controllerCertificate (by decide)
  · exact .ofTwoLimited 1
      (.singletonSeparator 1 3
        (by decide) (by decide) (by decide))

/-- A finite marked-digraph digest for a two-letter deletion projection.
The exact multiplicities are checked separately below, so only the marked
endpoints and the four possible directed edges are needed here. -/
private def markedPairDigestEq
    (left right : List Nat) (first second : Nat) : Bool :=
  decide (left.head? = right.head?) &&
    decide (left.getLast? = right.getLast?) &&
    decide ((first, first) ∈ adjacentPairsList left ↔
      (first, first) ∈ adjacentPairsList right) &&
    decide ((first, second) ∈ adjacentPairsList left ↔
      (first, second) ∈ adjacentPairsList right) &&
    decide ((second, first) ∈ adjacentPairsList left ↔
      (second, first) ∈ adjacentPairsList right) &&
    decide ((second, second) ∈ adjacentPairsList left ↔
      (second, second) ∈ adjacentPairsList right)

private theorem markedPairDigestEq_true_of_same
    {left right : List Nat}
    (same : SameMarkedDigraphList left right)
    (first second : Nat) :
    markedPairDigestEq left right first second = true := by
  simp [markedPairDigestEq, same.1, same.2.1,
    same.2.2.2 first first, same.2.2.2 first second,
    same.2.2.2 second first, same.2.2.2 second second]

private def markedFullDigestEqFour
    (left right : List Nat) : Bool :=
  markedPairDigestEq left right 0 1 &&
    markedPairDigestEq left right 0 2 &&
    markedPairDigestEq left right 0 3 &&
    markedPairDigestEq left right 1 2 &&
    markedPairDigestEq left right 1 3 &&
    markedPairDigestEq left right 2 3

private theorem markedFullDigestEqFour_true_of_same
    {left right : List Nat}
    (same : SameMarkedDigraphList left right) :
    markedFullDigestEqFour left right = true := by
  have digest01 := markedPairDigestEq_true_of_same same 0 1
  have digest02 := markedPairDigestEq_true_of_same same 0 2
  have digest03 := markedPairDigestEq_true_of_same same 0 3
  have digest12 := markedPairDigestEq_true_of_same same 1 2
  have digest13 := markedPairDigestEq_true_of_same same 1 3
  have digest23 := markedPairDigestEq_true_of_same same 2 3
  simp [markedFullDigestEqFour, digest01, digest02, digest03,
    digest12, digest13, digest23]

private def tripleOccurrenceNecessary
    (letters : List Nat) : Bool :=
  decide (letters.count 0 = 3) &&
    decide (letters.count 1 = 2) &&
    decide (letters.count 2 = 2) &&
    decide (letters.count 3 = 1) &&
    markedPairDigestEq
      (tripleOccurrenceSource.toList.filter
        (fun value => value == 0 || value == 1))
      (letters.filter
        (fun value => value == 0 || value == 1)) 0 1 &&
    markedPairDigestEq
      (tripleOccurrenceSource.toList.filter
        (fun value => value == 0 || value == 2))
      (letters.filter
        (fun value => value == 0 || value == 2)) 0 2 &&
    markedPairDigestEq
      (tripleOccurrenceSource.toList.filter
        (fun value => value == 0 || value == 3))
      (letters.filter
        (fun value => value == 0 || value == 3)) 0 3 &&
    markedPairDigestEq
      (tripleOccurrenceSource.toList.filter
        (fun value => value == 1 || value == 2))
      (letters.filter
        (fun value => value == 1 || value == 2)) 1 2 &&
    markedPairDigestEq
      (tripleOccurrenceSource.toList.filter
        (fun value => value == 1 || value == 3))
      (letters.filter
        (fun value => value == 1 || value == 3)) 1 3 &&
    markedPairDigestEq
      (tripleOccurrenceSource.toList.filter
        (fun value => value == 2 || value == 3))
      (letters.filter
        (fun value => value == 2 || value == 3)) 2 3 &&
    markedFullDigestEqFour
      (tripleOccurrenceSource.toList.filter
        (fun value => value == 1 || value == 2 || value == 3))
      (letters.filter
        (fun value => value == 1 || value == 2 || value == 3)) &&
    markedFullDigestEqFour
      (tripleOccurrenceSource.toList.filter
        (fun value => value == 0 || value == 2 || value == 3))
      (letters.filter
        (fun value => value == 0 || value == 2 || value == 3)) &&
    markedFullDigestEqFour
      (tripleOccurrenceSource.toList.filter
        (fun value => value == 0 || value == 1 || value == 3))
      (letters.filter
        (fun value => value == 0 || value == 1 || value == 3)) &&
    markedFullDigestEqFour
      (tripleOccurrenceSource.toList.filter
        (fun value => value == 0 || value == 1 || value == 2))
      (letters.filter
        (fun value => value == 0 || value == 1 || value == 2)) &&
    markedFullDigestEqFour tripleOccurrenceSource.toList letters

private def tripleOccurrencePrefixCandidates
    (first second third fourth : Nat) : List (List Nat) :=
  (List.range 4).flatMap fun fifth =>
    (List.range 4).map fun sixth =>
      [0, first, second, third, fourth, fifth, sixth, 1]

private def tripleOccurrencePrefixRigidityCheck
    (first second third fourth : Nat) : Bool :=
  (tripleOccurrencePrefixCandidates
    first second third fourth).all fun candidate =>
    !tripleOccurrenceNecessary candidate ||
      decide (candidate = tripleOccurrenceSource.toList)

private theorem tripleOccurrencePrefixRigidityCheck_eq_true
    (first second third fourth : Nat)
    (firstSmall : first < 4)
    (secondSmall : second < 4)
    (thirdSmall : third < 4)
    (fourthSmall : fourth < 4) :
    tripleOccurrencePrefixRigidityCheck
      first second third fourth = true := by
  have firstCases :
      first = 0 ∨ first = 1 ∨ first = 2 ∨ first = 3 := by
    omega
  have secondCases :
      second = 0 ∨ second = 1 ∨ second = 2 ∨ second = 3 := by
    omega
  have thirdCases :
      third = 0 ∨ third = 1 ∨ third = 2 ∨ third = 3 := by
    omega
  have fourthCases :
      fourth = 0 ∨ fourth = 1 ∨ fourth = 2 ∨ fourth = 3 := by
    omega
  rcases firstCases with rfl | rfl | rfl | rfl <;>
    rcases secondCases with rfl | rfl | rfl | rfl <;>
      rcases thirdCases with rfl | rfl | rfl | rfl <;>
        rcases fourthCases with rfl | rfl | rfl | rfl <;>
      decide

/-- The first triple-occurrence anchor preimage has a fully kernel-checked
bounded-multiplicity reconstruction certificate.  Support preservation,
the local count lemmas, and the marked endpoints reduce an arbitrary
competitor to 256 sixteen-word prefix blocks; every block is reflected with
`by decide`. -/
theorem tripleOccurrenceSource_boundedMultiplicityRigidity :
    BoundedMultiplicityRigidityCertificate 3
      tripleOccurrenceSource := by
  intro other same bounded
  have twoCertificate :
      LocalTwoLimitedCertificate tripleOccurrenceSource 2 :=
    .singletonSeparator 2 3
      (by decide) (by decide) (by decide)
  have oneCertificate :
      LocalTwoLimitedCertificate tripleOccurrenceSource 1 :=
    .singletonSeparator 1 3
      (by decide) (by decide) (by decide)
  have countZero : other.toList.count 0 = 3 :=
    right_count_eq_three_of_alternating_projection
      same (by decide) twoCertificate (by decide)
  have countOne : other.toList.count 1 = 2 :=
    oneCertificate.right_count_eq_two same (by decide)
  have countTwo : other.toList.count 2 = 2 :=
    twoCertificate.right_count_eq_two same (by decide)
  have countThree : other.toList.count 3 = 1 :=
    (sameDeletionMarkedDigraph_count_eq_one_iff same 3).mp
      (by decide)
  have necessary :
      tripleOccurrenceNecessary other.toList = true := by
    have digest01 := markedPairDigestEq_true_of_same
      (same (fun value => value == 0 || value == 1)) 0 1
    have digest02 := markedPairDigestEq_true_of_same
      (same (fun value => value == 0 || value == 2)) 0 2
    have digest03 := markedPairDigestEq_true_of_same
      (same (fun value => value == 0 || value == 3)) 0 3
    have digest12 := markedPairDigestEq_true_of_same
      (same (fun value => value == 1 || value == 2)) 1 2
    have digest13 := markedPairDigestEq_true_of_same
      (same (fun value => value == 1 || value == 3)) 1 3
    have digest23 := markedPairDigestEq_true_of_same
      (same (fun value => value == 2 || value == 3)) 2 3
    have digest123 := markedFullDigestEqFour_true_of_same
      (same (fun value => value == 1 || value == 2 || value == 3))
    have digest023 := markedFullDigestEqFour_true_of_same
      (same (fun value => value == 0 || value == 2 || value == 3))
    have digest013 := markedFullDigestEqFour_true_of_same
      (same (fun value => value == 0 || value == 1 || value == 3))
    have digest012 := markedFullDigestEqFour_true_of_same
      (same (fun value => value == 0 || value == 1 || value == 2))
    have digestFull := markedFullDigestEqFour_true_of_same
      (same (fun _ => true))
    have digestFull' :
        markedFullDigestEqFour
          tripleOccurrenceSource.toList other.toList = true := by
      simpa only [filter_true] using digestFull
    simp [tripleOccurrenceNecessary, countZero, countOne, countTwo,
      countThree, digest01, digest02, digest03, digest12, digest13,
      digest23, digest123, digest023, digest013, digest012, digestFull']
  have supportSmall :
      ∀ letter, letter ∈ other.toList → letter < 4 := by
    intro letter member
    have sourceMember :=
      (sameDeletionMarkedDigraph_mem_iff same letter).mpr member
    change letter ∈ [0, 1, 2, 3, 0, 2, 0, 1] at sourceMember
    simp at sourceMember
    omega
  have sameFull := sameDeletionMarkedDigraph_full same
  have headZero : other.toList.head? = some 0 := by
    simpa [tripleOccurrenceSource, Word.toList] using sameFull.1.symm
  have lastOne : other.toList.getLast? = some 1 := by
    simpa [tripleOccurrenceSource, Word.toList] using sameFull.2.1.symm
  have otherPerm :
      other.toList.Perm [0, 0, 0, 1, 1, 2, 2, 3] := by
    rw [List.perm_iff_count]
    intro letter
    by_cases zero : letter = 0
    · subst letter
      simpa [countZero]
    · by_cases one : letter = 1
      · subst letter
        simpa [countOne]
      · by_cases two : letter = 2
        · subst letter
          simpa [countTwo]
        · by_cases three : letter = 3
          · subst letter
            simpa [countThree]
          · have sourceZero :
                tripleOccurrenceSource.toList.count letter = 0 := by
              apply List.count_eq_zero.mpr
              intro member
              change
                letter ∈ [0, 1, 2, 3, 0, 2, 0, 1] at member
              simp [zero, one, two, three] at member
            have otherZero :=
              (sameDeletionMarkedDigraph_count_eq_zero_iff
                same letter).mp sourceZero
            rw [otherZero]
            simp [zero, one, two, three, Ne.symm zero,
              Ne.symm one, Ne.symm two, Ne.symm three]
  have otherLength : other.toList.length = 8 := by
    simpa using otherPerm.length_eq
  rcases other with ⟨head, tail⟩
  cases tail with
  | nil =>
      simp [Word.toList] at otherLength
  | cons first tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at otherLength
      | cons second tail =>
          cases tail with
          | nil =>
              simp [Word.toList] at otherLength
          | cons third tail =>
              cases tail with
              | nil =>
                  simp [Word.toList] at otherLength
              | cons fourth tail =>
                  cases tail with
                  | nil =>
                      simp [Word.toList] at otherLength
                  | cons fifth tail =>
                      cases tail with
                      | nil =>
                          simp [Word.toList] at otherLength
                      | cons sixth tail =>
                          cases tail with
                          | nil =>
                              simp [Word.toList] at otherLength
                          | cons final rest =>
                              have restEmpty : rest = [] := by
                                apply List.eq_nil_of_length_eq_zero
                                simpa [Word.toList] using otherLength
                              subst rest
                              have headEq : head = 0 := by
                                simpa [Word.toList] using headZero
                              have finalEq : final = 1 := by
                                simpa [Word.toList] using lastOne
                              subst head
                              subst final
                              have firstSmall : first < 4 :=
                                supportSmall first (by simp [Word.toList])
                              have secondSmall : second < 4 :=
                                supportSmall second (by simp [Word.toList])
                              have thirdSmall : third < 4 :=
                                supportSmall third (by simp [Word.toList])
                              have fourthSmall : fourth < 4 :=
                                supportSmall fourth (by simp [Word.toList])
                              have fifthSmall : fifth < 4 :=
                                supportSmall fifth (by simp [Word.toList])
                              have sixthSmall : sixth < 4 :=
                                supportSmall sixth (by simp [Word.toList])
                              have candidateMember :
                                  [0, first, second, third, fourth, fifth,
                                      sixth, 1] ∈
                                    tripleOccurrencePrefixCandidates
                                      first second third fourth := by
                                simp only [tripleOccurrencePrefixCandidates,
                                  List.mem_flatMap, List.mem_map]
                                exact
                                  ⟨fifth, List.mem_range.mpr fifthSmall,
                                    sixth, List.mem_range.mpr sixthSmall,
                                    rfl⟩
                              have checked :=
                                (List.all_eq_true.mp
                                  (tripleOccurrencePrefixRigidityCheck_eq_true
                                    first second third fourth
                                    firstSmall secondSmall
                                    thirdSmall fourthSmall))
                                  [0, first, second, third, fourth, fifth,
                                    sixth, 1]
                                  candidateMember
                              have equalityChecked :
                                  decide
                                      ([0, first, second, third, fourth,
                                          fifth, sixth, 1] =
                                        tripleOccurrenceSource.toList) =
                                    true := by
                                have candidateNecessary :
                                    tripleOccurrenceNecessary
                                        [0, first, second, third, fourth,
                                          fifth, sixth, 1] =
                                      true := by
                                  simpa [Word.toList] using necessary
                                simpa [candidateNecessary] using checked
                              have reconstructed :
                                  [0, first, second, third, fourth, fifth,
                                      sixth, 1] =
                                    tripleOccurrenceSource.toList :=
                                of_decide_eq_true equalityChecked
                              apply Word.toList_injective
                              exact reconstructed

/-- The local 2-limited cover does not hold uniformly for anchor preimages.
The remaining A2One proof must handle variables that occur three times. -/
theorem not_anchorPreimageLocalTwoLimitedCover :
    ¬AnchorPreimageLocalTwoLimitedCover := by
  intro covered
  have sourceCovered :=
    covered 4 tripleOccurrenceSource
      tripleOccurrenceSource_uses
      tripleOccurrenceSubstitution
      tripleOccurrenceSource_maps
  exact tripleOccurrenceSource_not_twoLimited sourceCovered.1

private theorem all_letters_eq_head_of_usesAtMost_one'
    {word : Word Nat}
    (uses : WordUsesAtMost word 1) :
    ∀ letter, letter ∈ word.toList → letter = word.head := by
  rcases uses with ⟨variables, lengthBound, covered⟩
  cases variables with
  | nil =>
      have impossible :=
        covered word.head (by simp [Word.toList])
      simp at impossible
  | cons coverLetter rest =>
      have restEmpty : rest = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [List.length_cons] at lengthBound
        omega
      subst rest
      have headEq : word.head = coverLetter := by
        have := covered word.head (by simp [Word.toList])
        simpa using this
      intro letter member
      have := covered letter member
      simpa [headEq] using this

private theorem flatMap_length_of_all_eq'
    (letters : List Nat) (images : Nat → List Nat) (letter : Nat)
    (allEqual : ∀ value, value ∈ letters → value = letter) :
    (letters.flatMap images).length =
      letters.length * (images letter).length := by
  induction letters with
  | nil => simp
  | cons first rest ih =>
      have firstEq : first = letter :=
        allEqual first (by simp)
      have restEqual :
          ∀ value, value ∈ rest → value = letter := by
        intro value member
        exact allEqual value (by simp [member])
      subst first
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [ih restEqual]
      rw [Nat.succ_mul]
      omega

/-- The singleton-pivot reconstruction is valid for a one-variable source.
This is the largest currently proved uniform fragment of the candidate. -/
theorem anchorFactorizationReconstruction_bound_one
    (word : Word Nat)
    (uses : WordUsesAtMost word 1)
    (substitution : Nat → Word Nat)
    (mapped : word.bind substitution = anchor 3) :
    ∃ pivot, SingletonPivotFactorization pivot word.toList := by
  have sourceLengthBound :
      word.toList.length ≤ 3 :=
    preimage_word_length_le_three_mul uses mapped
  have sourceLengthPositive : 1 ≤ word.toList.length := by
    cases word
    simp [Word.toList]
  have allEqual :=
    all_letters_eq_head_of_usesAtMost_one' uses
  have bindLength :
      (word.bind substitution).toList.length =
        word.toList.length *
          (substitution word.head).toList.length := by
    rw [Word.toList_bind]
    exact flatMap_length_of_all_eq' word.toList
      (fun letter => (substitution letter).toList)
      word.head allEqual
  rw [mapped, anchor_length] at bindLength
  have sourceLengthOne : word.toList.length = 1 := by
    have cases :
        word.toList.length = 1 ∨
          word.toList.length = 2 ∨
            word.toList.length = 3 := by
      omega
    rcases cases with one | two | three
    · exact one
    · rw [two] at bindLength
      omega
    · rw [three] at bindLength
      omega
  cases word with
  | mk head tail =>
      simp only [Word.toList, List.length_cons] at sourceLengthOne
      have tailEmpty : tail = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      subst tail
      exact ⟨head, [], [], rfl, by simp, by simp, by simp, by simp⟩

/-- Bound one satisfies the corrected deletion-rigidity boundary. -/
theorem anchorPreimageDeletionRigidity_bound_one
    (word : Word Nat)
    (uses : WordUsesAtMost word 1)
    (substitution : Nat → Word Nat)
    (mapped : word.bind substitution = anchor 3) :
    DeletionGraphRigidWord word := by
  obtain ⟨pivot, shape⟩ :=
    anchorFactorizationReconstruction_bound_one
      word uses substitution mapped
  exact deletionGraphRigidWord_of_singletonPivot shape

end SemigroupBasis.Nonfinite.A2One
