import SemigroupBasis.Nonfinite.A2One.FactorizationReconstruction

namespace SemigroupBasis.Nonfinite.A2One

open SemigroupBasis

private theorem flatMap_length_eq_length_of_image_length_one
    (letters : List Nat) (images : Nat → List Nat)
    (imageLengthOne :
      ∀ letter, letter ∈ letters →
        (images letter).length = 1) :
    (letters.flatMap images).length = letters.length := by
  induction letters with
  | nil => simp
  | cons first rest ih =>
      have firstLength : (images first).length = 1 :=
        imageLengthOne first (by simp)
      have restLength :
          ∀ letter, letter ∈ rest →
            (images letter).length = 1 := by
        intro letter member
        exact imageLengthOne letter (by simp [member])
      simp only [List.flatMap_cons, List.length_append,
        List.length_cons, firstLength]
      rw [ih restLength]
      omega

private theorem adjacentPairsList_append_left
    {left right : List Nat} {edge : Nat × Nat}
    (member : edge ∈ adjacentPairsList left) :
    edge ∈ adjacentPairsList (left ++ right) := by
  cases left with
  | nil => simp [adjacentPairsList] at member
  | cons first rest =>
      cases right with
      | nil => simpa using member
      | cons next tail =>
          change
            edge ∈ Word.adjacentPairsFrom first rest at member
          change
            edge ∈
              Word.adjacentPairsFrom first
                (rest ++ next :: tail)
          rw [Word.adjacentPairsFrom_append]
          simp [member]

private theorem adjacentPairsList_append_right
    {left right : List Nat} {edge : Nat × Nat}
    (member : edge ∈ adjacentPairsList right) :
    edge ∈ adjacentPairsList (left ++ right) := by
  cases left with
  | nil => simpa using member
  | cons first rest =>
      cases right with
      | nil => simp [adjacentPairsList] at member
      | cons next tail =>
          change
            edge ∈ Word.adjacentPairsFrom next tail at member
          change
            edge ∈
              Word.adjacentPairsFrom first
                (rest ++ next :: tail)
          rw [Word.adjacentPairsFrom_append]
          simp [member]

private theorem adjacentPairsList_flatMap_of_mem
    (letters : List Nat) (images : Nat → List Nat)
    {letter : Nat} (letterMember : letter ∈ letters)
    {edge : Nat × Nat}
    (edgeMember : edge ∈ adjacentPairsList (images letter)) :
    edge ∈ adjacentPairsList (letters.flatMap images) := by
  induction letters with
  | nil => simp at letterMember
  | cons first rest ih =>
      simp only [List.mem_cons] at letterMember
      rw [List.flatMap_cons]
      rcases letterMember with equality | restMember
      · subst first
        exact adjacentPairsList_append_left edgeMember
      · exact adjacentPairsList_append_right
          (ih restMember)

private theorem exists_long_image_in_separator_middle
    {bound : Nat} {word : Word Nat}
    (uses : WordUsesAtMost word bound)
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    {owner : Nat}
    (ownerCount : word.toList.count owner = 2)
    (separatorMember :
      3 * bound + 2 ∈ (substitution owner).toList) :
    ∃ before middle after controller,
      word.toList =
          before ++ owner :: (middle ++ owner :: after) ∧
        owner ∉ before ∧ owner ∉ middle ∧ owner ∉ after ∧
        middle.flatMap
            (fun letter => (substitution letter).toList) =
          (List.range (3 * bound + 2)).reverse ∧
        controller ∈ middle ∧
        2 ≤ (substitution controller).toList.length := by
  obtain
    ⟨before, middle, after, sourceSplit,
      ownerNotBefore, ownerNotMiddle, ownerNotAfter,
      _beforeMapped, middleMapped, _afterMapped⟩ :=
    preimage_two_occurrence_separator_owner_mapped_blocks
      mapped ownerCount separatorMember
  have sourceLengthBound :
      word.toList.length ≤ 3 * bound :=
    preimage_word_length_le_three_mul uses mapped
  have middleLengthBound :
      middle.length + 2 ≤ 3 * bound := by
    rw [sourceSplit] at sourceLengthBound
    simp only [List.length_append, List.length_cons] at sourceLengthBound
    omega
  have longImage :
      ∃ controller,
        controller ∈ middle ∧
          2 ≤ (substitution controller).toList.length := by
    apply Classical.byContradiction
    intro noLongImage
    have imageLengthOne :
        ∀ controller, controller ∈ middle →
          (substitution controller).toList.length = 1 := by
      intro controller controllerMember
      have notLong :
          ¬2 ≤ (substitution controller).toList.length := by
        intro controllerImageLong
        exact
          noLongImage
            ⟨controller, controllerMember, controllerImageLong⟩
      have upper :
          (substitution controller).toList.length ≤ 1 := by
        omega
      have positive :
          1 ≤ (substitution controller).toList.length := by
        cases substitution controller
        simp [Word.toList]
      omega
    have sameLength :
        (middle.flatMap
            (fun letter => (substitution letter).toList)).length =
          middle.length :=
      flatMap_length_eq_length_of_image_length_one
        middle (fun letter => (substitution letter).toList)
        imageLengthOne
    rw [middleMapped] at sameLength
    simp only [List.length_reverse, List.length_range] at sameLength
    omega
  obtain ⟨controller, controllerMember, controllerImageLong⟩ :=
    longImage
  exact
    ⟨before, middle, after, controller, sourceSplit,
      ownerNotBefore, ownerNotMiddle, ownerNotAfter,
      middleMapped, controllerMember, controllerImageLong⟩

private theorem separator_middle_long_image_owner_count_eq_one
    {bound : Nat} {word : Word Nat}
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    {middle : List Nat}
    (middleMapped :
      middle.flatMap
          (fun letter => (substitution letter).toList) =
        (List.range (3 * bound + 2)).reverse)
    {controller : Nat}
    (controllerMember : controller ∈ middle)
    (controllerImageLong :
      2 ≤ (substitution controller).toList.length)
    (controllerWordMember : controller ∈ word.toList) :
    word.toList.count controller = 1 := by
  have controllerPositive :
      1 ≤ word.toList.count controller :=
    List.count_pos_iff.mpr controllerWordMember
  have controllerUpper :
      word.toList.count controller ≤ 3 :=
    preimage_threeLimitedList mapped controller
  by_cases controllerOne :
      word.toList.count controller = 1
  · exact controllerOne
  have controllerCases :
      word.toList.count controller = 2 ∨
        word.toList.count controller = 3 := by
    omega
  rcases controllerCases with controllerTwo | controllerThree
  · cases imageEq : substitution controller with
    | mk head tail =>
        cases tail with
        | nil =>
            simp [imageEq, Word.toList] at controllerImageLong
        | cons next rest =>
            have imageEdge :
                (head, next) ∈
                  (substitution controller).adjacentPairs := by
              simp [imageEq, Word.adjacentPairs,
                Word.adjacentPairsFrom]
            have imageListEdge :
                (head, next) ∈
                  adjacentPairsList
                    (substitution controller).toList := by
              simpa [imageEq, Word.toList, adjacentPairsList,
                Word.adjacentPairsFrom] using imageEdge
            have middleEdge :
                (head, next) ∈
                  adjacentPairsList
                    (middle.flatMap
                      (fun letter =>
                        (substitution letter).toList)) :=
              adjacentPairsList_flatMap_of_mem
                middle
                (fun letter => (substitution letter).toList)
                controllerMember imageListEdge
            have reverseEdge :
                (head, next) ∈
                  adjacentPairsList
                    (List.range (3 * bound + 2)).reverse := by
              rwa [middleMapped] at middleEdge
            have descending :
                head = next + 1 :=
              adjacentPairsList_reverse_range_descending reverseEdge
            have forward :=
              (preimage_two_occurrence_image_edge_forward
                mapped controllerTwo imageEdge).2
            omega
  · have singletonImage :=
      preimage_three_occurrence_image_singleton
        mapped controllerThree
    have singletonLength :
        (substitution controller).toList.length = 1 := by
      rw [singletonImage]
      simp [Word.toList]
    omega

private theorem filter_pair_eq_nil
    {letters : List Nat} {first second : Nat}
    (firstAbsent : first ∉ letters)
    (secondAbsent : second ∉ letters) :
    letters.filter
        (fun value => value == first || value == second) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro value valueMember
  simp only [Bool.or_eq_true, beq_iff_eq]
  rintro (equality | equality)
  · subst value
    exact firstAbsent valueMember
  · subst value
    exact secondAbsent valueMember

private theorem filter_pair_eq_singleton
    {letters : List Nat} {first second : Nat}
    (different : first ≠ second)
    (firstAbsent : first ∉ letters)
    (secondCountOne : letters.count second = 1) :
    letters.filter
        (fun value => value == first || value == second) = [second] := by
  rw [show
    letters.filter
        (fun value => value == first || value == second) =
      letters.filter (fun value => value == second) by
        apply List.filter_congr
        intro value valueMember
        have valueNeFirst : value ≠ first := by
          intro equality
          subst value
          exact firstAbsent valueMember
        simp [valueNeFirst]]
  induction letters with
  | nil => simp at secondCountOne
  | cons head tail ih =>
      by_cases equality : head = second
      · subst head
        have tailCountZero : tail.count second = 0 := by
          simp only [List.count_cons_self] at secondCountOne
          omega
        have tailFilter :
            tail.filter (fun value => value == second) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro value valueMember
          simp only [beq_iff_eq]
          intro valueEq
          subst value
          exact (List.count_eq_zero.mp tailCountZero) valueMember
        simp [tailFilter]
      · have tailCountOne : tail.count second = 1 := by
          simpa [equality] using secondCountOne
        have tailFirstAbsent : first ∉ tail := by
          intro member
          exact firstAbsent (by simp [member])
        simp [equality, ih tailFirstAbsent tailCountOne]

/-- A twice-occurring source variable that owns the distinguished anchor
separator has a local multiplicity certificate.  The variable bound forces
one image inside the intervening reverse block to contain a reverse edge;
that image can occur only once and separates the two owner occurrences. -/
theorem preimage_separator_owner_localTwoLimitedCertificate
    {bound : Nat} {word : Word Nat}
    (uses : WordUsesAtMost word bound)
    {substitution : Nat → Word Nat}
    (mapped : word.bind substitution = anchor (3 * bound))
    {owner : Nat}
    (ownerCount : word.toList.count owner = 2)
    (separatorMember :
      3 * bound + 2 ∈ (substitution owner).toList) :
    LocalTwoLimitedCertificate word owner := by
  obtain
    ⟨before, middle, after, controller, sourceSplit,
      ownerNotBefore, ownerNotMiddle, ownerNotAfter,
      middleMapped, controllerMember, controllerImageLong⟩ :=
    exists_long_image_in_separator_middle
      uses mapped ownerCount separatorMember
  have controllerWordMember : controller ∈ word.toList := by
    rw [sourceSplit]
    simp [controllerMember]
  have controllerCountOne :
      word.toList.count controller = 1 :=
    separator_middle_long_image_owner_count_eq_one
      mapped middleMapped controllerMember controllerImageLong
      controllerWordMember
  have ownerNeController : owner ≠ controller := by
    intro equality
    subst controller
    exact ownerNotMiddle controllerMember
  have splitCounts := congrArg (List.count controller) sourceSplit
  have middlePositive :
      1 ≤ middle.count controller :=
    List.count_pos_iff.mpr controllerMember
  have beforeCountZero : before.count controller = 0 := by
    rw [controllerCountOne] at splitCounts
    simp [ownerNeController, Ne.symm ownerNeController] at splitCounts
    omega
  have middleCountOne : middle.count controller = 1 := by
    rw [controllerCountOne] at splitCounts
    simp [ownerNeController, Ne.symm ownerNeController] at splitCounts
    omega
  have afterCountZero : after.count controller = 0 := by
    rw [controllerCountOne] at splitCounts
    simp [ownerNeController, Ne.symm ownerNeController] at splitCounts
    omega
  have beforeFilter :
      before.filter
          (fun value => value == owner || value == controller) = [] :=
    filter_pair_eq_nil ownerNotBefore
      (List.count_eq_zero.mp beforeCountZero)
  have middleFilter :
      middle.filter
          (fun value => value == owner || value == controller) =
        [controller] :=
    filter_pair_eq_singleton ownerNeController ownerNotMiddle
      middleCountOne
  have afterFilter :
      after.filter
          (fun value => value == owner || value == controller) = [] :=
    filter_pair_eq_nil ownerNotAfter
      (List.count_eq_zero.mp afterCountZero)
  apply LocalTwoLimitedCertificate.singletonSeparator
      owner controller ownerNeController controllerCountOne
  rw [sourceSplit, List.filter_append, List.filter_cons,
    List.filter_append, List.filter_cons]
  simp [beforeFilter, middleFilter, afterFilter,
    ownerNeController, adjacentPairsList,
    Word.adjacentPairsFrom]

end SemigroupBasis.Nonfinite.A2One
