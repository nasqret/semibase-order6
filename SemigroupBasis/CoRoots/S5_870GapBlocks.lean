import SemigroupBasis.CoRoots.S5_870Signature

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_870

open SemigroupBasis

/-! ## Executable first-occurrence gap decomposition -/

/-- One first-occurrence marker together with the later occurrences appearing
before the next new marker. On a two-limited word, `seconds` contains exactly
the second occurrences assigned to this gap. -/
structure FirstOccurrenceGapBlock where
  marker : Nat
  seconds : List Nat
deriving DecidableEq, Repr

instance countLeTwoDecidable (letters : List Nat) :
    Decidable (∀ letter, letters.count letter <= 2) :=
  if checked :
      letters.all (fun letter => decide (letters.count letter <= 2)) then
    isTrue (by
      intro letter
      by_cases member : letter ∈ letters
      · exact of_decide_eq_true
          ((List.all_eq_true.mp checked) letter member)
      · have zero : letters.count letter = 0 :=
          List.count_eq_zero.mpr member
        omega)
  else
    isFalse (by
      intro bounded
      apply checked
      apply List.all_eq_true.mpr
      intro letter _
      exact decide_eq_true (bounded letter))

/-- Flatten a first-occurrence gap decomposition. -/
def renderGapBlocks : List FirstOccurrenceGapBlock -> List Nat
  | [] => []
  | block :: rest =>
      block.marker :: (block.seconds ++ renderGapBlocks rest)

def gapBlockMarkers (blocks : List FirstOccurrenceGapBlock) : List Nat :=
  blocks.map FirstOccurrenceGapBlock.marker

def gapBlockSeconds (blocks : List FirstOccurrenceGapBlock) : List Nat :=
  blocks.flatMap FirstOccurrenceGapBlock.seconds

/-- The maximal initial segment consisting only of already seen letters. -/
def takeSeen (seen : List Nat) : List Nat -> List Nat
  | [] => []
  | letter :: rest =>
      if letter ∈ seen then letter :: takeSeen seen rest else []

/-- Drop the maximal initial segment consisting only of already seen letters. -/
def dropSeen (seen : List Nat) : List Nat -> List Nat
  | [] => []
  | letter :: rest =>
      if letter ∈ seen then dropSeen seen rest else letter :: rest

theorem takeSeen_append_dropSeen (seen letters : List Nat) :
    takeSeen seen letters ++ dropSeen seen letters = letters := by
  induction letters with
  | nil => rfl
  | cons letter rest induction =>
      by_cases member : letter ∈ seen
      · simp [takeSeen, dropSeen, member, induction]
      · simp [takeSeen, dropSeen, member]

theorem mem_takeSeen {seen letters : List Nat} {letter : Nat}
    (member : letter ∈ takeSeen seen letters) :
    letter ∈ seen := by
  induction letters with
  | nil => simp [takeSeen] at member
  | cons head tail induction =>
      by_cases headSeen : head ∈ seen
      · simp only [takeSeen, headSeen, if_pos, List.mem_cons] at member
        rcases member with equal | inTail
        · simpa [equal] using headSeen
        · exact induction inTail
      · simp [takeSeen, headSeen] at member

theorem dropSeen_length_le (seen letters : List Nat) :
    (dropSeen seen letters).length <= letters.length := by
  induction letters with
  | nil => simp [dropSeen]
  | cons letter rest induction =>
      by_cases member : letter ∈ seen
      · simp [dropSeen, member]
        omega
      · simp [dropSeen, member]

theorem head_dropSeen_not_mem
    (seen letters : List Nat) (head : Nat) (tail : List Nat)
    (shape : dropSeen seen letters = head :: tail) :
    head ∉ seen := by
  induction letters with
  | nil => simp [dropSeen] at shape
  | cons letter rest induction =>
      by_cases member : letter ∈ seen
      · simp [dropSeen, member] at shape
        exact induction shape
      · simp [dropSeen, member] at shape
        rcases shape with ⟨headEq, _⟩
        simpa [headEq] using member

@[simp]
theorem dropSeen_nil (letters : List Nat) :
    dropSeen [] letters = letters := by
  induction letters with
  | nil => rfl
  | cons letter rest induction =>
      simp [dropSeen, induction]

/-- Parse a list from left to right. Every fresh marker starts a block; the
maximal following run of already seen letters is that marker's gap block. -/
def gapBlocksAux (seen : List Nat) :
    List Nat -> List FirstOccurrenceGapBlock
  | [] => []
  | marker :: rest =>
      let nextSeen := marker :: seen
      let seconds := takeSeen nextSeen rest
      let remaining := dropSeen nextSeen rest
      { marker := marker, seconds := seconds } ::
        gapBlocksAux nextSeen remaining
termination_by letters => letters.length
decreasing_by
  exact Nat.lt_succ_of_le (dropSeen_length_le _ _)

private def gapBlocksFuel :
    Nat -> List Nat -> List Nat -> List FirstOccurrenceGapBlock
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | fuel + 1, seen, marker :: rest =>
      let nextSeen := marker :: seen
      let seconds := takeSeen nextSeen rest
      let remaining := dropSeen nextSeen rest
      { marker := marker, seconds := seconds } ::
        gapBlocksFuel fuel nextSeen remaining

private theorem gapBlocksFuel_eq_gapBlocksAux :
    ∀ (fuel : Nat) (seen letters : List Nat),
      letters.length <= fuel ->
        gapBlocksFuel fuel seen letters = gapBlocksAux seen letters
  | 0, _, [], _ => by simp [gapBlocksFuel, gapBlocksAux]
  | 0, _, _ :: _, enough => by simp at enough
  | _ + 1, _, [], _ => by simp [gapBlocksFuel, gapBlocksAux]
  | fuel + 1, seen, marker :: rest, enough => by
      simp only [gapBlocksFuel, gapBlocksAux]
      have restBound : rest.length <= fuel := by
        simpa using enough
      have tails := gapBlocksFuel_eq_gapBlocksAux
        fuel (marker :: seen) (dropSeen (marker :: seen) rest) <|
          Nat.le_trans
            (dropSeen_length_le (marker :: seen) rest) restBound
      exact congrArg
        (fun tail : List FirstOccurrenceGapBlock =>
          { marker := marker,
            seconds := takeSeen (marker :: seen) rest } :: tail)
        tails

def gapBlocksList (letters : List Nat) :
    List FirstOccurrenceGapBlock :=
  gapBlocksFuel letters.length [] letters

private theorem gapBlocksList_eq_gapBlocksAux (letters : List Nat) :
    gapBlocksList letters = gapBlocksAux [] letters := by
  exact gapBlocksFuel_eq_gapBlocksAux
    letters.length [] letters (Nat.le_refl _)

theorem render_gapBlocksAux (seen : List Nat) :
    ∀ letters : List Nat,
      renderGapBlocks (gapBlocksAux seen letters) = letters
  | [] => by simp [gapBlocksAux, renderGapBlocks]
  | marker :: rest => by
      rw [gapBlocksAux, renderGapBlocks,
        render_gapBlocksAux (marker :: seen)
          (dropSeen (marker :: seen) rest)]
      simpa using congrArg (List.cons marker)
        (takeSeen_append_dropSeen (marker :: seen) rest)
termination_by letters => letters.length
decreasing_by
  exact Nat.lt_succ_of_le (dropSeen_length_le _ _)

theorem render_gapBlocksList (letters : List Nat) :
    renderGapBlocks (gapBlocksList letters) = letters := by
  rw [gapBlocksList_eq_gapBlocksAux]
  exact render_gapBlocksAux [] letters

/-- Structural invariant of the parser. `seen` is the reverse list of markers
that precede the displayed blocks. -/
inductive GapBlocksWellFormed :
    List Nat -> List FirstOccurrenceGapBlock -> Prop
  | nil (seen : List Nat) : GapBlocksWellFormed seen []
  | cons (seen : List Nat) (block : FirstOccurrenceGapBlock)
      (rest : List FirstOccurrenceGapBlock)
      (markerFresh : block.marker ∉ seen)
      (secondsSeen :
        ∀ letter, letter ∈ block.seconds ->
          letter ∈ block.marker :: seen)
      (tail : GapBlocksWellFormed (block.marker :: seen) rest) :
      GapBlocksWellFormed seen (block :: rest)

theorem gapBlocksAux_dropSeen_wellFormed :
    ∀ (seen letters : List Nat),
      GapBlocksWellFormed seen
        (gapBlocksAux seen (dropSeen seen letters))
  | seen, [] => by
      simp [dropSeen, gapBlocksAux]
      exact GapBlocksWellFormed.nil seen
  | seen, letter :: rest => by
      by_cases member : letter ∈ seen
      · simpa [dropSeen, member] using
          gapBlocksAux_dropSeen_wellFormed seen rest
      · rw [dropSeen]
        simp only [member, ↓reduceIte, gapBlocksAux]
        exact GapBlocksWellFormed.cons seen
          { marker := letter,
            seconds := takeSeen (letter :: seen) rest }
          (gapBlocksAux (letter :: seen)
            (dropSeen (letter :: seen) rest))
          member
          (by
            intro tested testedIn
            exact mem_takeSeen testedIn)
          (gapBlocksAux_dropSeen_wellFormed
            (letter :: seen) rest)

theorem gapBlocksList_wellFormed (letters : List Nat) :
    GapBlocksWellFormed [] (gapBlocksList letters) := by
  rw [gapBlocksList_eq_gapBlocksAux]
  simpa using
    gapBlocksAux_dropSeen_wellFormed [] letters

theorem gapBlockMarkers_gapBlocksAux_dropSeen :
    ∀ (seen letters : List Nat),
      gapBlockMarkers
          (gapBlocksAux seen (dropSeen seen letters)) =
        firstOccurrenceSequenceAux seen letters
  | seen, [] => by simp [dropSeen, gapBlocksAux, gapBlockMarkers,
      firstOccurrenceSequenceAux]
  | seen, letter :: rest => by
      by_cases member : letter ∈ seen
      · simpa [dropSeen, firstOccurrenceSequenceAux, member] using
          gapBlockMarkers_gapBlocksAux_dropSeen seen rest
      · simp only [dropSeen, member, ↓reduceIte, gapBlocksAux,
          gapBlockMarkers, List.map_cons,
          FirstOccurrenceGapBlock.marker,
          firstOccurrenceSequenceAux]
        exact congrArg (List.cons letter)
          (gapBlockMarkers_gapBlocksAux_dropSeen
            (letter :: seen) rest)

theorem gapBlockMarkers_gapBlocksList (letters : List Nat) :
    gapBlockMarkers (gapBlocksList letters) =
      firstOccurrenceSequenceList letters := by
  rw [gapBlocksList_eq_gapBlocksAux]
  simpa [firstOccurrenceSequenceList] using
    gapBlockMarkers_gapBlocksAux_dropSeen [] letters

/-! ## Structural consequences -/

theorem GapBlocksWellFormed.markersAvoidSeen
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed seen blocks) :
    ∀ letter, letter ∈ seen ->
      letter ∉ gapBlockMarkers blocks := by
  induction formed with
  | nil => simp [gapBlockMarkers]
  | cons seen block rest markerFresh secondsSeen tail induction =>
      intro letter letterSeen
      simp only [gapBlockMarkers, List.map_cons,
        FirstOccurrenceGapBlock.marker, List.mem_cons]
      intro markerMember
      rcases markerMember with equal | later
      · subst letter
        exact markerFresh letterSeen
      · exact induction letter
          (List.Mem.tail block.marker letterSeen) later

theorem GapBlocksWellFormed.markersNodup
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed seen blocks) :
    (gapBlockMarkers blocks).Nodup := by
  induction formed with
  | nil => simp [gapBlockMarkers]
  | cons seen block rest markerFresh secondsSeen tail induction =>
      simp only [gapBlockMarkers, List.map_cons,
        FirstOccurrenceGapBlock.marker, List.nodup_cons]
      constructor
      · exact tail.markersAvoidSeen block.marker
          (List.Mem.head seen)
      · exact induction

theorem GapBlocksWellFormed.secondsInSeenOrMarkers
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed seen blocks) :
    ∀ letter, letter ∈ gapBlockSeconds blocks ->
      letter ∈ seen ∨ letter ∈ gapBlockMarkers blocks := by
  induction formed with
  | nil => simp [gapBlockSeconds]
  | cons seen block rest markerFresh secondsSeen tail induction =>
      intro letter member
      simp only [gapBlockSeconds, List.flatMap_cons,
        List.mem_append] at member
      rcases member with current | later
      · have known := secondsSeen letter current
        rcases List.mem_cons.mp known with atMarker | inSeen
        · exact Or.inr <| by
            simp [gapBlockMarkers, atMarker]
        · exact Or.inl inSeen
      · rcases induction letter later with inNextSeen | inRest
        · rcases List.mem_cons.mp inNextSeen with atMarker | inSeen
          · exact Or.inr <| by
              simp [gapBlockMarkers, atMarker]
          · exact Or.inl inSeen
        · exact Or.inr <| by
            change letter ∈ block.marker :: gapBlockMarkers rest
            exact List.Mem.tail block.marker inRest

theorem count_renderGapBlocks
    (tested : Nat) (blocks : List FirstOccurrenceGapBlock) :
    (renderGapBlocks blocks).count tested =
      (gapBlockMarkers blocks).count tested +
        (gapBlockSeconds blocks).count tested := by
  induction blocks with
  | nil => simp [renderGapBlocks, gapBlockMarkers, gapBlockSeconds]
  | cons block rest induction =>
      simp only [renderGapBlocks, gapBlockMarkers, gapBlockSeconds,
        List.map_cons, List.flatMap_cons, List.count_cons,
        List.count_append, FirstOccurrenceGapBlock.marker,
        FirstOccurrenceGapBlock.seconds, induction]
      omega

private theorem nodup_of_count_le_one
    {letters : List Nat}
    (bounded : ∀ letter, letters.count letter <= 1) :
    letters.Nodup := by
  rw [List.nodup_iff_count]
  exact bounded

theorem gapBlockSeconds_nodup_of_limited
    {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed [] blocks)
    (limited : ∀ letter,
      (renderGapBlocks blocks).count letter <= 2) :
    (gapBlockSeconds blocks).Nodup := by
  have markersNodup := formed.markersNodup
  apply nodup_of_count_le_one
  intro letter
  have bound := limited letter
  rw [count_renderGapBlocks] at bound
  by_cases member : letter ∈ gapBlockSeconds blocks
  · have markerMember : letter ∈ gapBlockMarkers blocks :=
      (formed.secondsInSeenOrMarkers letter member).resolve_left
        (by simp)
    have markerCount :
        (gapBlockMarkers blocks).count letter = 1 := by
      rw [markersNodup.count]
      simp [markerMember]
    rw [markerCount] at bound
    omega
  · rw [List.count_eq_zero.mpr member]
    omega

theorem gapBlocksList_seconds_nodup
    (letters : List Nat)
    (limited : ∀ letter, letters.count letter <= 2) :
    (gapBlockSeconds (gapBlocksList letters)).Nodup := by
  apply gapBlockSeconds_nodup_of_limited
    (gapBlocksList_wellFormed letters)
  intro letter
  simpa [render_gapBlocksList] using limited letter

/-! ## Exact interpretation of second-occurrence gaps -/

/-- Read the gap number assigned to `selected` from parsed blocks. -/
def blockSecondGapAux
    (selected : Nat) (seen : List Nat) :
    List FirstOccurrenceGapBlock -> Option Nat
  | [] => none
  | block :: rest =>
      if selected ∈ block.seconds then
        some (block.marker :: seen).length
      else
        blockSecondGapAux selected (block.marker :: seen) rest

private theorem secondOccurrenceGapAux_knownBlock
    (selected : Nat) (firsts block suffix : List Nat)
    (known : ∀ letter, letter ∈ block -> letter ∈ firsts) :
    secondOccurrenceGapAux selected
        (decide (selected ∈ firsts)) firsts (block ++ suffix) =
      if selected ∈ block then some firsts.length
      else secondOccurrenceGapAux selected
        (decide (selected ∈ firsts)) firsts suffix := by
  induction block with
  | nil => simp
  | cons head tail induction =>
      have headKnown : head ∈ firsts :=
        known head (List.Mem.head tail)
      have tailKnown : ∀ letter, letter ∈ tail -> letter ∈ firsts := by
        intro letter member
        exact known letter (List.Mem.tail head member)
      by_cases equal : head = selected
      · subst head
        simp [secondOccurrenceGapAux, headKnown]
      · have selectedNe : selected ≠ head := Ne.symm equal
        simp [secondOccurrenceGapAux, headKnown, equal, selectedNe,
          induction tailKnown]

theorem secondOccurrenceGapAux_renderGapBlocks
    (selected : Nat) {seen : List Nat}
    {blocks : List FirstOccurrenceGapBlock}
    (formed : GapBlocksWellFormed seen blocks) :
    secondOccurrenceGapAux selected
        (decide (selected ∈ seen)) seen (renderGapBlocks blocks) =
      blockSecondGapAux selected seen blocks := by
  induction formed with
  | nil => simp [renderGapBlocks, blockSecondGapAux,
      secondOccurrenceGapAux]
  | cons seen block rest markerFresh secondsSeen tail induction =>
      have afterMarker :
          secondOccurrenceGapAux selected
              (decide (selected ∈ seen)) seen
              (block.marker ::
                (block.seconds ++ renderGapBlocks rest)) =
            secondOccurrenceGapAux selected
              (decide (selected ∈ block.marker :: seen))
              (block.marker :: seen)
              (block.seconds ++ renderGapBlocks rest) := by
        by_cases equal : block.marker = selected
        · subst selected
          simp [secondOccurrenceGapAux, markerFresh]
        · have selectedNe : selected ≠ block.marker := Ne.symm equal
          simp [secondOccurrenceGapAux, markerFresh, equal, selectedNe]
      rw [renderGapBlocks, afterMarker]
      rw [secondOccurrenceGapAux_knownBlock selected
        (block.marker :: seen) block.seconds
        (renderGapBlocks rest) secondsSeen]
      by_cases member : selected ∈ block.seconds
      · simp only [blockSecondGapAux, member, ↓reduceIte]
      · simpa only [blockSecondGapAux, member, ↓reduceIte] using
          induction

theorem secondOccurrenceGapList_eq_blockSecondGapAux
    (letters : List Nat) (selected : Nat) :
    secondOccurrenceGapList letters selected =
      blockSecondGapAux selected [] (gapBlocksList letters) := by
  calc
    secondOccurrenceGapList letters selected =
        secondOccurrenceGapList
          (renderGapBlocks (gapBlocksList letters)) selected := by
      rw [render_gapBlocksList]
    _ = blockSecondGapAux selected [] (gapBlocksList letters) := by
      unfold secondOccurrenceGapList
      simpa using secondOccurrenceGapAux_renderGapBlocks selected
        (gapBlocksList_wellFormed letters)

theorem blockSecondGapAux_gt
    (selected : Nat) :
    ∀ {seen : List Nat}
      {blocks : List FirstOccurrenceGapBlock} {gap : Nat},
      blockSecondGapAux selected seen blocks = some gap ->
        seen.length < gap
  | seen, [], gap, equality => by
      simp [blockSecondGapAux] at equality
  | seen, block :: rest, gap, equality => by
      by_cases member : selected ∈ block.seconds
      · simp [blockSecondGapAux, member] at equality
        omega
      · have later := blockSecondGapAux_gt selected
          (seen := block.marker :: seen) (blocks := rest)
          (gap := gap) (by
            simpa [blockSecondGapAux, member] using equality)
        have step : seen.length < (block.marker :: seen).length := by
          simp
        exact Nat.lt_trans step later

theorem blockSecondGapAux_eq_current_iff
    (selected : Nat) (seen : List Nat)
    (block : FirstOccurrenceGapBlock)
    (rest : List FirstOccurrenceGapBlock) :
    blockSecondGapAux selected seen (block :: rest) =
        some (block.marker :: seen).length ↔
      selected ∈ block.seconds := by
  by_cases member : selected ∈ block.seconds
  · simp [blockSecondGapAux, member]
  · constructor
    · intro equality
      have later := blockSecondGapAux_gt selected
        (seen := block.marker :: seen) (blocks := rest)
        (gap := (block.marker :: seen).length) (by
          simpa [blockSecondGapAux, member] using equality)
      omega
    · intro inBlock
      exact False.elim (member inBlock)

theorem blockSecondGapAux_eq_none_of_not_mem_seconds
    (selected : Nat) :
    ∀ (seen : List Nat) (blocks : List FirstOccurrenceGapBlock),
      selected ∉ gapBlockSeconds blocks ->
        blockSecondGapAux selected seen blocks = none
  | seen, [], _ => rfl
  | seen, block :: rest, absent => by
      have currentAbsent : selected ∉ block.seconds := by
        intro member
        apply absent
        change selected ∈ block.seconds ++ gapBlockSeconds rest
        exact List.mem_append_left _ member
      have restAbsent : selected ∉ gapBlockSeconds rest := by
        intro member
        apply absent
        change selected ∈ block.seconds ++ gapBlockSeconds rest
        exact List.mem_append_right _ member
      simp [blockSecondGapAux, currentAbsent,
        blockSecondGapAux_eq_none_of_not_mem_seconds
          selected (block.marker :: seen) rest restAbsent]

/-! ## Equal signatures give corresponding block permutations -/

private theorem pointwise_of_map_eq
    {alpha beta : Type} (f g : alpha -> beta) :
    ∀ {keys : List alpha},
      keys.map f = keys.map g ->
        ∀ key, key ∈ keys -> f key = g key
  | [], equality, key, member => by simp at member
  | head :: tail, equality, key, member => by
      simp only [List.map_cons] at equality
      injection equality with headEq tailEq
      rcases List.mem_cons.mp member with atHead | inTail
      · simpa [atHead] using headEq
      · exact pointwise_of_map_eq f g tailEq key inTail

inductive CorrespondingGapBlocks :
    List FirstOccurrenceGapBlock ->
      List FirstOccurrenceGapBlock -> Prop
  | nil : CorrespondingGapBlocks [] []
  | cons {leftBlock rightBlock : FirstOccurrenceGapBlock}
      {leftRest rightRest : List FirstOccurrenceGapBlock}
      (marker : leftBlock.marker = rightBlock.marker)
      (seconds : leftBlock.seconds.Perm rightBlock.seconds)
      (rest : CorrespondingGapBlocks leftRest rightRest) :
      CorrespondingGapBlocks
        (leftBlock :: leftRest) (rightBlock :: rightRest)

private theorem perm_of_nodup_mem_iff
    {left right : List Nat}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (members : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left.Perm right := by
  rw [List.perm_iff_count]
  intro letter
  rw [leftNodup.count, rightNodup.count]
  simp only [members letter]

private theorem correspondingGapBlocks_of_data :
    ∀ {seen : List Nat}
      {left right : List FirstOccurrenceGapBlock},
      GapBlocksWellFormed seen left ->
      GapBlocksWellFormed seen right ->
      gapBlockMarkers left = gapBlockMarkers right ->
      (gapBlockSeconds left).Nodup ->
      (gapBlockSeconds right).Nodup ->
      (∀ selected,
        selected ∈ seen ∨ selected ∈ gapBlockMarkers left ->
          blockSecondGapAux selected seen left =
            blockSecondGapAux selected seen right) ->
      CorrespondingGapBlocks left right
  | seen, [], [], _, _, _, _, _, _ => CorrespondingGapBlocks.nil
  | seen, [], _ :: _, _, _, markers, _, _, _ => by
      simp [gapBlockMarkers] at markers
  | seen, _ :: _, [], _, _, markers, _, _, _ => by
      simp [gapBlockMarkers] at markers
  | seen, leftBlock :: leftRest, rightBlock :: rightRest,
      leftFormed, rightFormed, markers, leftSecondsNodup,
      rightSecondsNodup, gaps => by
      cases leftFormed with
      | cons _ _ _ leftFresh leftSeen leftTail =>
        cases rightFormed with
        | cons _ _ _ rightFresh rightSeen rightTail =>
          simp only [gapBlockMarkers, List.map_cons,
            FirstOccurrenceGapBlock.marker] at markers
          injection markers with markerEq tailMarkers
          have rightTailNorm :
              GapBlocksWellFormed
                (leftBlock.marker :: seen) rightRest := by
            simpa [markerEq] using rightTail
          have leftCurrentNodup : leftBlock.seconds.Nodup :=
            (List.nodup_append.mp leftSecondsNodup).1
          have rightCurrentNodup : rightBlock.seconds.Nodup :=
            (List.nodup_append.mp rightSecondsNodup).1
          have currentMembers :
              ∀ selected,
                selected ∈ leftBlock.seconds ↔
                  selected ∈ rightBlock.seconds := by
            intro selected
            constructor
            · intro member
              have known := leftSeen selected member
              have gapEq := gaps selected <| by
                rcases List.mem_cons.mp known with atMarker | inSeen
                · exact Or.inr <| by
                    simp [gapBlockMarkers, atMarker, markerEq]
                · exact Or.inl inSeen
              have sourceGap :=
                (blockSecondGapAux_eq_current_iff selected seen
                  leftBlock leftRest).2 member
              have targetGap :
                  blockSecondGapAux selected seen
                      (rightBlock :: rightRest) =
                    some (rightBlock.marker :: seen).length := by
                calc
                  blockSecondGapAux selected seen
                      (rightBlock :: rightRest) =
                      blockSecondGapAux selected seen
                        (leftBlock :: leftRest) := gapEq.symm
                  _ = some (leftBlock.marker :: seen).length := sourceGap
                  _ = some (rightBlock.marker :: seen).length := by
                    simp [markerEq]
              exact
                (blockSecondGapAux_eq_current_iff selected seen
                  rightBlock rightRest).1 targetGap
            · intro member
              have known := rightSeen selected member
              have gapEq := gaps selected <| by
                rcases List.mem_cons.mp known with atMarker | inSeen
                · exact Or.inr <| by
                    simp [gapBlockMarkers, atMarker, markerEq]
                · exact Or.inl inSeen
              have targetGap :=
                (blockSecondGapAux_eq_current_iff selected seen
                  rightBlock rightRest).2 member
              have sourceGap :
                  blockSecondGapAux selected seen
                      (leftBlock :: leftRest) =
                    some (leftBlock.marker :: seen).length := by
                calc
                  blockSecondGapAux selected seen
                      (leftBlock :: leftRest) =
                      blockSecondGapAux selected seen
                        (rightBlock :: rightRest) := gapEq
                  _ = some (rightBlock.marker :: seen).length := targetGap
                  _ = some (leftBlock.marker :: seen).length := by
                    simp [markerEq]
              exact
                (blockSecondGapAux_eq_current_iff selected seen
                  leftBlock leftRest).1 sourceGap
          have currentPermutation :
              leftBlock.seconds.Perm rightBlock.seconds :=
            perm_of_nodup_mem_iff leftCurrentNodup
              rightCurrentNodup currentMembers
          have leftRestNodup :
              (gapBlockSeconds leftRest).Nodup :=
            (List.nodup_append.mp leftSecondsNodup).2.1
          have rightRestNodup :
              (gapBlockSeconds rightRest).Nodup :=
            (List.nodup_append.mp rightSecondsNodup).2.1
          have restGaps :
              ∀ selected,
                selected ∈ leftBlock.marker :: seen ∨
                    selected ∈ gapBlockMarkers leftRest ->
                  blockSecondGapAux selected
                      (leftBlock.marker :: seen) leftRest =
                    blockSecondGapAux selected
                      (leftBlock.marker :: seen) rightRest := by
            intro selected relevant
            by_cases current : selected ∈ leftBlock.seconds
            · have targetCurrent : selected ∈ rightBlock.seconds :=
                (currentMembers selected).1 current
              have leftRestAbsent :
                  selected ∉ gapBlockSeconds leftRest := by
                intro later
                exact (List.nodup_append.mp leftSecondsNodup).2.2
                  selected current selected later rfl
              have rightRestAbsent :
                  selected ∉ gapBlockSeconds rightRest := by
                intro later
                exact (List.nodup_append.mp rightSecondsNodup).2.2
                  selected targetCurrent selected later rfl
              rw [blockSecondGapAux_eq_none_of_not_mem_seconds
                  selected (leftBlock.marker :: seen) leftRest
                  leftRestAbsent,
                blockSecondGapAux_eq_none_of_not_mem_seconds
                  selected (leftBlock.marker :: seen) rightRest
                  rightRestAbsent]
            · have targetCurrent : selected ∉ rightBlock.seconds := by
                intro member
                exact current ((currentMembers selected).2 member)
              have fullRelevant :
                  selected ∈ seen ∨
                    selected ∈ gapBlockMarkers
                      (leftBlock :: leftRest) := by
                rcases relevant with inNextSeen | inRestMarkers
                · rcases List.mem_cons.mp inNextSeen with atMarker | inSeen
                  · exact Or.inr <| by
                      simp [gapBlockMarkers, atMarker]
                  · exact Or.inl inSeen
                · exact Or.inr <| by
                    change selected ∈
                      leftBlock.marker :: gapBlockMarkers leftRest
                    exact List.Mem.tail leftBlock.marker inRestMarkers
              have full := gaps selected fullRelevant
              simp only [blockSecondGapAux, current, targetCurrent,
                ↓reduceIte] at full
              rw [← markerEq] at full
              exact full
          exact CorrespondingGapBlocks.cons markerEq
            currentPermutation
            (correspondingGapBlocks_of_data leftTail rightTailNorm
              tailMarkers leftRestNodup rightRestNodup restGaps)

theorem correspondingGapBlocks_of_sameSignatureList
    (left right : List Nat)
    (leftLimited : ∀ letter, left.count letter <= 2)
    (rightLimited : ∀ letter, right.count letter <= 2)
    (same : gapSignatureList left = gapSignatureList right) :
    CorrespondingGapBlocks
      (gapBlocksList left) (gapBlocksList right) := by
  have firsts :
      firstOccurrenceSequenceList left =
        firstOccurrenceSequenceList right := by
    simpa [gapSignatureList] using
      congrArg GapSignature.firstOccurrences same
  have secondGaps :
      secondOccurrenceGapsList left =
        secondOccurrenceGapsList right := by
    simpa [gapSignatureList] using
      congrArg GapSignature.secondOccurrenceGaps same
  have markerEq :
      gapBlockMarkers (gapBlocksList left) =
        gapBlockMarkers (gapBlocksList right) := by
    simpa [gapBlockMarkers_gapBlocksList] using firsts
  have mappedGaps :
      (firstOccurrenceSequenceList left).map
          (secondOccurrenceGapList left) =
        (firstOccurrenceSequenceList left).map
          (secondOccurrenceGapList right) := by
    unfold secondOccurrenceGapsList at secondGaps
    rw [← firsts] at secondGaps
    exact secondGaps
  have gapEq :
      ∀ selected,
        selected ∈ gapBlockMarkers (gapBlocksList left) ->
          blockSecondGapAux selected [] (gapBlocksList left) =
            blockSecondGapAux selected [] (gapBlocksList right) := by
    intro selected member
    have inFirsts : selected ∈ firstOccurrenceSequenceList left := by
      simpa [gapBlockMarkers_gapBlocksList] using member
    have pointwise := pointwise_of_map_eq
      (secondOccurrenceGapList left)
      (secondOccurrenceGapList right)
      mappedGaps selected inFirsts
    simpa [secondOccurrenceGapList_eq_blockSecondGapAux] using pointwise
  apply correspondingGapBlocks_of_data
    (gapBlocksList_wellFormed left)
    (gapBlocksList_wellFormed right)
    markerEq
    (gapBlocksList_seconds_nodup left leftLimited)
    (gapBlocksList_seconds_nodup right rightLimited)
  intro selected relevant
  exact gapEq selected (relevant.resolve_left (by simp))

end SemigroupBasis.CoRoots.S5_870
