import SemigroupBasis.CoRoots.Order6SporadicSection27F9Uniqueness
import SemigroupBasis.CoRoots.Order6SporadicSection27BetaBlockCombinatorics

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection27

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_870

private abbrev F9Table : FiniteTable :=
  SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13559.table

private abbrev F9Separator : BetaSeparator F9Table.semigroup :=
  SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13559.betaSeparator

/-!
## The four valuation zones in the Proposition 27.3 proof

The paper's one-based values `4`, `2`, `5`, and `6` are respectively the
ordinary, active, bridge, and fresh fields of the pinned F9 separator.  The
priority order below is intentional: the structural case lemmas must prove
that the zones are disjoint before an active or bridge value can be read.
-/

def f9ZoneValuation
    (ordinaryZone : List Nat) (activeLetter : Nat)
    (bridgeZone : List Nat) (letter : Nat) : Fin 6 :=
  if letter ∈ ordinaryZone then F9Separator.ordinary
  else if letter = activeLetter then F9Separator.active
  else if letter ∈ bridgeZone then F9Separator.bridge
  else F9Separator.fresh

theorem f9ZoneValuation_of_ordinary
    (ordinaryZone bridgeZone : List Nat) (activeLetter letter : Nat)
    (member : letter ∈ ordinaryZone) :
    f9ZoneValuation ordinaryZone activeLetter bridgeZone letter =
      F9Separator.ordinary := by
  simp [f9ZoneValuation, member]

theorem f9ZoneValuation_of_active
    (ordinaryZone bridgeZone : List Nat) (activeLetter : Nat)
    (absent : activeLetter ∉ ordinaryZone) :
    f9ZoneValuation ordinaryZone activeLetter bridgeZone activeLetter =
      F9Separator.active := by
  simp [f9ZoneValuation, absent]

theorem f9ZoneValuation_of_bridge
    (ordinaryZone bridgeZone : List Nat) (activeLetter letter : Nat)
    (ordinaryAbsent : letter ∉ ordinaryZone)
    (activeNe : letter ≠ activeLetter)
    (member : letter ∈ bridgeZone) :
    f9ZoneValuation ordinaryZone activeLetter bridgeZone letter =
      F9Separator.bridge := by
  simp [f9ZoneValuation, ordinaryAbsent, activeNe, member]

theorem f9ZoneValuation_of_fresh
    (ordinaryZone bridgeZone : List Nat) (activeLetter letter : Nat)
    (ordinaryAbsent : letter ∉ ordinaryZone)
    (activeNe : letter ≠ activeLetter)
    (bridgeAbsent : letter ∉ bridgeZone) :
    f9ZoneValuation ordinaryZone activeLetter bridgeZone letter =
      F9Separator.fresh := by
  simp [f9ZoneValuation, ordinaryAbsent, activeNe, bridgeAbsent]

/-! ## A public word wrapper for the semantic prefix calculation -/

def f9CasePrefixWord
    (ordinaryZone : List Nat) (activeLetter : Nat)
    (bridgeZone : List Nat) : Word Nat :=
  match ordinaryZone with
  | [] => S5_107.listWordOfCons activeLetter bridgeZone
  | head :: tail =>
      S5_107.listWordOfCons head (tail ++ activeLetter :: bridgeZone)

theorem f9CasePrefixWord_toList
    (ordinaryZone : List Nat) (activeLetter : Nat)
    (bridgeZone : List Nat) :
    (f9CasePrefixWord ordinaryZone activeLetter bridgeZone).toList =
      ordinaryZone ++ activeLetter :: bridgeZone := by
  cases ordinaryZone <;>
    simp [f9CasePrefixWord, S5_107.listWordOfCons, Word.toList]

/-- Package a possibly empty suffix after adjoining the common fresh
successor used in the paper. -/
def f9SuffixWord (suffix : List Nat) (freshLetter : Nat) : Word Nat :=
  match suffix with
  | [] => Word.singleton freshLetter
  | head :: tail =>
      S5_107.listWordOfCons head (tail ++ [freshLetter])

theorem f9SuffixWord_toList (suffix : List Nat) (freshLetter : Nat) :
    (f9SuffixWord suffix freshLetter).toList =
      suffix ++ [freshLetter] := by
  cases suffix <;>
    simp [f9SuffixWord, S5_107.listWordOfCons, Word.toList]

/-- A deterministic natural strictly above every member of a finite list. -/
def f9FreshAbove : List Nat → Nat
  | [] => 0
  | head :: tail => Nat.max (head + 1) (f9FreshAbove tail)

theorem lt_f9FreshAbove_of_mem (letter : Nat) :
    ∀ letters : List Nat, letter ∈ letters → letter < f9FreshAbove letters
  | [], member => by simp at member
  | head :: tail, member => by
      rcases List.mem_cons.mp member with equal | inTail
      · subst letter
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self head)
          (Nat.le_max_left (head + 1) (f9FreshAbove tail))
      · exact Nat.lt_of_lt_of_le
          (lt_f9FreshAbove_of_mem letter tail inTail)
          (Nat.le_max_right (head + 1) (f9FreshAbove tail))

theorem f9FreshAbove_not_mem (letters : List Nat) :
    f9FreshAbove letters ∉ letters := by
  intro member
  exact Nat.lt_irrefl (f9FreshAbove letters)
    (lt_f9FreshAbove_of_mem (f9FreshAbove letters) letters member)

def f9FreshLetter
    (ordinaryZone : List Nat) (activeLetter : Nat)
    (bridgeZone : List Nat) : Nat :=
  f9FreshAbove (activeLetter :: ordinaryZone ++ bridgeZone)

theorem f9FreshLetter_outside
    (ordinaryZone : List Nat) (activeLetter : Nat)
    (bridgeZone : List Nat) :
    f9FreshLetter ordinaryZone activeLetter bridgeZone ∉ ordinaryZone ∧
      f9FreshLetter ordinaryZone activeLetter bridgeZone ≠ activeLetter ∧
        f9FreshLetter ordinaryZone activeLetter bridgeZone ∉ bridgeZone := by
  have absent :=
    f9FreshAbove_not_mem (activeLetter :: ordinaryZone ++ bridgeZone)
  constructor
  · intro member
    apply absent
    apply List.Mem.tail
    exact List.mem_append_left bridgeZone member
  · constructor
    · intro equal
      apply absent
      change
        f9FreshAbove (activeLetter :: ordinaryZone ++ bridgeZone) =
          activeLetter at equal
      rw [equal]
      exact List.Mem.head _
    · intro member
      apply absent
      apply List.Mem.tail
      exact List.mem_append_right ordinaryZone member

/-! ## Sparse-prefix support and freshness -/

theorem ChoiceIn.member_allowed
    {allowed seconds : List Nat} (choice : ChoiceIn allowed seconds)
    {letter : Nat} (member : letter ∈ seconds) :
    letter ∈ allowed := by
  rcases choice with empty | ⟨selected, selectedAllowed, shape⟩
  · simp [empty] at member
  · rw [shape] at member
    have equal : letter = selected := by simpa using member
    simpa [equal] using selectedAllowed

theorem mem_renderGapBlocks_of_mem_marker
    {blocks : List FirstOccurrenceGapBlock} {letter : Nat}
    (member : letter ∈ gapBlockMarkers blocks) :
    letter ∈ renderGapBlocks blocks := by
  induction blocks with
  | nil => simp [gapBlockMarkers] at member
  | cons block rest induction =>
      simp only [gapBlockMarkers, List.map_cons,
        FirstOccurrenceGapBlock.marker, List.mem_cons] at member
      simp only [renderGapBlocks, List.mem_cons, List.mem_append]
      rcases member with atMarker | inRest
      · exact Or.inl atMarker
      · exact Or.inr (Or.inr (induction inRest))

/-- Every letter rendered by a sparse prefix belongs to its final reverse
marker accumulator. -/
theorem SparseBlocks.mem_seenAfter_of_mem_render
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (sparse : SparseBlocks seen blocks) {letter : Nat}
    (member : letter ∈ renderGapBlocks blocks) :
    letter ∈ seenAfterGapBlocks seen blocks := by
  induction sparse with
  | nil seen => simp [renderGapBlocks] at member
  | cons seen block rest markerFresh choice tail induction =>
      simp only [renderGapBlocks, List.mem_cons,
        List.mem_append] at member
      rw [seenAfterGapBlocks_cons]
      rcases member with atMarker | inSeconds | inRest
      · subst letter
        simp [seenAfterGapBlocks]
      · have allowed := choice.member_allowed inSeconds
        simp only [seenAfterGapBlocks, List.mem_append]
        exact Or.inr allowed
      · exact induction inRest

theorem SparseBlocks.earlierIn_next_of_mem_render
    {blocks : List FirstOccurrenceGapBlock}
    (sparse : SparseBlocks [] blocks)
    {markers suffix : List Nat} {letter nextMarker : Nat}
    (markerShape :
      markers = gapBlockMarkers blocks ++ nextMarker :: suffix)
    (member : letter ∈ renderGapBlocks blocks) :
    EarlierIn markers letter nextMarker := by
  have inSeen := sparse.mem_seenAfter_of_mem_render member
  have inMarkers : letter ∈ gapBlockMarkers blocks := by
    simpa [seenAfterGapBlocks] using inSeen
  obtain ⟨before, middle, shape⟩ := List.mem_iff_append.mp inMarkers
  exact ⟨before, middle, suffix, by
    rw [markerShape, shape]⟩

/-- The head of a nonempty sparse rendered suffix is fresh for its incoming
accumulator. -/
theorem SparseBlocks.render_head_not_mem_seen
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (sparse : SparseBlocks seen blocks) {head : Nat} {tail : List Nat}
    (shape : renderGapBlocks blocks = head :: tail) :
    head ∉ seen := by
  cases blocks with
  | nil => simp [renderGapBlocks] at shape
  | cons block rest =>
      have headData := sparse.cons_inv
      simp only [renderGapBlocks] at shape
      injection shape with headEq _
      subst head
      exact headData.1

theorem SparseBlocks.render_head_outside_zones
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (sparse : SparseBlocks seen blocks) {head : Nat} {tail : List Nat}
    (shape : renderGapBlocks blocks = head :: tail)
    (ordinaryZone bridgeZone : List Nat) (activeLetter : Nat)
    (ordinarySeen : ∀ letter, letter ∈ ordinaryZone → letter ∈ seen)
    (activeSeen : activeLetter ∈ seen)
    (bridgeSeen : ∀ letter, letter ∈ bridgeZone → letter ∈ seen) :
    head ∉ ordinaryZone ∧ head ≠ activeLetter ∧ head ∉ bridgeZone := by
  have fresh := sparse.render_head_not_mem_seen shape
  exact ⟨
    (by intro member; exact fresh (ordinarySeen head member)),
    (by intro equal; exact fresh (by simpa [equal] using activeSeen)),
    (by intro member; exact fresh (bridgeSeen head member))⟩

theorem LeastDifferingSparseBlocks.current_not_mem_renderedCommonPrefix
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference : LeastDifferingSparseBlocks [] leftBlocks rightBlocks) :
    difference.leftBlock.marker ∉
      renderGapBlocks difference.commonPrefix := by
  intro member
  exact difference.markerFresh
    (difference.leftPrefixSparse.mem_seenAfter_of_mem_render member)

theorem LeastDifferingSparseBlocks.mem_tailSeen_of_mem_renderedPrefix
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference : LeastDifferingSparseBlocks [] leftBlocks rightBlocks)
    {letter : Nat}
    (member : letter ∈ renderGapBlocks difference.commonPrefix) :
    letter ∈ difference.leftBlock.marker ::
      seenAfterGapBlocks [] difference.commonPrefix :=
  List.Mem.tail difference.leftBlock.marker
    (difference.leftPrefixSparse.mem_seenAfter_of_mem_render member)

theorem LeastDifferingSparseBlocks.selected_mem_renderedCommonPrefix
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference : LeastDifferingSparseBlocks [] leftBlocks rightBlocks)
    {selected : Nat}
    (allowed :
      selected ∈ difference.leftBlock.marker ::
        seenAfterGapBlocks [] difference.commonPrefix)
    (notCurrent : selected ≠ difference.leftBlock.marker) :
    selected ∈ renderGapBlocks difference.commonPrefix := by
  have inSeen :
      selected ∈ seenAfterGapBlocks [] difference.commonPrefix :=
    (List.mem_cons.mp allowed).resolve_left notCurrent
  have inMarkers :
      selected ∈ gapBlockMarkers difference.commonPrefix := by
    simpa [seenAfterGapBlocks] using inSeen
  exact mem_renderGapBlocks_of_mem_marker inMarkers

theorem LeastDifferingSparseBlocks.earlierIn_current_of_mem_renderedPrefix
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference : LeastDifferingSparseBlocks [] leftBlocks rightBlocks)
    {letter : Nat}
    (member : letter ∈ renderGapBlocks difference.commonPrefix) :
    EarlierIn (gapBlockMarkers leftBlocks)
      letter difference.leftBlock.marker := by
  have inSeen :=
    difference.leftPrefixSparse.mem_seenAfter_of_mem_render member
  have inMarkers : letter ∈ gapBlockMarkers difference.commonPrefix := by
    simpa [seenAfterGapBlocks] using inSeen
  obtain ⟨before, middle, prefixShape⟩ :=
    List.mem_iff_append.mp inMarkers
  exact ⟨before, middle, gapBlockMarkers difference.leftTail, by
    rw [difference.left_markerSequence_eq, prefixShape]⟩

theorem ChoiceIn.selected_allowed_of_eq_singleton
    {allowed seconds : List Nat} (choice : ChoiceIn allowed seconds)
    {selected : Nat} (shape : seconds = [selected]) :
    selected ∈ allowed :=
  choice.member_allowed <| by simp [shape]

/-- Split at the first occurrence of a selected natural. -/
theorem exists_firstOccurrence_split
    (selected : Nat) :
    ∀ {letters : List Nat}, selected ∈ letters →
      ∃ before after,
        letters = before ++ selected :: after ∧ selected ∉ before
  | [], member => by simp at member
  | head :: tail, member => by
      by_cases equal : head = selected
      · subst head
        exact ⟨[], tail, by simp⟩
      · have inTail : selected ∈ tail := by
          rcases List.mem_cons.mp member with atHead | inTail
          · exact False.elim (equal atHead.symm)
          · exact inTail
        obtain ⟨before, after, shape, absent⟩ :=
          exists_firstOccurrence_split selected inTail
        exact ⟨head :: before, after, by simp [shape], by
          intro prefixMember
          rcases List.mem_cons.mp prefixMember with atHead | inBefore
          · exact (Ne.symm equal) atHead
          · exact absent inBefore⟩

/-- Every nonempty list has a literal last-letter split. -/
theorem exists_append_singleton_of_ne_nil :
    ∀ letters : List Nat, letters ≠ [] →
      ∃ initial final, letters = initial ++ [final]
  | [], different => False.elim (different rfl)
  | head :: tail, _ => by
      cases tail with
      | nil => exact ⟨[], head, rfl⟩
      | cons next rest =>
          obtain ⟨initial, final, shape⟩ :=
            exists_append_singleton_of_ne_nil (next :: rest) (by simp)
          exact ⟨head :: initial, final, by simp [shape]⟩

/-- The exact ordinary/active/bridge scan used in the four nonempty-prefix
subcases of Cases 2 and 3. -/
theorem f9_eval_casePrefixWord
    (ordinaryZone : List Nat) (activeLetter : Nat)
    (bridgeZone : List Nat)
    (activeAbsent : activeLetter ∉ ordinaryZone)
    (bridgeDisjoint :
      ∀ letter, letter ∈ bridgeZone →
        letter ∉ ordinaryZone ∧ letter ≠ activeLetter) :
    F9Table.semigroup.eval
        (f9ZoneValuation ordinaryZone activeLetter bridgeZone)
        (f9CasePrefixWord ordinaryZone activeLetter bridgeZone) =
      F9Separator.active := by
  exact f9_eval_paperPrefixWord
    (f9ZoneValuation ordinaryZone activeLetter bridgeZone)
    ordinaryZone activeLetter bridgeZone
    (by
      intro letter member
      exact f9ZoneValuation_of_ordinary
        ordinaryZone bridgeZone activeLetter letter member)
    (f9ZoneValuation_of_active
      ordinaryZone bridgeZone activeLetter activeAbsent)
    (by
      intro letter member
      exact f9ZoneValuation_of_bridge
        ordinaryZone bridgeZone activeLetter letter
        (bridgeDisjoint letter member).1
        (bridgeDisjoint letter member).2 member)

/-!
## Exact semantic payloads for the three paper cases

Case 1 has no bridge letter after the active prefix.  Cases 2 and 3 share
the bridge payload; their different combinatorics are entirely in how the
zone-disjointness fields are obtained from conditions (II) and (III).
-/

structure F9Case1Data (left right : Word Nat) where
  freshLetter : Nat
  ordinaryZone : List Nat
  activeLetter : Nat
  killed : Nat
  leftTail : Word Nat
  rightTail : Word Nat
  leftExtended_eq :
    left ++ Word.singleton freshLetter =
      (f9CasePrefixWord ordinaryZone activeLetter [] ++
        Word.singleton killed) ++ leftTail
  rightExtended_eq :
    right ++ Word.singleton freshLetter =
      f9CasePrefixWord ordinaryZone activeLetter [] ++ rightTail
  activeAbsent : activeLetter ∉ ordinaryZone
  killedZone : killed ∈ ordinaryZone ∨ killed = activeLetter
  leftTailOutside :
    leftTail.head ∉ ordinaryZone ∧ leftTail.head ≠ activeLetter
  rightTailOutside :
    rightTail.head ∉ ordinaryZone ∧ rightTail.head ≠ activeLetter

structure F9BridgeCaseData (left right : Word Nat) where
  freshLetter : Nat
  ordinaryZone : List Nat
  activeLetter : Nat
  bridgeZone : List Nat
  killed : Nat
  preserved : Nat
  leftTail : Word Nat
  rightTail : Word Nat
  leftExtended_eq :
    left ++ Word.singleton freshLetter =
      (f9CasePrefixWord ordinaryZone activeLetter bridgeZone ++
        Word.singleton killed) ++ leftTail
  rightExtended_eq :
    right ++ Word.singleton freshLetter =
      (f9CasePrefixWord ordinaryZone activeLetter bridgeZone ++
        Word.singleton preserved) ++ rightTail
  activeAbsent : activeLetter ∉ ordinaryZone
  bridgeDisjoint :
    ∀ letter, letter ∈ bridgeZone →
      letter ∉ ordinaryZone ∧ letter ≠ activeLetter
  killedZone : killed ∈ ordinaryZone ∨ killed = activeLetter
  preservedBridge : preserved ∈ bridgeZone
  leftTailOutside :
    leftTail.head ∉ ordinaryZone ∧
      leftTail.head ≠ activeLetter ∧
        leftTail.head ∉ bridgeZone
  rightTailOutside :
    rightTail.head ∉ ordinaryZone ∧
      rightTail.head ≠ activeLetter ∧
        rightTail.head ∉ bridgeZone

namespace F9Case1Data

/-- Build the Case-1 payload directly from literal list splits.  The two
head hypotheses cover a genuine next marker; `freshOutside` covers the
terminal block after adjoining the common successor. -/
def ofListShapes
    {left right : Word Nat}
    (freshLetter : Nat) (ordinaryZone : List Nat)
    (activeLetter killed : Nat) (leftSuffix rightSuffix : List Nat)
    (leftShape :
      left.toList =
        ordinaryZone ++ activeLetter :: killed :: leftSuffix)
    (rightShape :
      right.toList = ordinaryZone ++ activeLetter :: rightSuffix)
    (activeAbsent : activeLetter ∉ ordinaryZone)
    (killedZone : killed ∈ ordinaryZone ∨ killed = activeLetter)
    (leftHeadOutside :
      ∀ head tail, leftSuffix = head :: tail →
        head ∉ ordinaryZone ∧ head ≠ activeLetter)
    (rightHeadOutside :
      ∀ head tail, rightSuffix = head :: tail →
        head ∉ ordinaryZone ∧ head ≠ activeLetter)
    (freshOutside :
      freshLetter ∉ ordinaryZone ∧ freshLetter ≠ activeLetter) :
    F9Case1Data left right where
  freshLetter := freshLetter
  ordinaryZone := ordinaryZone
  activeLetter := activeLetter
  killed := killed
  leftTail := f9SuffixWord leftSuffix freshLetter
  rightTail := f9SuffixWord rightSuffix freshLetter
  leftExtended_eq := by
    apply Word.toList_injective
    simp [Word.toList_append, f9CasePrefixWord_toList,
      f9SuffixWord_toList, leftShape, List.append_assoc]
  rightExtended_eq := by
    apply Word.toList_injective
    simp [Word.toList_append, f9CasePrefixWord_toList,
      f9SuffixWord_toList, rightShape, List.append_assoc]
  activeAbsent := activeAbsent
  killedZone := killedZone
  leftTailOutside := by
    cases leftSuffix with
    | nil => simpa [f9SuffixWord] using freshOutside
    | cons head tail =>
        simpa [f9SuffixWord] using leftHeadOutside head tail rfl
  rightTailOutside := by
    cases rightSuffix with
    | nil => simpa [f9SuffixWord] using freshOutside
    | cons head tail =>
        simpa [f9SuffixWord] using rightHeadOutside head tail rfl

end F9Case1Data

namespace F9BridgeCaseData

/-- Build a Case-2/3 bridge payload from the paper's literal list splits. -/
def ofListShapes
    {left right : Word Nat}
    (freshLetter : Nat) (ordinaryZone : List Nat)
    (activeLetter : Nat) (bridgeZone : List Nat)
    (killed preserved : Nat) (leftSuffix rightSuffix : List Nat)
    (leftShape :
      left.toList =
        ordinaryZone ++ activeLetter :: bridgeZone ++
          killed :: leftSuffix)
    (rightShape :
      right.toList =
        ordinaryZone ++ activeLetter :: bridgeZone ++
          preserved :: rightSuffix)
    (activeAbsent : activeLetter ∉ ordinaryZone)
    (bridgeDisjoint :
      ∀ letter, letter ∈ bridgeZone →
        letter ∉ ordinaryZone ∧ letter ≠ activeLetter)
    (killedZone : killed ∈ ordinaryZone ∨ killed = activeLetter)
    (preservedBridge : preserved ∈ bridgeZone)
    (leftHeadOutside :
      ∀ head tail, leftSuffix = head :: tail →
        head ∉ ordinaryZone ∧
          head ≠ activeLetter ∧ head ∉ bridgeZone)
    (rightHeadOutside :
      ∀ head tail, rightSuffix = head :: tail →
        head ∉ ordinaryZone ∧
          head ≠ activeLetter ∧ head ∉ bridgeZone)
    (freshOutside :
      freshLetter ∉ ordinaryZone ∧
        freshLetter ≠ activeLetter ∧ freshLetter ∉ bridgeZone) :
    F9BridgeCaseData left right where
  freshLetter := freshLetter
  ordinaryZone := ordinaryZone
  activeLetter := activeLetter
  bridgeZone := bridgeZone
  killed := killed
  preserved := preserved
  leftTail := f9SuffixWord leftSuffix freshLetter
  rightTail := f9SuffixWord rightSuffix freshLetter
  leftExtended_eq := by
    apply Word.toList_injective
    simp [Word.toList_append, f9CasePrefixWord_toList,
      f9SuffixWord_toList, leftShape, List.append_assoc]
  rightExtended_eq := by
    apply Word.toList_injective
    simp [Word.toList_append, f9CasePrefixWord_toList,
      f9SuffixWord_toList, rightShape, List.append_assoc]
  activeAbsent := activeAbsent
  bridgeDisjoint := bridgeDisjoint
  killedZone := killedZone
  preservedBridge := preservedBridge
  leftTailOutside := by
    cases leftSuffix with
    | nil => simpa [f9SuffixWord] using freshOutside
    | cons head tail =>
        simpa [f9SuffixWord] using leftHeadOutside head tail rfl
  rightTailOutside := by
    cases rightSuffix with
    | nil => simpa [f9SuffixWord] using freshOutside
    | cons head tail =>
        simpa [f9SuffixWord] using rightHeadOutside head tail rfl

end F9BridgeCaseData

/-!
## Canonical obstruction eliminators

These are the two list frames used verbatim in Cases 2.1 and 3.1.  They turn
conditions (II) and (III) into the zone-disjointness facts consumed above.
-/

/-- Membership in the strict marker prefix gives literal first-occurrence
order before the displayed marker. -/
theorem EarlierIn.of_mem_strictPrefix
    {markers before after : List Nat} {earlier later : Nat}
    (shape : markers = before ++ later :: after)
    (member : earlier ∈ before) :
    EarlierIn markers earlier later := by
  obtain ⟨first, middle, beforeShape⟩ :=
    List.mem_iff_append.mp member
  exact ⟨first, middle, after, by
    simpa [beforeShape, List.append_assoc] using shape⟩

/-- In a condition-(III)-free word, the active letter immediately preceding
the first displayed later marker cannot already occur in the preceding zone.
-/
theorem noAdjacentPair_forces_active_not_mem
    {markers letters before middle after : List Nat}
    {active later : Nat}
    (noAdjacent : ¬ Has27AdjacentPair markers letters)
    (order : EarlierIn markers active later)
    (shape :
      letters =
        before ++ [active, later] ++ middle ++ [later] ++ after) :
    active ∉ before := by
  intro member
  obtain ⟨initial, gap, beforeShape⟩ :=
    List.mem_iff_append.mp member
  apply noAdjacent
  exact ⟨active, later, initial, gap, middle, after, order, by
    simpa [beforeShape, List.append_assoc] using shape⟩

/-- In a condition-(II)-free word, the zone before the first displayed later
marker is disjoint from the zone between its two occurrences, provided every
letter of the first zone is earlier in first-occurrence order. -/
theorem noCrossing_forces_zone_disjoint
    {markers letters firstZone middleZone after : List Nat}
    {later : Nat}
    (noCrossing : ¬ Has27Crossing markers letters)
    (order :
      ∀ earlier, earlier ∈ firstZone → EarlierIn markers earlier later)
    (shape :
      letters =
        firstZone ++ [later] ++ middleZone ++ [later] ++ after) :
    ∀ letter, letter ∈ firstZone → letter ∉ middleZone := by
  intro letter inFirst inMiddle
  obtain ⟨before, firstGap, firstShape⟩ :=
    List.mem_iff_append.mp inFirst
  obtain ⟨secondGap, thirdGap, middleShape⟩ :=
    List.mem_iff_append.mp inMiddle
  apply noCrossing
  exact ⟨letter, later, before, firstGap, secondGap, thirdGap,
    after, order letter inFirst, by
      simpa [firstShape, middleShape, List.append_assoc] using shape⟩

/-- The form used in Case 3: the complete bridge zone, including its leading
later marker, avoids the zone preceding that marker. -/
theorem noCrossing_forces_bridge_disjoint
    {markers letters firstZone bridgeTail after : List Nat}
    {later : Nat}
    (noCrossing : ¬ Has27Crossing markers letters)
    (laterAbsent : later ∉ firstZone)
    (order :
      ∀ earlier, earlier ∈ firstZone → EarlierIn markers earlier later)
    (shape :
      letters =
        firstZone ++ [later] ++ bridgeTail ++ [later] ++ after) :
    ∀ letter, letter ∈ later :: bridgeTail → letter ∉ firstZone := by
  intro letter member inFirst
  rcases List.mem_cons.mp member with equal | inBridgeTail
  · subst letter
    exact laterAbsent inFirst
  · exact
      (noCrossing_forces_zone_disjoint noCrossing order shape
        letter inFirst) inBridgeTail

/-! ## Case 1 extraction from a least differing block -/

noncomputable def LeastDifferingSparseBlocks.case1Data
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference : LeastDifferingSparseBlocks [] leftBlocks rightBlocks)
    {leftWord rightWord : Word Nat} {selected : Nat}
    (leftRendered : renderGapBlocks leftBlocks = leftWord.toList)
    (rightRendered : renderGapBlocks rightBlocks = rightWord.toList)
    (leftSeconds : difference.leftBlock.seconds = [selected])
    (rightSeconds : difference.rightBlock.seconds = []) :
    F9Case1Data leftWord rightWord := by
  let ordinaryZone := renderGapBlocks difference.commonPrefix
  let current := difference.leftBlock.marker
  let leftSuffix := renderGapBlocks difference.leftTail
  let rightSuffix := renderGapBlocks difference.rightTail
  let freshLetter := f9FreshLetter ordinaryZone current []
  have activeAbsent : current ∉ ordinaryZone := by
    exact difference.current_not_mem_renderedCommonPrefix
  have selectedAllowed :
      selected ∈ current ::
        seenAfterGapBlocks [] difference.commonPrefix := by
    exact difference.leftChoice.selected_allowed_of_eq_singleton
      leftSeconds
  have killedZone : selected ∈ ordinaryZone ∨ selected = current := by
    rcases List.mem_cons.mp selectedAllowed with atCurrent | inSeen
    · exact Or.inr atCurrent
    · apply Or.inl
      apply mem_renderGapBlocks_of_mem_marker
      simpa [seenAfterGapBlocks] using inSeen
  have leftShape :
      leftWord.toList = ordinaryZone ++ current :: selected :: leftSuffix := by
    calc
      leftWord.toList = renderGapBlocks leftBlocks := leftRendered.symm
      _ = difference.renderedPrefix ++
            difference.leftBlock.seconds ++
            renderGapBlocks difference.leftTail :=
        difference.left_render_eq
      _ = ordinaryZone ++ current :: selected :: leftSuffix := by
        simp [LeastDifferingSparseBlocks.renderedPrefix,
          ordinaryZone, current, leftSuffix, leftSeconds,
          List.append_assoc]
  have rightShape :
      rightWord.toList = ordinaryZone ++ current :: rightSuffix := by
    calc
      rightWord.toList = renderGapBlocks rightBlocks := rightRendered.symm
      _ = difference.renderedPrefix ++
            difference.rightBlock.seconds ++
            renderGapBlocks difference.rightTail :=
        difference.right_render_eq
      _ = ordinaryZone ++ current :: rightSuffix := by
        simp [LeastDifferingSparseBlocks.renderedPrefix,
          ordinaryZone, current, rightSuffix, rightSeconds,
          List.append_assoc]
  have leftHeadOutside :
      ∀ head tail, leftSuffix = head :: tail →
        head ∉ ordinaryZone ∧ head ≠ current := by
    intro head tail shape
    have headFresh :=
      difference.leftTailSparse.render_head_not_mem_seen <| by
        simpa [leftSuffix] using shape
    constructor
    · intro member
      apply headFresh
      exact List.Mem.tail current <|
        difference.leftPrefixSparse.mem_seenAfter_of_mem_render <| by
          simpa [ordinaryZone] using member
    · intro equal
      subst head
      exact headFresh (List.Mem.head _)
  have rightHeadOutside :
      ∀ head tail, rightSuffix = head :: tail →
        head ∉ ordinaryZone ∧ head ≠ current := by
    intro head tail shape
    have headFresh :=
      difference.rightTailSparse.render_head_not_mem_seen <| by
        simpa [rightSuffix] using shape
    constructor
    · intro member
      apply headFresh
      exact List.Mem.tail current <|
        difference.rightPrefixSparse.mem_seenAfter_of_mem_render <| by
          simpa [ordinaryZone] using member
    · intro equal
      subst head
      exact headFresh (List.Mem.head _)
  have freshOutside :
      freshLetter ∉ ordinaryZone ∧ freshLetter ≠ current := by
    have outside := f9FreshLetter_outside ordinaryZone current []
    exact ⟨outside.1, outside.2.1⟩
  exact F9Case1Data.ofListShapes
    freshLetter ordinaryZone current selected leftSuffix rightSuffix
    leftShape rightShape activeAbsent killedZone
    leftHeadOutside rightHeadOutside freshOutside

/-! ## Case 2 extraction -/

noncomputable def LeastDifferingSparseBlocks.case2Data
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference : LeastDifferingSparseBlocks [] leftBlocks rightBlocks)
    {leftWord rightWord : Word Nat} {selected : Nat}
    (leftRendered : renderGapBlocks leftBlocks = leftWord.toList)
    (rightRendered : renderGapBlocks rightBlocks = rightWord.toList)
    (rightNoAdjacent :
      ¬ Has27AdjacentPair
        (gapBlockMarkers leftBlocks) (renderGapBlocks rightBlocks))
    (leftSeconds : difference.leftBlock.seconds = [selected])
    (rightSeconds :
      difference.rightBlock.seconds = [difference.leftBlock.marker]) :
    F9BridgeCaseData leftWord rightWord := by
  let commonRendered := renderGapBlocks difference.commonPrefix
  let current := difference.leftBlock.marker
  let leftSuffix := renderGapBlocks difference.leftTail
  let rightSuffix := renderGapBlocks difference.rightTail
  have selectedNeCurrent : selected ≠ current := by
    intro equal
    apply difference.differentSeconds
    simpa [leftSeconds, rightSeconds, current, equal]
  have selectedAllowed :
      selected ∈ current :: seenAfterGapBlocks [] difference.commonPrefix :=
    difference.leftChoice.selected_allowed_of_eq_singleton leftSeconds
  have selectedInPrefix : selected ∈ commonRendered := by
    exact difference.selected_mem_renderedCommonPrefix
      selectedAllowed selectedNeCurrent
  have currentAbsent : current ∉ commonRendered :=
    difference.current_not_mem_renderedCommonPrefix
  have leftBaseShape :
      leftWord.toList = commonRendered ++ current :: selected :: leftSuffix := by
    calc
      leftWord.toList = renderGapBlocks leftBlocks := leftRendered.symm
      _ = difference.renderedPrefix ++
            difference.leftBlock.seconds ++
            renderGapBlocks difference.leftTail :=
        difference.left_render_eq
      _ = commonRendered ++ current :: selected :: leftSuffix := by
        simp [LeastDifferingSparseBlocks.renderedPrefix,
          commonRendered, current, leftSuffix, leftSeconds, List.append_assoc]
  have rightBaseShape :
      rightWord.toList = commonRendered ++ current :: current :: rightSuffix := by
    calc
      rightWord.toList = renderGapBlocks rightBlocks := rightRendered.symm
      _ = difference.renderedPrefix ++
            difference.rightBlock.seconds ++
            renderGapBlocks difference.rightTail :=
        difference.right_render_eq
      _ = commonRendered ++ current :: current :: rightSuffix := by
        simp [LeastDifferingSparseBlocks.renderedPrefix,
          commonRendered, current, rightSuffix, rightSeconds, List.append_assoc]
  let prefixSplit :=
    exists_firstOccurrence_split selected selectedInPrefix
  let before : List Nat := Classical.choose prefixSplit
  have suffixSplit :
      ∃ after,
        commonRendered = before ++ selected :: after ∧
          selected ∉ before :=
    Classical.choose_spec prefixSplit
  let gap : List Nat := Classical.choose suffixSplit
  have prefixFacts :
      commonRendered = before ++ selected :: gap ∧
        selected ∉ before :=
    Classical.choose_spec suffixSplit
  have prefixShape := prefixFacts.1
  have selectedAbsent := prefixFacts.2
  by_cases gapEmpty : gap = []
  · have exactPrefix : commonRendered = before ++ [selected] := by
      simpa [gapEmpty] using prefixShape
    let ordinaryZone := before
    let activeLetter := selected
    let bridgeZone := [current]
    let freshLetter :=
      f9FreshLetter ordinaryZone activeLetter bridgeZone
    have activeAbsent : activeLetter ∉ ordinaryZone := by
      simpa [ordinaryZone, activeLetter] using selectedAbsent
    have bridgeDisjoint :
        ∀ letter, letter ∈ bridgeZone →
          letter ∉ ordinaryZone ∧ letter ≠ activeLetter := by
      intro letter member
      have equal : letter = current := by
        simpa [bridgeZone] using member
      subst letter
      constructor
      · intro inOrdinary
        apply currentAbsent
        rw [exactPrefix]
        exact List.mem_append_left [selected] <| by
          simpa [ordinaryZone] using inOrdinary
      · exact Ne.symm selectedNeCurrent
    have leftShape :
        leftWord.toList =
          ordinaryZone ++ activeLetter :: bridgeZone ++
            selected :: leftSuffix := by
      simpa [ordinaryZone, activeLetter, bridgeZone, exactPrefix,
        List.append_assoc] using leftBaseShape
    have rightShape :
        rightWord.toList =
          ordinaryZone ++ activeLetter :: bridgeZone ++
            current :: rightSuffix := by
      simpa [ordinaryZone, activeLetter, bridgeZone, exactPrefix,
        List.append_assoc] using rightBaseShape
    have ordinarySeen :
        ∀ letter, letter ∈ ordinaryZone →
          letter ∈ current ::
            seenAfterGapBlocks [] difference.commonPrefix := by
      intro letter member
      apply difference.mem_tailSeen_of_mem_renderedPrefix
      change letter ∈ commonRendered
      rw [exactPrefix]
      exact List.mem_append_left [selected] <| by
        simpa [ordinaryZone] using member
    have activeSeen :
        activeLetter ∈ current ::
          seenAfterGapBlocks [] difference.commonPrefix := by
      simpa [activeLetter] using selectedAllowed
    have bridgeSeen :
        ∀ letter, letter ∈ bridgeZone →
          letter ∈ current ::
            seenAfterGapBlocks [] difference.commonPrefix := by
      intro letter member
      have equal : letter = current := by
        simpa [bridgeZone] using member
      subst letter
      exact List.Mem.head _
    have leftHeadOutside :
        ∀ head tail, leftSuffix = head :: tail →
          head ∉ ordinaryZone ∧
            head ≠ activeLetter ∧ head ∉ bridgeZone := by
      intro head tail shape
      apply difference.leftTailSparse.render_head_outside_zones
        (ordinaryZone := ordinaryZone) (bridgeZone := bridgeZone)
        (activeLetter := activeLetter)
      · simpa [leftSuffix] using shape
      · exact ordinarySeen
      · exact activeSeen
      · exact bridgeSeen
    have rightHeadOutside :
        ∀ head tail, rightSuffix = head :: tail →
          head ∉ ordinaryZone ∧
            head ≠ activeLetter ∧ head ∉ bridgeZone := by
      intro head tail shape
      apply difference.rightTailSparse.render_head_outside_zones
        (ordinaryZone := ordinaryZone) (bridgeZone := bridgeZone)
        (activeLetter := activeLetter)
      · simpa [rightSuffix] using shape
      · exact ordinarySeen
      · exact activeSeen
      · exact bridgeSeen
    have freshOutside :=
      f9FreshLetter_outside ordinaryZone activeLetter bridgeZone
    exact F9BridgeCaseData.ofListShapes
      freshLetter ordinaryZone activeLetter bridgeZone
      selected current leftSuffix rightSuffix
      leftShape rightShape activeAbsent bridgeDisjoint
      (Or.inr rfl) (by simp [bridgeZone])
      leftHeadOutside rightHeadOutside freshOutside
  · let terminalSplit :=
      exists_append_singleton_of_ne_nil gap gapEmpty
    let middle : List Nat := Classical.choose terminalSplit
    have finalSplit :
        ∃ final, gap = middle ++ [final] :=
      Classical.choose_spec terminalSplit
    let activeLetter : Nat := Classical.choose finalSplit
    have gapShape : gap = middle ++ [activeLetter] :=
      Classical.choose_spec finalSplit
    let ordinaryZone := before ++ selected :: middle
    let bridgeZone := [current]
    let freshLetter :=
      f9FreshLetter ordinaryZone activeLetter bridgeZone
    have activeInPrefix : activeLetter ∈ commonRendered := by
      rw [prefixShape, gapShape]
      simp
    have activeOrder :
        EarlierIn (gapBlockMarkers leftBlocks) activeLetter current :=
      difference.earlierIn_current_of_mem_renderedPrefix activeInPrefix
    have adjacentShape :
        renderGapBlocks rightBlocks =
          ordinaryZone ++ [activeLetter, current] ++ [] ++
            [current] ++ rightSuffix := by
      calc
        renderGapBlocks rightBlocks = rightWord.toList := rightRendered
        _ = commonRendered ++ current :: current :: rightSuffix := rightBaseShape
        _ = ordinaryZone ++ [activeLetter, current] ++ [] ++
              [current] ++ rightSuffix := by
          simp [prefixShape, gapShape, ordinaryZone,
            List.append_assoc]
    have activeAbsent : activeLetter ∉ ordinaryZone :=
      noAdjacentPair_forces_active_not_mem
        rightNoAdjacent activeOrder adjacentShape
    have bridgeDisjoint :
        ∀ letter, letter ∈ bridgeZone →
          letter ∉ ordinaryZone ∧ letter ≠ activeLetter := by
      intro letter member
      have equal : letter = current := by
        simpa [bridgeZone] using member
      subst letter
      constructor
      · intro inOrdinary
        apply currentAbsent
        rw [prefixShape, gapShape]
        simpa [ordinaryZone, List.append_assoc] using
          List.mem_append_left [activeLetter] inOrdinary
      · intro equal
        apply currentAbsent
        simpa [equal] using activeInPrefix
    have leftShape :
        leftWord.toList =
          ordinaryZone ++ activeLetter :: bridgeZone ++
            selected :: leftSuffix := by
      simpa [prefixShape, gapShape, ordinaryZone, bridgeZone,
        List.append_assoc] using leftBaseShape
    have rightShape :
        rightWord.toList =
          ordinaryZone ++ activeLetter :: bridgeZone ++
            current :: rightSuffix := by
      simpa [prefixShape, gapShape, ordinaryZone, bridgeZone,
        List.append_assoc] using rightBaseShape
    have ordinarySeen :
        ∀ letter, letter ∈ ordinaryZone →
          letter ∈ current ::
            seenAfterGapBlocks [] difference.commonPrefix := by
      intro letter member
      apply difference.mem_tailSeen_of_mem_renderedPrefix
      change letter ∈ commonRendered
      rw [prefixShape, gapShape]
      have extended : letter ∈ ordinaryZone ++ [activeLetter] :=
        List.mem_append_left [activeLetter] member
      simpa [ordinaryZone, List.append_assoc] using extended
    have activeSeen :
        activeLetter ∈ current ::
          seenAfterGapBlocks [] difference.commonPrefix :=
      difference.mem_tailSeen_of_mem_renderedPrefix activeInPrefix
    have bridgeSeen :
        ∀ letter, letter ∈ bridgeZone →
          letter ∈ current ::
            seenAfterGapBlocks [] difference.commonPrefix := by
      intro letter member
      have equal : letter = current := by
        simpa [bridgeZone] using member
      subst letter
      exact List.Mem.head _
    have leftHeadOutside :
        ∀ head tail, leftSuffix = head :: tail →
          head ∉ ordinaryZone ∧
            head ≠ activeLetter ∧ head ∉ bridgeZone := by
      intro head tail shape
      apply difference.leftTailSparse.render_head_outside_zones
        (ordinaryZone := ordinaryZone) (bridgeZone := bridgeZone)
        (activeLetter := activeLetter)
      · simpa [leftSuffix] using shape
      · exact ordinarySeen
      · exact activeSeen
      · exact bridgeSeen
    have rightHeadOutside :
        ∀ head tail, rightSuffix = head :: tail →
          head ∉ ordinaryZone ∧
            head ≠ activeLetter ∧ head ∉ bridgeZone := by
      intro head tail shape
      apply difference.rightTailSparse.render_head_outside_zones
        (ordinaryZone := ordinaryZone) (bridgeZone := bridgeZone)
        (activeLetter := activeLetter)
      · simpa [rightSuffix] using shape
      · exact ordinarySeen
      · exact activeSeen
      · exact bridgeSeen
    have freshOutside :=
      f9FreshLetter_outside ordinaryZone activeLetter bridgeZone
    exact F9BridgeCaseData.ofListShapes
      freshLetter ordinaryZone activeLetter bridgeZone
      selected current leftSuffix rightSuffix
      leftShape rightShape activeAbsent bridgeDisjoint
      (Or.inl <| by simp [ordinaryZone]) (by simp [bridgeZone])
      leftHeadOutside rightHeadOutside freshOutside

/-! ## Case 3 extraction -/

/-- Extract the bridge valuation for two distinct previously selected letters
at the least differing block.  The ordered rendered-prefix split is the exact
`e x_i f x_j g` decomposition from Proposition 27.3. -/
noncomputable def LeastDifferingSparseBlocks.case3Data
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference : LeastDifferingSparseBlocks [] leftBlocks rightBlocks)
    {leftWord rightWord : Word Nat} {earlier later : Nat}
    (leftRendered : renderGapBlocks leftBlocks = leftWord.toList)
    (rightRendered : renderGapBlocks rightBlocks = rightWord.toList)
    (rightNoCrossing :
      ¬ Has27Crossing
        (gapBlockMarkers leftBlocks) (renderGapBlocks rightBlocks))
    (rightNoAdjacent :
      ¬ Has27AdjacentPair
        (gapBlockMarkers leftBlocks) (renderGapBlocks rightBlocks))
    (leftSeconds : difference.leftBlock.seconds = [earlier])
    (rightSeconds : difference.rightBlock.seconds = [later])
    (earlierBeforeLater :
      EarlierIn (gapBlockMarkers leftBlocks) earlier later)
    (laterBeforeCurrent :
      EarlierIn (gapBlockMarkers leftBlocks)
        later difference.leftBlock.marker) :
    F9BridgeCaseData leftWord rightWord := by
  let commonRendered := renderGapBlocks difference.commonPrefix
  let current := difference.leftBlock.marker
  let leftSuffix := renderGapBlocks difference.leftTail
  let rightSuffix := renderGapBlocks difference.rightTail
  have earlierAllowed :
      earlier ∈ current ::
        seenAfterGapBlocks [] difference.commonPrefix := by
    exact difference.leftChoice.selected_allowed_of_eq_singleton leftSeconds
  have laterAllowed :
      later ∈ current ::
        seenAfterGapBlocks [] difference.commonPrefix := by
    exact difference.rightChoice.selected_allowed_of_eq_singleton rightSeconds
  let split := Classical.choice <|
    difference.orderedRenderedPrefixSplit
      leftSeconds rightSeconds earlierBeforeLater laterBeforeCurrent
  let firstZone := split.before ++ earlier :: split.between
  let bridgeTail := split.after ++ [current]
  let bridgeZone := later :: bridgeTail
  have leftBaseShape :
      leftWord.toList =
        commonRendered ++ current :: earlier :: leftSuffix := by
    calc
      leftWord.toList = renderGapBlocks leftBlocks := leftRendered.symm
      _ = difference.renderedPrefix ++
            difference.leftBlock.seconds ++
            renderGapBlocks difference.leftTail :=
        difference.left_render_eq
      _ = commonRendered ++ current :: earlier :: leftSuffix := by
        simp [LeastDifferingSparseBlocks.renderedPrefix,
          commonRendered, current, leftSuffix, leftSeconds,
          List.append_assoc]
  have rightBaseShape :
      rightWord.toList =
        commonRendered ++ current :: later :: rightSuffix := by
    calc
      rightWord.toList = renderGapBlocks rightBlocks := rightRendered.symm
      _ = difference.renderedPrefix ++
            difference.rightBlock.seconds ++
            renderGapBlocks difference.rightTail :=
        difference.right_render_eq
      _ = commonRendered ++ current :: later :: rightSuffix := by
        simp [LeastDifferingSparseBlocks.renderedPrefix,
          commonRendered, current, rightSuffix, rightSeconds,
          List.append_assoc]
  have crossingShape :
      renderGapBlocks rightBlocks =
        firstZone ++ [later] ++ bridgeTail ++ [later] ++ rightSuffix := by
    calc
      renderGapBlocks rightBlocks = rightWord.toList := rightRendered
      _ = commonRendered ++ current :: later :: rightSuffix :=
        rightBaseShape
      _ = firstZone ++ [later] ++ bridgeTail ++ [later] ++
            rightSuffix := by
        simp [commonRendered, split.render_eq, firstZone, bridgeTail,
          List.append_assoc]
  have firstZoneLaterAbsent : later ∉ firstZone := by
    simpa [firstZone] using split.later_not_mem_firstZone
  have firstZoneChronology :
      ∀ letter, letter ∈ firstZone →
        EarlierIn (gapBlockMarkers leftBlocks) letter later := by
    simpa [firstZone] using split.firstZone_chronology
  have bridgeAbsentFromFirst :
      ∀ letter, letter ∈ bridgeZone → letter ∉ firstZone := by
    simpa [bridgeZone] using
      (noCrossing_forces_bridge_disjoint
        rightNoCrossing firstZoneLaterAbsent firstZoneChronology
        crossingShape)
  have bridgeSeen :
      ∀ letter, letter ∈ bridgeZone →
        letter ∈ current ::
          seenAfterGapBlocks [] difference.commonPrefix := by
    intro letter member
    rcases List.mem_cons.mp member with atLater | inBridgeTail
    · simpa [atLater] using laterAllowed
    · change letter ∈ split.after ++ [current] at inBridgeTail
      rcases List.mem_append.mp inBridgeTail with inAfter | atCurrent
      · apply difference.mem_tailSeen_of_mem_renderedPrefix
        rw [split.render_eq]
        simp [inAfter]
      · have equal : letter = current := by simpa using atCurrent
        subst letter
        exact List.Mem.head _
  by_cases betweenEmpty : split.between = []
  · let ordinaryZone := split.before
    let activeLetter := earlier
    let freshLetter :=
      f9FreshLetter ordinaryZone activeLetter bridgeZone
    have commonShape :
        commonRendered =
          ordinaryZone ++ activeLetter :: later :: split.after := by
      simp [commonRendered, split.render_eq, betweenEmpty,
        ordinaryZone, activeLetter, List.append_assoc]
    have activeAbsent : activeLetter ∉ ordinaryZone := by
      simpa [ordinaryZone, activeLetter] using split.earlier_not_mem_before
    have ordinaryInFirst :
        ∀ letter, letter ∈ ordinaryZone → letter ∈ firstZone := by
      intro letter member
      exact List.mem_append_left _ <| by
        simpa [ordinaryZone] using member
    have activeInFirst : activeLetter ∈ firstZone := by
      simp [firstZone, betweenEmpty, activeLetter]
    have bridgeDisjoint :
        ∀ letter, letter ∈ bridgeZone →
          letter ∉ ordinaryZone ∧ letter ≠ activeLetter := by
      intro letter member
      have outside := bridgeAbsentFromFirst letter member
      constructor
      · intro inOrdinary
        exact outside (ordinaryInFirst letter inOrdinary)
      · intro equal
        subst letter
        exact outside activeInFirst
    have leftShape :
        leftWord.toList =
          ordinaryZone ++ activeLetter :: bridgeZone ++
            earlier :: leftSuffix := by
      simpa [commonShape, ordinaryZone, activeLetter, bridgeZone,
        bridgeTail, List.append_assoc] using leftBaseShape
    have rightShape :
        rightWord.toList =
          ordinaryZone ++ activeLetter :: bridgeZone ++
            later :: rightSuffix := by
      simpa [commonShape, ordinaryZone, activeLetter, bridgeZone,
        bridgeTail, List.append_assoc] using rightBaseShape
    have ordinarySeen :
        ∀ letter, letter ∈ ordinaryZone →
          letter ∈ current ::
            seenAfterGapBlocks [] difference.commonPrefix := by
      intro letter member
      apply difference.mem_tailSeen_of_mem_renderedPrefix
      change letter ∈ commonRendered
      rw [commonShape]
      exact List.mem_append_left _ member
    have activeSeen :
        activeLetter ∈ current ::
          seenAfterGapBlocks [] difference.commonPrefix := by
      simpa [activeLetter] using earlierAllowed
    have leftHeadOutside :
        ∀ head tail, leftSuffix = head :: tail →
          head ∉ ordinaryZone ∧
            head ≠ activeLetter ∧ head ∉ bridgeZone := by
      intro head tail shape
      apply difference.leftTailSparse.render_head_outside_zones
        (ordinaryZone := ordinaryZone) (bridgeZone := bridgeZone)
        (activeLetter := activeLetter)
      · simpa [leftSuffix] using shape
      · exact ordinarySeen
      · exact activeSeen
      · exact bridgeSeen
    have rightHeadOutside :
        ∀ head tail, rightSuffix = head :: tail →
          head ∉ ordinaryZone ∧
            head ≠ activeLetter ∧ head ∉ bridgeZone := by
      intro head tail shape
      apply difference.rightTailSparse.render_head_outside_zones
        (ordinaryZone := ordinaryZone) (bridgeZone := bridgeZone)
        (activeLetter := activeLetter)
      · simpa [rightSuffix] using shape
      · exact ordinarySeen
      · exact activeSeen
      · exact bridgeSeen
    have freshOutside :=
      f9FreshLetter_outside ordinaryZone activeLetter bridgeZone
    exact F9BridgeCaseData.ofListShapes
      freshLetter ordinaryZone activeLetter bridgeZone
      earlier later leftSuffix rightSuffix
      leftShape rightShape activeAbsent bridgeDisjoint
      (Or.inr rfl) (by simp [bridgeZone])
      leftHeadOutside rightHeadOutside freshOutside
  · let terminalSplit :=
      exists_append_singleton_of_ne_nil split.between betweenEmpty
    let middle : List Nat := Classical.choose terminalSplit
    have finalSplit :
        ∃ final, split.between = middle ++ [final] :=
      Classical.choose_spec terminalSplit
    let activeLetter : Nat := Classical.choose finalSplit
    have betweenShape : split.between = middle ++ [activeLetter] :=
      Classical.choose_spec finalSplit
    let ordinaryZone := split.before ++ earlier :: middle
    let freshLetter :=
      f9FreshLetter ordinaryZone activeLetter bridgeZone
    have commonShape :
        commonRendered =
          ordinaryZone ++ activeLetter :: later :: split.after := by
      simp [commonRendered, split.render_eq, betweenShape,
        ordinaryZone, List.append_assoc]
    have activeInFirst : activeLetter ∈ firstZone := by
      simp [firstZone, betweenShape]
    have activeOrder :
        EarlierIn (gapBlockMarkers leftBlocks) activeLetter later :=
      firstZoneChronology activeLetter activeInFirst
    have adjacentShape :
        renderGapBlocks rightBlocks =
          ordinaryZone ++ [activeLetter, later] ++ bridgeTail ++
            [later] ++ rightSuffix := by
      simpa [firstZone, betweenShape, ordinaryZone,
        List.append_assoc] using crossingShape
    have activeAbsent : activeLetter ∉ ordinaryZone :=
      noAdjacentPair_forces_active_not_mem
        rightNoAdjacent activeOrder adjacentShape
    have ordinaryInFirst :
        ∀ letter, letter ∈ ordinaryZone → letter ∈ firstZone := by
      intro letter member
      change
        letter ∈ split.before ++ earlier :: split.between
      rw [betweenShape]
      have extended : letter ∈ ordinaryZone ++ [activeLetter] :=
        List.mem_append_left [activeLetter] member
      simpa [ordinaryZone, List.append_assoc] using extended
    have bridgeDisjoint :
        ∀ letter, letter ∈ bridgeZone →
          letter ∉ ordinaryZone ∧ letter ≠ activeLetter := by
      intro letter member
      have outside := bridgeAbsentFromFirst letter member
      constructor
      · intro inOrdinary
        exact outside (ordinaryInFirst letter inOrdinary)
      · intro equal
        subst letter
        exact outside activeInFirst
    have leftShape :
        leftWord.toList =
          ordinaryZone ++ activeLetter :: bridgeZone ++
            earlier :: leftSuffix := by
      simpa [commonShape, ordinaryZone, bridgeZone, bridgeTail,
        List.append_assoc] using leftBaseShape
    have rightShape :
        rightWord.toList =
          ordinaryZone ++ activeLetter :: bridgeZone ++
            later :: rightSuffix := by
      simpa [commonShape, ordinaryZone, bridgeZone, bridgeTail,
        List.append_assoc] using rightBaseShape
    have ordinarySeen :
        ∀ letter, letter ∈ ordinaryZone →
          letter ∈ current ::
            seenAfterGapBlocks [] difference.commonPrefix := by
      intro letter member
      apply difference.mem_tailSeen_of_mem_renderedPrefix
      change letter ∈ commonRendered
      rw [commonShape]
      exact List.mem_append_left _ member
    have activeSeen :
        activeLetter ∈ current ::
          seenAfterGapBlocks [] difference.commonPrefix := by
      apply difference.mem_tailSeen_of_mem_renderedPrefix
      change activeLetter ∈ commonRendered
      rw [commonShape]
      exact List.mem_append_right ordinaryZone <| by simp
    have leftHeadOutside :
        ∀ head tail, leftSuffix = head :: tail →
          head ∉ ordinaryZone ∧
            head ≠ activeLetter ∧ head ∉ bridgeZone := by
      intro head tail shape
      apply difference.leftTailSparse.render_head_outside_zones
        (ordinaryZone := ordinaryZone) (bridgeZone := bridgeZone)
        (activeLetter := activeLetter)
      · simpa [leftSuffix] using shape
      · exact ordinarySeen
      · exact activeSeen
      · exact bridgeSeen
    have rightHeadOutside :
        ∀ head tail, rightSuffix = head :: tail →
          head ∉ ordinaryZone ∧
            head ≠ activeLetter ∧ head ∉ bridgeZone := by
      intro head tail shape
      apply difference.rightTailSparse.render_head_outside_zones
        (ordinaryZone := ordinaryZone) (bridgeZone := bridgeZone)
        (activeLetter := activeLetter)
      · simpa [rightSuffix] using shape
      · exact ordinarySeen
      · exact activeSeen
      · exact bridgeSeen
    have freshOutside :=
      f9FreshLetter_outside ordinaryZone activeLetter bridgeZone
    exact F9BridgeCaseData.ofListShapes
      freshLetter ordinaryZone activeLetter bridgeZone
      earlier later leftSuffix rightSuffix
      leftShape rightShape activeAbsent bridgeDisjoint
      (Or.inl <| by simp [ordinaryZone]) (by simp [bridgeZone])
      leftHeadOutside rightHeadOutside freshOutside

namespace F9Case1Data

def toSeparationCertificate
    {left right : Word Nat} (data : F9Case1Data left right) :
    F9EmptySeparationCertificate left right where
  valuation := f9ZoneValuation data.ordinaryZone data.activeLetter []
  freshLetter := data.freshLetter
  prefixWord :=
    f9CasePrefixWord data.ordinaryZone data.activeLetter []
  leftTail := data.leftTail
  rightTail := data.rightTail
  killed := data.killed
  leftExtended_eq := data.leftExtended_eq
  rightExtended_eq := data.rightExtended_eq
  prefixActive := f9_eval_casePrefixWord
    data.ordinaryZone data.activeLetter [] data.activeAbsent
    (by simp)
  killedValue := by
    rcases data.killedZone with ordinary | active
    · exact Or.inr <| f9ZoneValuation_of_ordinary
        data.ordinaryZone [] data.activeLetter data.killed ordinary
    · exact Or.inl <| by
        rw [active]
        exact f9ZoneValuation_of_active
          data.ordinaryZone [] data.activeLetter data.activeAbsent
  leftFresh := f9ZoneValuation_of_fresh
    data.ordinaryZone [] data.activeLetter data.leftTail.head
    data.leftTailOutside.1 data.leftTailOutside.2 (by simp)
  rightFresh := f9ZoneValuation_of_fresh
    data.ordinaryZone [] data.activeLetter data.rightTail.head
    data.rightTailOutside.1 data.rightTailOutside.2 (by simp)

theorem separation
    {left right : Word Nat} (data : F9Case1Data left right) :
    F9SeparationCertificate left right :=
  Or.inl ⟨data.toSeparationCertificate⟩

end F9Case1Data

namespace F9BridgeCaseData

def toSeparationCertificate
    {left right : Word Nat} (data : F9BridgeCaseData left right) :
    F9BridgeSeparationCertificate left right where
  valuation :=
    f9ZoneValuation data.ordinaryZone data.activeLetter data.bridgeZone
  freshLetter := data.freshLetter
  prefixWord :=
    f9CasePrefixWord data.ordinaryZone data.activeLetter data.bridgeZone
  leftTail := data.leftTail
  rightTail := data.rightTail
  killed := data.killed
  preserved := data.preserved
  leftExtended_eq := data.leftExtended_eq
  rightExtended_eq := data.rightExtended_eq
  prefixActive := f9_eval_casePrefixWord
    data.ordinaryZone data.activeLetter data.bridgeZone
    data.activeAbsent data.bridgeDisjoint
  killedValue := by
    rcases data.killedZone with ordinary | active
    · exact Or.inr <| f9ZoneValuation_of_ordinary
        data.ordinaryZone data.bridgeZone data.activeLetter
        data.killed ordinary
    · exact Or.inl <| by
        rw [active]
        exact f9ZoneValuation_of_active
          data.ordinaryZone data.bridgeZone data.activeLetter
          data.activeAbsent
  preservedValue := f9ZoneValuation_of_bridge
    data.ordinaryZone data.bridgeZone data.activeLetter data.preserved
    (data.bridgeDisjoint data.preserved data.preservedBridge).1
    (data.bridgeDisjoint data.preserved data.preservedBridge).2
    data.preservedBridge
  leftFresh := f9ZoneValuation_of_fresh
    data.ordinaryZone data.bridgeZone data.activeLetter data.leftTail.head
    data.leftTailOutside.1 data.leftTailOutside.2.1
    data.leftTailOutside.2.2
  rightFresh := f9ZoneValuation_of_fresh
    data.ordinaryZone data.bridgeZone data.activeLetter data.rightTail.head
    data.rightTailOutside.1 data.rightTailOutside.2.1
    data.rightTailOutside.2.2

theorem separation
    {left right : Word Nat} (data : F9BridgeCaseData left right) :
    F9SeparationCertificate left right :=
  Or.inr ⟨data.toSeparationCertificate⟩

end F9BridgeCaseData

/-! ## The exact remaining case-extraction boundary -/

/-- Reverse a least-difference certificate without repeating the list search.
This is used only to orient the paper cases so that the selected or earlier
letter is on the left. -/
private def swapLeastDifferingSparseBlocks
    {seen : List Nat}
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    (difference :
      LeastDifferingSparseBlocks seen leftBlocks rightBlocks) :
    LeastDifferingSparseBlocks seen rightBlocks leftBlocks where
  commonPrefix := difference.commonPrefix
  leftBlock := difference.rightBlock
  rightBlock := difference.leftBlock
  leftTail := difference.rightTail
  rightTail := difference.leftTail
  left_eq := difference.right_eq
  right_eq := difference.left_eq
  sameMarker := difference.sameMarker.symm
  differentSeconds := by
    intro equal
    exact difference.differentSeconds equal.symm
  tailMarkers_eq := difference.tailMarkers_eq.symm
  leftPrefixSparse := difference.rightPrefixSparse
  rightPrefixSparse := difference.leftPrefixSparse
  markerFresh := by
    simpa only [difference.sameMarker] using difference.markerFresh
  leftChoice := by
    simpa only [difference.sameMarker] using difference.rightChoice
  rightChoice := by
    simpa only [difference.sameMarker] using difference.leftChoice
  leftTailSparse := by
    simpa only [difference.sameMarker] using difference.rightTailSparse
  rightTailSparse := by
    simpa only [difference.sameMarker] using difference.leftTailSparse

/-- Expose the constructor indices of an oriented sparse choice as ordinary
equalities.  Keeping the indexed elimination here, while the two second lists
are variables, avoids asking the dispatcher to rewrite structure projections
during dependent case analysis. -/
private theorem orientedChoiceDifference_explicitCases
    {markers : List Nat} {current : Nat}
    {leftSeconds rightSeconds : List Nat}
    (oriented :
      OrientedChoiceDifference
        markers current leftSeconds rightSeconds) :
    (∃ selected,
      leftSeconds = [selected] ∧ rightSeconds = []) ∨
    (∃ selected,
      leftSeconds = [selected] ∧ rightSeconds = [current]) ∨
    (∃ earlier later,
      leftSeconds = [earlier] ∧ rightSeconds = [later] ∧
        EarlierIn markers earlier later ∧
          EarlierIn markers later current) := by
  cases oriented with
  | selectedEmpty selected atOrBefore =>
      exact Or.inl ⟨selected, rfl, rfl⟩
  | selectedCurrent selected beforeCurrent =>
      exact Or.inr <| Or.inl ⟨selected, rfl, rfl⟩
  | orderedSelected earlier later earlierBeforeLater laterBeforeCurrent =>
      exact Or.inr <| Or.inr ⟨earlier, later, rfl, rfl,
        earlierBeforeLater, laterBeforeCurrent⟩

def F9PaperCasesExtracted : Prop :=
  ∀ {leftBlocks rightBlocks : List S5_870.FirstOccurrenceGapBlock}
      {leftWord rightWord : Word Nat},
    BetaCanonicalBlocks leftBlocks →
    BetaCanonicalBlocks rightBlocks →
    S5_870.renderGapBlocks leftBlocks = leftWord.toList →
    S5_870.renderGapBlocks rightBlocks = rightWord.toList →
    S5_870.gapBlockMarkers leftBlocks =
      S5_870.gapBlockMarkers rightBlocks →
    leftBlocks ≠ rightBlocks →
      Nonempty (F9Case1Data leftWord rightWord) ∨
      Nonempty (F9Case1Data rightWord leftWord) ∨
      Nonempty (F9BridgeCaseData leftWord rightWord) ∨
      Nonempty (F9BridgeCaseData rightWord leftWord)

/-- Proposition 27.3's three least-difference cases, with symmetry made
explicit.  Each branch produces the literal valuation payload consumed by the
already verified semantic certificates above. -/
theorem f9PaperCasesExtracted : F9PaperCasesExtracted := by
  intro leftBlocks rightBlocks leftWord rightWord
    leftCanonical rightCanonical leftRendered rightRendered
    sameMarkers different
  obtain ⟨least⟩ :=
    exists_leastDifferingBetaBlocks
      leftCanonical rightCanonical sameMarkers different
  let difference := least.difference
  have rightNoCrossingOnLeft :
      ¬ Has27Crossing
        (gapBlockMarkers leftBlocks) (renderGapBlocks rightBlocks) := by
    rw [sameMarkers]
    exact least.rightNoCrossing
  have rightNoAdjacentOnLeft :
      ¬ Has27AdjacentPair
        (gapBlockMarkers leftBlocks) (renderGapBlocks rightBlocks) := by
    rw [sameMarkers]
    exact least.rightNoAdjacentPair
  have leftNoCrossingOnRight :
      ¬ Has27Crossing
        (gapBlockMarkers rightBlocks) (renderGapBlocks leftBlocks) := by
    rw [← sameMarkers]
    exact least.leftNoCrossing
  have leftNoAdjacentOnRight :
      ¬ Has27AdjacentPair
        (gapBlockMarkers rightBlocks) (renderGapBlocks leftBlocks) := by
    rw [← sameMarkers]
    exact least.leftNoAdjacentPair
  rcases difference.orientedChoiceDifference with forward | reverse
  · rcases orientedChoiceDifference_explicitCases forward with
      ⟨selected, leftSeconds, rightSeconds⟩ |
      ⟨selected, leftSeconds, rightSeconds⟩ |
      ⟨earlier, later, leftSeconds, rightSeconds,
        earlierBeforeLater, laterBeforeCurrent⟩
    · exact Or.inl ⟨difference.case1Data
        leftRendered rightRendered leftSeconds rightSeconds⟩
    · exact Or.inr <| Or.inr <| Or.inl ⟨difference.case2Data
        leftRendered rightRendered rightNoAdjacentOnLeft
        leftSeconds rightSeconds⟩
    · exact Or.inr <| Or.inr <| Or.inl ⟨difference.case3Data
        leftRendered rightRendered rightNoCrossingOnLeft
        rightNoAdjacentOnLeft leftSeconds rightSeconds
        earlierBeforeLater laterBeforeCurrent⟩
  · let reverseDifference :=
      swapLeastDifferingSparseBlocks difference
    have reverseOriented :
        OrientedChoiceDifference
          (gapBlockMarkers rightBlocks)
          reverseDifference.leftBlock.marker
          reverseDifference.leftBlock.seconds
          reverseDifference.rightBlock.seconds := by
      simpa only [sameMarkers, difference.sameMarker,
        reverseDifference, swapLeastDifferingSparseBlocks] using reverse
    rcases orientedChoiceDifference_explicitCases reverseOriented with
      ⟨selected, leftSeconds, rightSeconds⟩ |
      ⟨selected, leftSeconds, rightSeconds⟩ |
      ⟨earlier, later, leftSeconds, rightSeconds,
        earlierBeforeLater, laterBeforeCurrent⟩
    · exact Or.inr <| Or.inl ⟨reverseDifference.case1Data
        rightRendered leftRendered leftSeconds rightSeconds⟩
    · exact Or.inr <| Or.inr <| Or.inr ⟨reverseDifference.case2Data
        rightRendered leftRendered leftNoAdjacentOnRight
        leftSeconds rightSeconds⟩
    · exact Or.inr <| Or.inr <| Or.inr ⟨reverseDifference.case3Data
        rightRendered leftRendered leftNoCrossingOnRight
        leftNoAdjacentOnRight leftSeconds rightSeconds
        earlierBeforeLater laterBeforeCurrent⟩

/-- Once the literal Cases 1/2/3 data have been extracted, the semantic
boundary from `Order6SporadicSection27F9Uniqueness` is discharged. -/
theorem f9SeparatesDistinctBetaCanonicalBlocks_of_paperCases
    (extracts : F9PaperCasesExtracted) :
    F9SeparatesDistinctBetaCanonicalBlocks := by
  intro leftBlocks rightBlocks leftWord rightWord
    leftCanonical rightCanonical leftRendered rightRendered
    sameMarkers different
  rcases extracts leftCanonical rightCanonical leftRendered rightRendered
      sameMarkers different with
    ⟨leftCaseOne⟩ | ⟨rightCaseOne⟩ | ⟨leftBridge⟩ | ⟨rightBridge⟩
  · rcases leftCaseOne with ⟨leftCaseOne⟩
    exact Or.inl leftCaseOne.separation
  · rcases rightCaseOne with ⟨rightCaseOne⟩
    exact Or.inr rightCaseOne.separation
  · rcases leftBridge with ⟨leftBridge⟩
    exact Or.inl leftBridge.separation
  · rcases rightBridge with ⟨rightBridge⟩
    exact Or.inr rightBridge.separation

/-- The pinned F9 separator distinguishes every pair of distinct beta
canonical block words with the same first-occurrence marker sequence. -/
theorem f9SeparatesDistinctBetaCanonicalBlocks :
    F9SeparatesDistinctBetaCanonicalBlocks :=
  f9SeparatesDistinctBetaCanonicalBlocks_of_paperCases
    f9PaperCasesExtracted

end SemigroupBasis.CoRoots.Order6SporadicSection27
