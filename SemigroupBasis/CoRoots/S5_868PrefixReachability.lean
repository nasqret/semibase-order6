import SemigroupBasis.CoRoots.S5_868CompleteRepresentative

namespace SemigroupBasis.CoRoots.S5_868

open SemigroupBasis

/-! ## Nonempty-word contexts for exact prefix alignment -/

/-- Prepend a possibly empty raw list to a nonempty word. -/
def prefixPrependLetters : List Nat → Word Nat → Word Nat
  | [], word => word
  | head :: tail, word => ⟨head, tail⟩ ++ word

@[simp]
theorem prefixPrependLetters_toList
    (letters : List Nat) (word : Word Nat) :
    (prefixPrependLetters letters word).toList =
      letters ++ word.toList := by
  cases letters with
  | nil => simp [prefixPrependLetters]
  | cons head tail =>
      simp [prefixPrependLetters, Word.toList_append, Word.toList]

/-- Append a possibly empty raw list to a nonempty word. -/
def prefixAppendLetters : Word Nat → List Nat → Word Nat
  | word, [] => word
  | word, head :: tail => word ++ ⟨head, tail⟩

@[simp]
theorem prefixAppendLetters_toList
    (word : Word Nat) (letters : List Nat) :
    (prefixAppendLetters word letters).toList =
      word.toList ++ letters := by
  cases letters with
  | nil => simp [prefixAppendLetters]
  | cons head tail =>
      simp [prefixAppendLetters, Word.toList_append, Word.toList]

/-- Place a nonempty core word in possibly empty raw left and right
contexts. -/
def prefixContext
    (left : List Nat) (core : Word Nat) (right : List Nat) :
    Word Nat :=
  prefixAppendLetters (prefixPrependLetters left core) right

@[simp]
theorem prefixContext_toList
    (left : List Nat) (core : Word Nat) (right : List Nat) :
    (prefixContext left core right).toList =
      left ++ core.toList ++ right := by
  simp [prefixContext, List.append_assoc]

theorem derivesPrefixPrependLetters
    (letters : List Nat) {source target : Word Nat}
    (derivation : Derives basis source target) :
    Derives basis
      (prefixPrependLetters letters source)
      (prefixPrependLetters letters target) := by
  cases letters with
  | nil => simpa [prefixPrependLetters] using derivation
  | cons head tail =>
      simpa [prefixPrependLetters] using
        Derives.prepend ⟨head, tail⟩ derivation

theorem derivesPrefixAppendLetters
    {source target : Word Nat}
    (derivation : Derives basis source target)
    (letters : List Nat) :
    Derives basis
      (prefixAppendLetters source letters)
      (prefixAppendLetters target letters) := by
  cases letters with
  | nil => simpa [prefixAppendLetters] using derivation
  | cons head tail =>
      simpa [prefixAppendLetters] using
        Derives.appendRight derivation ⟨head, tail⟩

/-- Equational derivations are closed under the exact raw-list contexts
used by the prefix induction. -/
theorem derivesPrefixContext
    (left right : List Nat) {source target : Word Nat}
    (derivation : Derives basis source target) :
    Derives basis
      (prefixContext left source right)
      (prefixContext left target right) :=
  derivesPrefixAppendLetters
    (derivesPrefixPrependLetters left derivation) right

/-! ## The two local algebraic prefix moves -/

/-- If the required edge `previous → next` already occurs inside the
matched prefix, duplicate the closed walk from that occurrence back to the
current prefix endpoint. The new copy starts with `next`. -/
theorem existsPrefixAlignment_of_earlierEdge
    (current : Word Nat) (left middle trailing : List Nat)
    (previous next : Nat)
    (shape :
      current.toList =
        left ++ previous :: next :: middle ++ previous :: trailing) :
    ∃ expanded : Word Nat, ∃ suffix : List Nat,
      Derives basis current expanded ∧
        expanded.toList =
          (left ++ previous :: next :: middle) ++
            previous :: next :: suffix := by
  let anchor := Word.singleton previous
  let excursion : Word Nat := ⟨next, middle⟩
  have excursionList : excursion.toList = next :: middle := rfl
  let sourceCore := (anchor ++ excursion) ++ anchor
  let targetCore := (((anchor ++ excursion) ++ anchor) ++ excursion) ++
    anchor
  let sourceWord := prefixContext left sourceCore trailing
  let targetWord := prefixContext left targetCore trailing
  have currentEq : current = sourceWord := by
    apply Word.toList_injective
    rw [shape]
    simp only [sourceWord, prefixContext_toList, sourceCore,
      Word.toList_append, anchor, Word.toList_singleton, excursionList,
      List.cons_append, List.nil_append, List.append_assoc]
  have derivation : Derives basis current targetWord := by
    rw [currentEq]
    exact derivesPrefixContext left trailing
      (derivesSandwichExpansion anchor excursion)
  refine ⟨targetWord, middle ++ previous :: trailing, derivation, ?_⟩
  simp only [targetWord, prefixContext_toList, targetCore,
    Word.toList_append, anchor, Word.toList_singleton, excursionList,
    List.cons_append, List.nil_append, List.append_assoc]

/-- A terminal self-edge in the already matched prefix is exposed with
`x² = x³`. This is the empty-excursion boundary case of the preceding
move. -/
theorem existsPrefixAlignment_of_terminalSelfEdge
    (current : Word Nat) (left trailing : List Nat)
    (previous : Nat)
    (shape :
      current.toList =
        left ++ previous :: previous :: trailing) :
    ∃ expanded : Word Nat, ∃ suffix : List Nat,
      Derives basis current expanded ∧
        expanded.toList =
          (left ++ [previous]) ++
            previous :: previous :: suffix := by
  let anchor := Word.singleton previous
  let sourceCore := anchor ++ anchor
  let targetCore := (anchor ++ anchor) ++ anchor
  let sourceWord := prefixContext left sourceCore trailing
  let targetWord := prefixContext left targetCore trailing
  have currentEq : current = sourceWord := by
    apply Word.toList_injective
    rw [shape]
    simp only [sourceWord, prefixContext_toList, sourceCore,
      Word.toList_append, anchor, Word.toList_singleton,
      List.cons_append, List.nil_append, List.append_assoc]
  have derivation : Derives basis current targetWord := by
    rw [currentEq]
    exact derivesPrefixContext left trailing
      (derivesPowerExpansion anchor)
  refine ⟨targetWord, trailing, derivation, ?_⟩
  simp only [targetWord, prefixContext_toList, targetCore,
    Word.toList_append, anchor, Word.toList_singleton,
    List.cons_append, List.nil_append, List.append_assoc]

/-- Once two later copies of `previous → next` have been exposed, the
graph-switch law moves the corresponding `next`-excursion directly after
the matched prefix endpoint. If the first anchored gap is empty, the
derived endpoint-transfer law performs the same move. -/
theorem existsPrefixAlignment_of_repeatedLaterEdge
    (current : Word Nat) (stem gap between trailing : List Nat)
    (previous next : Nat)
    (shape :
      current.toList =
        stem ++ previous :: gap ++
          previous :: next :: between ++
            previous :: next :: trailing) :
    ∃ expanded : Word Nat, ∃ suffix : List Nat,
      Derives basis current expanded ∧
        expanded.toList =
          stem ++ previous :: next :: suffix := by
  let anchor := Word.singleton previous
  let nextExcursion : Word Nat := ⟨next, between⟩
  have nextExcursionList : nextExcursion.toList = next :: between := rfl
  cases gap with
  | nil =>
      let sourceCore := ((anchor ++ anchor) ++ nextExcursion) ++ anchor
      let targetCore := ((anchor ++ nextExcursion) ++ anchor) ++ anchor
      let sourceWord :=
        prefixContext stem sourceCore (next :: trailing)
      let targetWord :=
        prefixContext stem targetCore (next :: trailing)
      have currentEq : current = sourceWord := by
        apply Word.toList_injective
        rw [shape]
        simp only [sourceWord, prefixContext_toList, sourceCore,
          Word.toList_append, anchor, Word.toList_singleton,
          nextExcursionList, List.cons_append, List.nil_append,
          List.append_assoc]
      have derivation : Derives basis current targetWord := by
        rw [currentEq]
        exact derivesPrefixContext stem (next :: trailing)
          (derivesEndpointTransfer anchor nextExcursion)
      refine
        ⟨targetWord,
          between ++ previous :: previous :: next :: trailing,
          derivation, ?_⟩
      simp only [targetWord, prefixContext_toList, targetCore,
        Word.toList_append, anchor, Word.toList_singleton,
        nextExcursionList, List.cons_append, List.nil_append,
        List.append_assoc]
  | cons gapHead gapTail =>
      let firstExcursion : Word Nat := ⟨gapHead, gapTail⟩
      have firstExcursionList :
          firstExcursion.toList = gapHead :: gapTail := rfl
      let sourceCore :=
        (((anchor ++ firstExcursion) ++ anchor) ++ nextExcursion) ++
          anchor
      let targetCore :=
        (((anchor ++ nextExcursion) ++ anchor) ++ firstExcursion) ++
          anchor
      let sourceWord :=
        prefixContext stem sourceCore (next :: trailing)
      let targetWord :=
        prefixContext stem targetCore (next :: trailing)
      have currentEq : current = sourceWord := by
        apply Word.toList_injective
        rw [shape]
        simp only [sourceWord, prefixContext_toList, sourceCore,
          Word.toList_append, anchor, Word.toList_singleton,
          firstExcursionList, nextExcursionList, List.cons_append,
          List.nil_append, List.append_assoc]
      have derivation : Derives basis current targetWord := by
        rw [currentEq]
        exact derivesPrefixContext stem (next :: trailing)
          (derivesAnchoredLoopSwap
            anchor firstExcursion nextExcursion)
      refine
        ⟨targetWord,
          between ++ previous :: gapHead :: gapTail ++
            previous :: next :: trailing,
          derivation, ?_⟩
      simp only [targetWord, prefixContext_toList, targetCore,
        Word.toList_append, anchor, Word.toList_singleton,
        firstExcursionList, nextExcursionList, List.cons_append,
        List.nil_append, List.append_assoc]

/-! ## Exact induction boundary -/

/-- The one-step graph-combinatorial statement required by Trahtman's
prefix induction. Every assumption is produced by the induction invariant:
the current word is indecomposable, literally begins with `prefix ·
previous`, and contains the next target edge in its marked graph. -/
def PrefixEdgeExtensionStep : Prop :=
  ∀ current : Word Nat,
    ∀ stem : List Nat,
      ∀ previous next : Nat,
        ∀ currentSuffix : List Nat,
          TrahtmanIndecomposable current →
            current.toList = stem ++ previous :: currentSuffix →
              (previous, next) ∈ current.adjacentPairs →
                ∃ expanded : Word Nat, ∃ suffix : List Nat,
                  Derives basis current expanded ∧
                    expanded.toList =
                      stem ++ previous :: next :: suffix

/-- Exact remaining graph-exposure statement in the paper's one-step
argument. Either the desired edge has already been moved to the prefix, or
two later copies have been exposed so `graphSwitchLaw` (and its empty-gap
endpoint-transfer case) can move it there. -/
def PrefixEdgeExposure : Prop :=
  ∀ current : Word Nat,
    ∀ stem : List Nat,
      ∀ previous next : Nat,
        ∀ currentSuffix : List Nat,
          TrahtmanIndecomposable current →
            current.toList = stem ++ previous :: currentSuffix →
              (previous, next) ∈ current.adjacentPairs →
                ∃ exposed : Word Nat,
                  Derives basis current exposed ∧
                    ((∃ suffix : List Nat,
                        exposed.toList =
                          stem ++ previous :: next :: suffix) ∨
                      ∃ gap between trailing : List Nat,
                        exposed.toList =
                          stem ++ previous :: gap ++
                            previous :: next :: between ++
                              previous :: next :: trailing)

/-- `PrefixEdgeExposure` strictly discharges the algebraic part of the
one-step obligation. -/
theorem prefixEdgeExtensionStep_of_exposure
    (exposure : PrefixEdgeExposure) :
    PrefixEdgeExtensionStep := by
  intro current stem previous next currentSuffix
    currentIndecomposable currentShape currentEdge
  rcases exposure current stem previous next currentSuffix
      currentIndecomposable currentShape currentEdge with
    ⟨exposed, currentExposed, aligned | repeated⟩
  · rcases aligned with ⟨suffix, exposedShape⟩
    exact ⟨exposed, suffix, currentExposed, exposedShape⟩
  · rcases repeated with ⟨gap, between, trailing, exposedShape⟩
    rcases existsPrefixAlignment_of_repeatedLaterEdge
        exposed stem gap between trailing previous next
        exposedShape with
      ⟨aligned, suffix, exposedAligned, alignedShape⟩
    exact
      ⟨aligned, suffix, currentExposed.trans exposedAligned,
        alignedShape⟩

private def prefixAdjacentPairsList :
    List Nat → List (Nat × Nat)
  | [] => []
  | first :: rest => Word.adjacentPairsFrom first rest

private theorem mem_prefixAdjacentPairsList_iff_exists_split
    (source target : Nat) :
    ∀ letters : List Nat,
      (source, target) ∈ prefixAdjacentPairsList letters ↔
        ∃ before after,
          letters = before ++ source :: target :: after
  | [] => by
      constructor
      · simp [prefixAdjacentPairsList]
      · rintro ⟨before, after, split⟩
        have lengthEquality := congrArg List.length split
        simp at lengthEquality
        omega
  | [first] => by
      constructor
      · simp [prefixAdjacentPairsList, Word.adjacentPairsFrom]
      · rintro ⟨before, after, split⟩
        have lengthEquality := congrArg List.length split
        simp at lengthEquality
        omega
  | first :: second :: rest => by
      change
        (source, target) ∈
              (first, second) ::
                prefixAdjacentPairsList (second :: rest) ↔
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
            (mem_prefixAdjacentPairsList_iff_exists_split
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
              (mem_prefixAdjacentPairsList_iff_exists_split
                source target (second :: rest)).mpr
                ⟨beforeTail, after, tailSplit⟩

private theorem prefixAdjacentPairsList_word (word : Word Nat) :
    prefixAdjacentPairsList word.toList = word.adjacentPairs := by
  cases word
  rfl

/-- Locate a graph edge as an exact adjacent occurrence in the ambient
word. This is the list decomposition used by both cases of Trahtman's
prefix step. -/
theorem adjacentPair_mem_iff_exists_toList_split
    (source target : Nat) (word : Word Nat) :
    (source, target) ∈ word.adjacentPairs ↔
      ∃ before after,
        word.toList = before ++ source :: target :: after := by
  rw [← prefixAdjacentPairsList_word]
  exact mem_prefixAdjacentPairsList_iff_exists_split
    source target word.toList

private theorem prefixAdjacentPair_support
    {letters : List Nat} {source target : Nat}
    (member :
      (source, target) ∈ prefixAdjacentPairsList letters) :
    source ∈ letters ∧ target ∈ letters := by
  rcases
      (mem_prefixAdjacentPairsList_iff_exists_split
        source target letters).mp member with
    ⟨before, after, shape⟩
  rw [shape]
  simp

private theorem sharedSupport_or_disjoint :
    ∀ left right : List Nat,
      (∃ letter, letter ∈ left ∧ letter ∈ right) ∨
        ∀ letter, letter ∈ left → letter ∉ right
  | [], right => by
      exact Or.inr <| by
        intro letter member
        simp at member
  | head :: tail, right => by
      by_cases headRight : head ∈ right
      · exact Or.inl ⟨head, by simp, headRight⟩
      · rcases sharedSupport_or_disjoint tail right with
          shared | disjoint
        · rcases shared with ⟨letter, letterTail, letterRight⟩
          exact Or.inl
            ⟨letter, List.Mem.tail head letterTail, letterRight⟩
        · exact Or.inr <| by
            intro letter member
            simp only [List.mem_cons] at member
            rcases member with rfl | letterTail
            · exact headRight
            · exact disjoint letter letterTail

private theorem no_reverse_edge_across_disjoint_cut
    (leftHead rightHead : Nat)
    (leftTail rightTail : List Nat)
    (disjoint :
      ∀ letter,
        letter ∈ leftHead :: leftTail →
          letter ∉ rightHead :: rightTail)
    {source target : Nat}
    (sourceRight : source ∈ rightHead :: rightTail)
    (targetLeft : target ∈ leftHead :: leftTail) :
    (source, target) ∉
      prefixAdjacentPairsList
        ((leftHead :: leftTail) ++ rightHead :: rightTail) := by
  intro edge
  change
    (source, target) ∈
      Word.adjacentPairsFrom leftHead
        (leftTail ++ rightHead :: rightTail) at edge
  rw [Word.adjacentPairsFrom_append] at edge
  simp only [List.mem_append, List.mem_cons] at edge
  rcases edge with leftEdge | boundary | rightEdge
  · have sourceLeft : source ∈ leftHead :: leftTail :=
      (prefixAdjacentPair_support
        (letters := leftHead :: leftTail) leftEdge).1
    exact disjoint source sourceLeft sourceRight
  · simp only [Prod.mk.injEq] at boundary
    rcases boundary with ⟨sourceEq, _⟩
    have finalLeft :
        leftTail.getLastD leftHead ∈ leftHead :: leftTail :=
      List.getLastD_mem_cons
    have sourceLeft : source ∈ leftHead :: leftTail := by
      rw [sourceEq]
      exact finalLeft
    exact disjoint source sourceLeft sourceRight
  · have targetRight : target ∈ rightHead :: rightTail :=
      (prefixAdjacentPair_support
        (letters := rightHead :: rightTail) rightEdge).2
    exact disjoint target targetLeft targetRight

private theorem exists_path_edge_crossing_cut
    (left right : List Nat)
    (disjoint :
      ∀ letter, letter ∈ left → letter ∉ right) :
    ∀ (previous : Nat) (tail : List Nat),
      previous ∈ right →
        tail.getLastD previous ∈ left →
          (∀ letter,
            letter ∈ previous :: tail →
              letter ∈ left ∨ letter ∈ right) →
            ∃ source target,
              source ∈ right ∧
                target ∈ left ∧
                  (source, target) ∈
                    Word.adjacentPairsFrom previous tail
  | previous, [], previousRight, finalLeft, _ => by
      exact False.elim
        (disjoint previous finalLeft previousRight)
  | previous, next :: rest, previousRight, finalLeft,
      vertices => by
      by_cases nextLeft : next ∈ left
      · exact
          ⟨previous, next, previousRight, nextLeft, by
            simp [Word.adjacentPairsFrom]⟩
      · have nextRight : next ∈ right := by
          rcases vertices next (by simp) with inLeft | inRight
          · exact False.elim (nextLeft inLeft)
          · exact inRight
        have restFinalLeft : rest.getLastD next ∈ left := by
          simpa only [List.getLastD_cons] using finalLeft
        have restVertices :
            ∀ letter,
              letter ∈ next :: rest →
                letter ∈ left ∨ letter ∈ right := by
          intro letter member
          exact vertices letter (List.Mem.tail previous member)
        rcases exists_path_edge_crossing_cut left right disjoint
            next rest nextRight restFinalLeft restVertices with
          ⟨source, target, sourceRight, targetLeft, edge⟩
        exact
          ⟨source, target, sourceRight, targetLeft, by
            simp only [Word.adjacentPairsFrom, List.mem_cons]
            exact Or.inr edge⟩

/-- Every cut of an indecomposable word into two nonempty pieces has a
letter represented on both sides. Otherwise no edge can return from the
right support to the left support, contradicting directed reachability. -/
theorem indecomposable_split_support_overlap
    (word : Word Nat)
    (leftHead rightHead : Nat)
    (leftTail rightTail : List Nat)
    (shape :
      word.toList =
        (leftHead :: leftTail) ++ rightHead :: rightTail)
    (indecomposable : TrahtmanIndecomposable word) :
    ∃ letter,
      letter ∈ leftHead :: leftTail ∧
        letter ∈ rightHead :: rightTail := by
  rcases sharedSupport_or_disjoint
      (leftHead :: leftTail) (rightHead :: rightTail) with
    shared | disjoint
  · exact shared
  · have rightHeadWord : rightHead ∈ word.toList := by
      rw [shape]
      simp
    let leftFinal : Nat := leftTail.getLastD leftHead
    have leftFinalLeft : leftFinal ∈ leftHead :: leftTail := by
      simpa [leftFinal] using
        (List.getLastD_mem_cons (l := leftTail) (a := leftHead))
    have leftFinalWord : leftFinal ∈ word.toList := by
      rw [shape]
      exact List.mem_append_left _ leftFinalLeft
    rcases indecomposable rightHead rightHeadWord
        leftFinal leftFinalWord with
      ⟨path, pathHead, pathFinal, pathIn⟩
    have pathVertices :
        ∀ letter,
          letter ∈ path.toList →
            letter ∈ leftHead :: leftTail ∨
              letter ∈ rightHead :: rightTail := by
      intro letter member
      have wordMember := pathIn.1 letter member
      rw [shape, List.mem_append] at wordMember
      exact wordMember
    have pathHeadRight :
        path.head ∈ rightHead :: rightTail := by
      rw [pathHead]
      exact List.Mem.head rightTail
    have pathFinalLeft :
        path.tail.getLastD path.head ∈ leftHead :: leftTail := by
      change path.final ∈ leftHead :: leftTail
      rw [pathFinal]
      exact leftFinalLeft
    rcases exists_path_edge_crossing_cut
        (leftHead :: leftTail) (rightHead :: rightTail) disjoint
        path.head path.tail pathHeadRight pathFinalLeft
        pathVertices with
      ⟨source, target, sourceRight, targetLeft, pathEdge⟩
    have wordEdge :
        (source, target) ∈ word.adjacentPairs :=
      pathIn.2 source target pathEdge
    have listEdge :
        (source, target) ∈
          prefixAdjacentPairsList
            ((leftHead :: leftTail) ++ rightHead :: rightTail) := by
      rw [← shape, prefixAdjacentPairsList_word]
      exact wordEdge
    exact False.elim <|
      no_reverse_edge_across_disjoint_cut
        leftHead rightHead leftTail rightTail disjoint
        sourceRight targetLeft listEdge

/-- A literal adjacent pair in a list decomposition is an edge of the
represented word. -/
theorem adjacentPair_mem_of_toList_split
    {word : Word Nat} (stem suffix : List Nat)
    (source target : Nat)
    (shape :
      word.toList = stem ++ source :: target :: suffix) :
    (source, target) ∈ word.adjacentPairs :=
  (adjacentPair_mem_iff_exists_toList_split
    source target word).mpr ⟨stem, suffix, shape⟩

/-- Exhaustive positional classification of the required edge relative to
the endpoint of an already matched prefix. -/
theorem prefixEdgeOccurrence_cases
    (current : Word Nat) (stem currentSuffix : List Nat)
    (previous next : Nat)
    (currentShape :
      current.toList = stem ++ previous :: currentSuffix)
    (currentEdge :
      (previous, next) ∈ current.adjacentPairs) :
    (∃ suffix,
        current.toList = stem ++ previous :: next :: suffix) ∨
      (∃ left middle trailing,
        stem = left ++ previous :: next :: middle ∧
          current.toList =
            left ++ previous :: next :: middle ++
              previous :: trailing) ∨
      (next = previous ∧
        ∃ left trailing,
          stem = left ++ [previous] ∧
            current.toList =
              left ++ previous :: previous :: trailing) ∨
      (∃ gap trailing,
        current.toList =
          stem ++ previous :: gap ++
            previous :: next :: trailing) := by
  rcases
      (adjacentPair_mem_iff_exists_toList_split
        previous next current).mp currentEdge with
    ⟨before, after, edgeShape⟩
  have equality :
      stem ++ previous :: currentSuffix =
        before ++ previous :: next :: after :=
    currentShape.symm.trans edgeShape
  rcases List.append_eq_append_iff.mp equality with
      ⟨extra, beforeShape, currentTail⟩ |
      ⟨extra, prefixShape, edgeTail⟩
  · cases extra with
    | nil =>
        simp only [List.append_nil, List.nil_append] at beforeShape currentTail
        injection currentTail with _ suffixShape
        exact Or.inl ⟨after, by simpa [suffixShape] using currentShape⟩
    | cons extraHead extraTail =>
        simp only [List.cons_append] at currentTail
        injection currentTail with headEq suffixShape
        subst extraHead
        exact Or.inr <| Or.inr <| Or.inr
          ⟨extraTail, after, by
            rw [currentShape, suffixShape]
            simp [List.append_assoc]⟩
  · cases extra with
    | nil =>
        simp only [List.append_nil, List.nil_append] at prefixShape edgeTail
        injection edgeTail with _ tailEq
        exact Or.inl
          ⟨after, by
            rw [currentShape, tailEq]⟩
    | cons extraHead extraTail =>
        simp only [List.cons_append] at edgeTail
        injection edgeTail with headEq tailEq
        subst extraHead
        cases extraTail with
        | nil =>
            simp only [List.nil_append] at tailEq
            injection tailEq with nextEq afterEq
            subst next
            exact Or.inr <| Or.inr <| Or.inl
              ⟨rfl, before, currentSuffix,
                by simpa using prefixShape,
                by
                  simpa [prefixShape, List.append_assoc] using
                    currentShape⟩
        | cons second rest =>
            simp only [List.cons_append] at tailEq
            injection tailEq with secondEq afterEq
            subst second
            exact Or.inr <| Or.inl
              ⟨before, rest, currentSuffix,
                by simpa using prefixShape,
                by
                  simpa [prefixShape, List.append_assoc] using
                    currentShape⟩

/-- The sole remaining combinatorial move after edge location: a strictly
later occurrence of `previous → next` can be duplicated inside an
indecomposable word while preserving the already matched prefix. -/
def LaterEdgeRepetition : Prop :=
  ∀ current : Word Nat,
    ∀ stem gap trailing : List Nat,
      ∀ previous next : Nat,
        TrahtmanIndecomposable current →
          current.toList =
            stem ++ previous :: gap ++
              previous :: next :: trailing →
            ∃ exposed : Word Nat,
              ∃ between repeatedTrailing : List Nat,
                Derives basis current exposed ∧
                  exposed.toList =
                    stem ++ previous :: gap ++
                      previous :: next :: between ++
                        previous :: next :: repeatedTrailing

/-- Indecomposability supplies a repeated anchor enclosing a strictly
later occurrence of the required edge. -/
theorem laterEdge_has_enclosingAnchor
    (current : Word Nat) (stem gap trailing : List Nat)
    (previous next : Nat)
    (indecomposable : TrahtmanIndecomposable current)
    (shape :
      current.toList =
        stem ++ previous :: gap ++
          previous :: next :: trailing) :
    ∃ anchor,
      anchor ∈ stem ++ previous :: gap ++ [previous] ∧
        anchor ∈ next :: trailing := by
  cases stem with
  | nil =>
      have splitShape :
          current.toList =
            (previous :: gap ++ [previous]) ++ next :: trailing := by
        simpa [List.append_assoc] using shape
      rcases indecomposable_split_support_overlap
          current previous next (gap ++ [previous]) trailing
          splitShape indecomposable with
        ⟨anchor, anchorLeft, anchorRight⟩
      exact ⟨anchor, by simpa using anchorLeft, anchorRight⟩
  | cons prefixHead prefixTail =>
      have splitShape :
          current.toList =
            (prefixHead ::
              prefixTail ++ previous :: gap ++ [previous]) ++
                next :: trailing := by
        simpa [List.append_assoc] using shape
      rcases indecomposable_split_support_overlap
          current prefixHead next
          (prefixTail ++ previous :: gap ++ [previous]) trailing
          splitShape indecomposable with
        ⟨anchor, anchorLeft, anchorRight⟩
      exact ⟨anchor, by simpa [List.append_assoc] using anchorLeft,
        anchorRight⟩

/-- A later self-edge is repeated directly by duplicating the closed walk
from the matched endpoint through that edge target. -/
theorem existsLaterEdgeRepetition_self
    (current : Word Nat) (stem gap trailing : List Nat)
    (previous : Nat)
    (shape :
      current.toList =
        stem ++ previous :: gap ++
          previous :: previous :: trailing) :
    ∃ exposed : Word Nat,
      ∃ between repeatedTrailing : List Nat,
        Derives basis current exposed ∧
          exposed.toList =
            stem ++ previous :: gap ++
              previous :: previous :: between ++
                previous :: previous :: repeatedTrailing := by
  have excursionNonempty : gap ++ [previous] ≠ [] := by
    simp
  let anchor := Word.singleton previous
  let excursion :=
    completionWordOfList previous (gap ++ [previous])
  have excursionList : excursion.toList = gap ++ [previous] := by
    exact completionWordOfList_toList previous excursionNonempty
  let sourceCore := (anchor ++ excursion) ++ anchor
  let targetCore := (((anchor ++ excursion) ++ anchor) ++ excursion) ++
    anchor
  let sourceWord := prefixContext stem sourceCore trailing
  let targetWord := prefixContext stem targetCore trailing
  have currentEq : current = sourceWord := by
    apply Word.toList_injective
    rw [shape]
    simp only [sourceWord, prefixContext_toList, sourceCore,
      Word.toList_append, anchor, Word.toList_singleton, excursionList,
      List.cons_append, List.nil_append, List.append_assoc]
  have derivation : Derives basis current targetWord := by
    rw [currentEq]
    exact derivesPrefixContext stem trailing
      (derivesSandwichExpansion anchor excursion)
  refine ⟨targetWord, gap, trailing, derivation, ?_⟩
  simp only [targetWord, prefixContext_toList, targetCore,
    Word.toList_append, anchor, Word.toList_singleton, excursionList,
    List.cons_append, List.nil_append, List.append_assoc]

/-- The remaining non-self-loop version of `LaterEdgeRepetition`. -/
def DistinctLaterEdgeRepetition : Prop :=
  ∀ current : Word Nat,
    ∀ stem gap trailing : List Nat,
      ∀ previous next : Nat,
        previous ≠ next →
          TrahtmanIndecomposable current →
            current.toList =
              stem ++ previous :: gap ++
                previous :: next :: trailing →
              ∃ exposed : Word Nat,
                ∃ between repeatedTrailing : List Nat,
                  Derives basis current exposed ∧
                    exposed.toList =
                      stem ++ previous :: gap ++
                        previous :: next :: between ++
                          previous :: next :: repeatedTrailing

private theorem prefix_getLastD_append
    (left right : List Nat) (fallback : Nat) :
    (left ++ right).getLastD fallback =
      right.getLastD (left.getLastD fallback) := by
  induction left generalizing fallback with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, List.getLastD_cons]
      exact ih head

private theorem prefix_getLastD_append_singleton
    (letters : List Nat) (terminal fallback : Nat) :
    (letters ++ [terminal]).getLastD fallback = terminal := by
  rw [prefix_getLastD_append]
  simp only [List.getLastD_cons]
  rfl

private theorem prefix_exists_append_getLastD_cons
    (head fallback : Nat) (tail : List Nat) :
    ∃ before,
      head :: tail =
        before ++ [(head :: tail).getLastD fallback] := by
  induction tail generalizing head fallback with
  | nil => exact ⟨[], by simp⟩
  | cons next rest ih =>
      rcases ih next head with ⟨before, beforeShape⟩
      refine ⟨head :: before, ?_⟩
      simpa only [List.getLastD_cons, List.cons_append] using
        congrArg (List.cons head) beforeShape

private theorem prefix_exists_append_getLastD
    (letters : List Nat) (fallback : Nat)
    (nonempty : letters ≠ []) :
    ∃ before,
      letters = before ++ [letters.getLastD fallback] := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
      exact prefix_exists_append_getLastD_cons head fallback tail

private theorem prefix_rightAnchorSplit
    (next anchor : Nat)
    (trailing before after : List Nat)
    (shape : next :: trailing = before ++ anchor :: after) :
    ∃ cycleTail,
      before ++ [anchor] = next :: cycleTail ∧
        trailing = cycleTail ++ after := by
  cases before with
  | nil =>
      simp only [List.nil_append] at shape
      injection shape with headEq tailEq
      subst anchor
      exact ⟨[], by simp, by simpa using tailEq⟩
  | cons head tail =>
      simp only [List.cons_append] at shape
      injection shape with headEq tailEq
      subst head
      refine ⟨tail ++ [anchor], rfl, ?_⟩
      simpa [List.append_assoc] using tailEq

/-- Smallest remaining algebraic statement. The graph argument has already
supplied an anchor occurring on both sides of the later edge; this statement
only splits at those occurrences and duplicates the enclosed nonempty walk
with `sandwichLaw`. -/
def EnclosingAnchorDuplication : Prop :=
  ∀ current : Word Nat,
    ∀ stem gap trailing : List Nat,
      ∀ previous next anchor : Nat,
        previous ≠ next →
          current.toList =
            stem ++ previous :: gap ++
              previous :: next :: trailing →
            anchor ∈ stem ++ previous :: gap ++ [previous] →
              anchor ∈ next :: trailing →
                ∃ exposed : Word Nat,
                  ∃ between repeatedTrailing : List Nat,
                    Derives basis current exposed ∧
                      exposed.toList =
                        stem ++ previous :: gap ++
                          previous :: next :: between ++
                            previous :: next :: repeatedTrailing

/-- Split at the two supplied anchor occurrences and duplicate the enclosed
nonempty walk with the sandwich law. The list reconstruction records the
second copy of the distinguished `previous → next` edge explicitly. -/
theorem enclosingAnchorDuplication :
    EnclosingAnchorDuplication := by
  intro current stem gap trailing previous next anchor different
    shape anchorLeft anchorRight
  rcases List.mem_iff_append.mp anchorLeft with
    ⟨leftBefore, leftAfter, leftShape⟩
  rcases List.mem_iff_append.mp anchorRight with
    ⟨rightBefore, rightAfter, rightShape⟩
  have leftFinal : leftAfter.getLastD anchor = previous := by
    have lastEquality :
        (stem ++ previous :: gap ++ [previous]).getLastD previous =
          (leftBefore ++ anchor :: leftAfter).getLastD previous :=
      congrArg (fun letters : List Nat => letters.getLastD previous)
        leftShape
    have sourceFinal :
        (stem ++ previous :: gap ++ [previous]).getLastD previous =
          previous := by
      simpa [List.append_assoc] using
        (prefix_getLastD_append_singleton
          (stem ++ (previous :: gap)) previous previous)
    have splitFinal :
        (leftBefore ++ anchor :: leftAfter).getLastD previous =
          leftAfter.getLastD anchor := by
      rw [prefix_getLastD_append, List.getLastD_cons]
    rw [sourceFinal, splitFinal] at lastEquality
    exact lastEquality.symm
  have excursionNonempty : leftAfter ++ rightBefore ≠ [] := by
    intro empty
    have emptyParts := List.append_eq_nil_iff.mp empty
    have anchorPrevious : anchor = previous := by
      have final := leftFinal
      rw [emptyParts.1] at final
      simpa using final
    have nextAnchor : next = anchor := by
      have right := rightShape
      rw [emptyParts.2] at right
      simp only [List.nil_append] at right
      injection right
    exact different (anchorPrevious.symm.trans nextAnchor.symm)
  rcases prefix_rightAnchorSplit next anchor trailing rightBefore
      rightAfter rightShape with
    ⟨cycleTail, cycleShape, trailingShape⟩
  have cycleFinal : cycleTail.getLastD next = anchor := by
    have lastEquality :
        (rightBefore ++ [anchor]).getLastD next =
          (next :: cycleTail).getLastD next :=
      congrArg (fun letters : List Nat => letters.getLastD next)
        cycleShape
    have prefixFinal :
        (rightBefore ++ [anchor]).getLastD next = anchor :=
      prefix_getLastD_append_singleton rightBefore anchor next
    have splitFinal :
        (next :: cycleTail).getLastD next =
          cycleTail.getLastD next := by
      rw [List.getLastD_cons]
    rw [prefixFinal, splitFinal] at lastEquality
    exact lastEquality.symm
  have enclosedNonempty : cycleTail ++ leftAfter ≠ [] := by
    intro empty
    have emptyParts := List.append_eq_nil_iff.mp empty
    have anchorPrevious : anchor = previous := by
      have final := leftFinal
      rw [emptyParts.2] at final
      simpa using final
    have nextAnchor : next = anchor := by
      have final := cycleFinal
      rw [emptyParts.1] at final
      simpa using final
    exact different (anchorPrevious.symm.trans nextAnchor.symm)
  have enclosedFinal :
      (cycleTail ++ leftAfter).getLastD next = previous := by
    rw [prefix_getLastD_append, cycleFinal, leftFinal]
  rcases prefix_exists_append_getLastD
      (cycleTail ++ leftAfter) next enclosedNonempty with
    ⟨between, enclosedShape⟩
  rw [enclosedFinal] at enclosedShape
  let anchorWord := Word.singleton anchor
  let excursion :=
    completionWordOfList anchor (leftAfter ++ rightBefore)
  have excursionList :
      excursion.toList = leftAfter ++ rightBefore := by
    exact completionWordOfList_toList anchor excursionNonempty
  let sourceCore := (anchorWord ++ excursion) ++ anchorWord
  let targetCore :=
    (((anchorWord ++ excursion) ++ anchorWord) ++ excursion) ++
      anchorWord
  let sourceWord := prefixContext leftBefore sourceCore rightAfter
  let targetWord := prefixContext leftBefore targetCore rightAfter
  have currentEq : current = sourceWord := by
    apply Word.toList_injective
    calc
      current.toList =
          (stem ++ previous :: gap ++ [previous]) ++
            next :: trailing := by
        simpa [List.append_assoc] using shape
      _ = (leftBefore ++ anchor :: leftAfter) ++
            (rightBefore ++ anchor :: rightAfter) := by
        rw [leftShape, rightShape]
      _ = sourceWord.toList := by
        simp only [sourceWord, prefixContext_toList, sourceCore,
          Word.toList_append, anchorWord, Word.toList_singleton,
          excursionList, List.cons_append, List.nil_append,
          List.append_assoc]
  have derivation : Derives basis current targetWord := by
    rw [currentEq]
    exact derivesPrefixContext leftBefore rightAfter
      (derivesSandwichExpansion anchorWord excursion)
  refine
    ⟨targetWord, between, cycleTail ++ rightAfter, derivation, ?_⟩
  have leftBlockShape :
      leftBefore ++ [anchor] ++ leftAfter =
        stem ++ previous :: gap ++ [previous] := by
    simpa [List.append_assoc] using leftShape.symm
  calc
    targetWord.toList =
        ((((leftBefore ++ [anchor] ++ leftAfter) ++
              (rightBefore ++ [anchor])) ++ leftAfter) ++
            (rightBefore ++ [anchor])) ++ rightAfter := by
      simp only [targetWord, prefixContext_toList, targetCore,
        Word.toList_append, anchorWord, Word.toList_singleton,
        excursionList, List.cons_append, List.nil_append,
        List.append_assoc]
    _ = ((((stem ++ previous :: gap ++ [previous]) ++
              (next :: cycleTail)) ++ leftAfter) ++
            (next :: cycleTail)) ++ rightAfter := by
      simp only [leftBlockShape, cycleShape]
    _ = (stem ++ previous :: gap ++ [previous]) ++
          next :: ((cycleTail ++ leftAfter) ++
            next :: cycleTail ++ rightAfter) := by
      simp [List.append_assoc]
    _ = (stem ++ previous :: gap ++ [previous]) ++
          next :: ((between ++ [previous]) ++
            next :: cycleTail ++ rightAfter) := by
      rw [enclosedShape]
    _ = stem ++ previous :: gap ++
          previous :: next :: between ++
            previous :: next :: (cycleTail ++ rightAfter) := by
      simp [List.append_assoc]

theorem distinctLaterEdgeRepetition_of_enclosingAnchorDuplication
    (duplicate : EnclosingAnchorDuplication) :
    DistinctLaterEdgeRepetition := by
  intro current stem gap trailing previous next different
    indecomposable shape
  rcases laterEdge_has_enclosingAnchor
      current stem gap trailing previous next
      indecomposable shape with
    ⟨anchor, anchorLeft, anchorRight⟩
  exact duplicate current stem gap trailing previous next anchor
    different shape anchorLeft anchorRight

theorem laterEdgeRepetition_of_distinct
    (repeatDistinct : DistinctLaterEdgeRepetition) :
    LaterEdgeRepetition := by
  intro current stem gap trailing previous next
    currentIndecomposable shape
  by_cases same : previous = next
  · subst next
    exact existsLaterEdgeRepetition_self
      current stem gap trailing previous shape
  · exact repeatDistinct current stem gap trailing previous next
      same currentIndecomposable shape

theorem laterEdgeRepetition_of_enclosingAnchorDuplication
    (duplicate : EnclosingAnchorDuplication) :
    LaterEdgeRepetition :=
  laterEdgeRepetition_of_distinct
    (distinctLaterEdgeRepetition_of_enclosingAnchorDuplication duplicate)

/-- Edge location, the two elementary prefix rewrites, and the repeated
edge switch reduce `PrefixEdgeExposure` to `LaterEdgeRepetition`. -/
theorem prefixEdgeExposure_of_laterEdgeRepetition
    (repeatLater : LaterEdgeRepetition) :
    PrefixEdgeExposure := by
  intro current stem previous next currentSuffix
    currentIndecomposable currentShape currentEdge
  rcases prefixEdgeOccurrence_cases current stem currentSuffix
      previous next currentShape currentEdge with
    alreadyAligned | earlier | terminalSelf | later
  · rcases alreadyAligned with ⟨suffix, alignedShape⟩
    exact
      ⟨current, Derives.refl current,
        Or.inl ⟨suffix, alignedShape⟩⟩
  · rcases earlier with
      ⟨left, middle, trailing, prefixShape, earlierShape⟩
    rcases existsPrefixAlignment_of_earlierEdge
        current left middle trailing previous next earlierShape with
      ⟨aligned, suffix, derivation, alignedShape⟩
    refine ⟨aligned, derivation, Or.inl ⟨suffix, ?_⟩⟩
    rw [prefixShape]
    exact alignedShape
  · rcases terminalSelf with
      ⟨nextEq, left, trailing, prefixShape, terminalShape⟩
    subst next
    rcases existsPrefixAlignment_of_terminalSelfEdge
        current left trailing previous terminalShape with
      ⟨aligned, suffix, derivation, alignedShape⟩
    refine ⟨aligned, derivation, Or.inl ⟨suffix, ?_⟩⟩
    rw [prefixShape]
    exact alignedShape
  · rcases later with ⟨gap, trailing, laterShape⟩
    rcases repeatLater current stem gap trailing previous next
        currentIndecomposable laterShape with
      ⟨exposed, between, repeatedTrailing,
        derivation, exposedShape⟩
    exact
      ⟨exposed, derivation,
        Or.inr ⟨gap, between, repeatedTrailing, exposedShape⟩⟩

theorem prefixEdgeExtensionStep_of_laterEdgeRepetition
    (repeatLater : LaterEdgeRepetition) :
    PrefixEdgeExtensionStep :=
  prefixEdgeExtensionStep_of_exposure
    (prefixEdgeExposure_of_laterEdgeRepetition repeatLater)

/-- Structural prefix induction. Once one adjacent target edge can be
exposed after any already matched prefix, the whole finite target word can
be exposed as a prefix. -/
private theorem existsCompletePrefix_of_edgeExtension
    (extension : PrefixEdgeExtensionStep)
    (complete : Word Nat) :
    ∀ remaining : List Nat,
      ∀ stem : List Nat,
        ∀ previous : Nat,
          ∀ current : Word Nat,
            ∀ currentSuffix : List Nat,
              complete.toList = stem ++ previous :: remaining →
                TrahtmanIndecomposable current →
                  current.SameMarkedDigraph complete →
                    current.toList =
                      stem ++ previous :: currentSuffix →
                      ∃ expanded : Word Nat, ∃ suffix : List Nat,
                        Derives basis current expanded ∧
                          expanded.toList =
                            complete.toList ++ suffix
  | [], stem, previous, current, currentSuffix,
      completeShape, _, _, currentShape => by
      refine ⟨current, currentSuffix, Derives.refl current, ?_⟩
      rw [currentShape, completeShape]
      simp [List.append_assoc]
  | next :: rest, stem, previous, current, currentSuffix,
      completeShape, currentIndecomposable, sameGraph,
      currentShape => by
      have completeEdge :
          (previous, next) ∈ complete.adjacentPairs :=
        adjacentPair_mem_of_toList_split
          stem rest previous next completeShape
      have currentEdge :
          (previous, next) ∈ current.adjacentPairs :=
        (sameGraph.edge previous next).mpr completeEdge
      rcases extension current stem previous next currentSuffix
          currentIndecomposable currentShape currentEdge with
        ⟨aligned, alignedSuffix, currentAligned, alignedShape⟩
      have currentAlignedGraph :
          current.SameMarkedDigraph aligned :=
        derives_sameMarkedDigraph currentAligned
      have alignedIndecomposable :
          TrahtmanIndecomposable aligned :=
        (trahtmanIndecomposable_iff_of_sameMarkedDigraph
          currentAlignedGraph).mp currentIndecomposable
      have alignedCompleteGraph :
          aligned.SameMarkedDigraph complete :=
        sameMarkedDigraph_trans
          (sameMarkedDigraph_symm currentAlignedGraph) sameGraph
      have completeRestShape :
          complete.toList =
            (stem ++ [previous]) ++ next :: rest := by
        simpa [List.append_assoc] using completeShape
      have alignedRestShape :
          aligned.toList =
            (stem ++ [previous]) ++ next :: alignedSuffix := by
        simpa [List.append_assoc] using alignedShape
      rcases existsCompletePrefix_of_edgeExtension extension complete
          rest (stem ++ [previous]) next aligned alignedSuffix
          completeRestShape alignedIndecomposable
          alignedCompleteGraph alignedRestShape with
        ⟨expanded, suffix, alignedExpanded, expandedShape⟩
      exact
        ⟨expanded, suffix, currentAligned.trans alignedExpanded,
          expandedShape⟩

/-- Exact reduction of `CompletePrefixReachability` to the single
edge-extension statement above. The completeness hypothesis is retained
unchanged even though the prefix induction itself needs only the marked
graph and indecomposability. -/
theorem completePrefixReachability_of_edgeExtension
    (extension : PrefixEdgeExtensionStep) :
    CompletePrefixReachability := by
  intro source complete sourceIndecomposable sameGraph _
  have completeShape :
      complete.toList = [] ++ complete.head :: complete.tail := by
    rfl
  have sourceShape :
      source.toList = [] ++ complete.head :: source.tail := by
    simpa [Word.toList] using congrArg
      (fun head => head :: source.tail) sameGraph.initial
  exact existsCompletePrefix_of_edgeExtension extension complete
    complete.tail [] complete.head source source.tail
    completeShape sourceIndecomposable sameGraph sourceShape

theorem completePrefixReachability_of_exposure
    (exposure : PrefixEdgeExposure) :
    CompletePrefixReachability :=
  completePrefixReachability_of_edgeExtension
    (prefixEdgeExtensionStep_of_exposure exposure)

theorem completePrefixReachability_of_laterEdgeRepetition
    (repeatLater : LaterEdgeRepetition) :
    CompletePrefixReachability :=
  completePrefixReachability_of_edgeExtension
    (prefixEdgeExtensionStep_of_laterEdgeRepetition repeatLater)

theorem completePrefixReachability_of_distinctLaterEdgeRepetition
    (repeatDistinct : DistinctLaterEdgeRepetition) :
    CompletePrefixReachability :=
  completePrefixReachability_of_laterEdgeRepetition
    (laterEdgeRepetition_of_distinct repeatDistinct)

theorem completePrefixReachability_of_enclosingAnchorDuplication
    (duplicate : EnclosingAnchorDuplication) :
    CompletePrefixReachability :=
  completePrefixReachability_of_laterEdgeRepetition
    (laterEdgeRepetition_of_enclosingAnchorDuplication duplicate)

/-- Trahtman's prefix-alignment induction is unconditional once the enclosing
anchor supplied by indecomposability is expanded. -/
theorem completePrefixReachability :
    CompletePrefixReachability :=
  completePrefixReachability_of_enclosingAnchorDuplication
    enclosingAnchorDuplication

/-- The completed representative construction and the prefix induction now
compose without any additional graph assumptions. -/
theorem existsCompletePrefixAlignment_of_edgeExtension
    (extension : PrefixEdgeExtensionStep)
    (source : Word Nat)
    (sourceIndecomposable : TrahtmanIndecomposable source) :
    ∃ complete expanded : Word Nat, ∃ suffix : List Nat,
      source.SameMarkedDigraph complete ∧
        TrahtmanComplete complete ∧
          Derives basis source expanded ∧
            expanded.toList = complete.toList ++ suffix := by
  rcases completeRepresentativeExistence source sourceIndecomposable with
    ⟨complete, sameGraph, completeWord⟩
  rcases completePrefixReachability_of_edgeExtension extension
      source complete sourceIndecomposable sameGraph completeWord with
    ⟨expanded, suffix, derivation, shape⟩
  exact
    ⟨complete, expanded, suffix, sameGraph, completeWord,
      derivation, shape⟩

theorem existsCompletePrefixAlignment_of_exposure
    (exposure : PrefixEdgeExposure)
    (source : Word Nat)
    (sourceIndecomposable : TrahtmanIndecomposable source) :
    ∃ complete expanded : Word Nat, ∃ suffix : List Nat,
      source.SameMarkedDigraph complete ∧
        TrahtmanComplete complete ∧
          Derives basis source expanded ∧
            expanded.toList = complete.toList ++ suffix :=
  existsCompletePrefixAlignment_of_edgeExtension
    (prefixEdgeExtensionStep_of_exposure exposure)
    source sourceIndecomposable

theorem existsCompletePrefixAlignment_of_laterEdgeRepetition
    (repeatLater : LaterEdgeRepetition)
    (source : Word Nat)
    (sourceIndecomposable : TrahtmanIndecomposable source) :
    ∃ complete expanded : Word Nat, ∃ suffix : List Nat,
      source.SameMarkedDigraph complete ∧
        TrahtmanComplete complete ∧
          Derives basis source expanded ∧
            expanded.toList = complete.toList ++ suffix :=
  existsCompletePrefixAlignment_of_edgeExtension
    (prefixEdgeExtensionStep_of_laterEdgeRepetition repeatLater)
    source sourceIndecomposable

theorem existsCompletePrefixAlignment_of_distinctLaterEdgeRepetition
    (repeatDistinct : DistinctLaterEdgeRepetition)
    (source : Word Nat)
    (sourceIndecomposable : TrahtmanIndecomposable source) :
    ∃ complete expanded : Word Nat, ∃ suffix : List Nat,
      source.SameMarkedDigraph complete ∧
        TrahtmanComplete complete ∧
          Derives basis source expanded ∧
            expanded.toList = complete.toList ++ suffix :=
  existsCompletePrefixAlignment_of_laterEdgeRepetition
    (laterEdgeRepetition_of_distinct repeatDistinct)
    source sourceIndecomposable

theorem existsCompletePrefixAlignment_of_enclosingAnchorDuplication
    (duplicate : EnclosingAnchorDuplication)
    (source : Word Nat)
    (sourceIndecomposable : TrahtmanIndecomposable source) :
    ∃ complete expanded : Word Nat, ∃ suffix : List Nat,
      source.SameMarkedDigraph complete ∧
        TrahtmanComplete complete ∧
          Derives basis source expanded ∧
            expanded.toList = complete.toList ++ suffix :=
  existsCompletePrefixAlignment_of_laterEdgeRepetition
    (laterEdgeRepetition_of_enclosingAnchorDuplication duplicate)
    source sourceIndecomposable

end SemigroupBasis.CoRoots.S5_868
