import SemigroupBasis.CoRoots.S5_868PrefixReachability

namespace SemigroupBasis.CoRoots.S5_868

open SemigroupBasis

/-! ## The closed walk carried by an appended suffix -/

/-- The suffix produced by prefix alignment is read as a walk beginning at
the final vertex of the complete prefix. -/
def suffixWalk (complete : Word Nat) (suffix : List Nat) : Word Nat :=
  ⟨complete.final, suffix⟩

@[simp]
theorem suffixWalk_toList (complete : Word Nat) (suffix : List Nat) :
    (suffixWalk complete suffix).toList = complete.final :: suffix :=
  rfl

private theorem suffix_final_mem_toList (word : Word Nat) :
    word.final ∈ word.toList := by
  cases word with
  | mk head tail =>
      simpa [Word.final, Word.toList] using
        (List.getLastD_mem_cons (l := tail) (a := head))

private theorem suffix_exists_append_getLastD_cons
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

private theorem suffix_word_toList_eq_prefix_final
    (word : Word Nat) :
    ∃ before, word.toList = before ++ [word.final] := by
  cases word with
  | mk head tail =>
      rcases suffix_exists_append_getLastD_cons head head tail with
        ⟨before, shape⟩
      exact
        ⟨before, by
          simpa only [Word.toList, Word.final, List.getLastD_cons] using
            shape⟩

private theorem suffix_getLastD_append
    (left right : List Nat) (fallback : Nat) :
    (left ++ right).getLastD fallback =
      right.getLastD (left.getLastD fallback) := by
  induction left generalizing fallback with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, List.getLastD_cons]
      exact ih head

private theorem suffix_toList_getLastD
    (word : Word Nat) (fallback : Nat) :
    word.toList.getLastD fallback = word.final := by
  cases word with
  | mk head tail =>
      simp only [Word.toList, Word.final, List.getLastD_cons]

private theorem suffix_expanded_eq_appendLetters
    {complete expanded : Word Nat} {suffix : List Nat}
    (shape : expanded.toList = complete.toList ++ suffix) :
    expanded = prefixAppendLetters complete suffix := by
  apply Word.toList_injective
  rw [shape]
  exact (prefixAppendLetters_toList complete suffix).symm

/-- Marked-final equality closes the suffix walk back at the final vertex of
the complete prefix. -/
theorem suffixWalk_final_eq
    {complete expanded : Word Nat} {suffix : List Nat}
    (shape : expanded.toList = complete.toList ++ suffix)
    (sameGraph : complete.SameMarkedDigraph expanded) :
    (suffixWalk complete suffix).final = complete.final := by
  cases suffix with
  | nil => rfl
  | cons head tail =>
      have expandedEq := suffix_expanded_eq_appendLetters shape
      have finalEq := sameGraph.final.symm
      rw [expandedEq] at finalEq
      simpa [prefixAppendLetters, suffixWalk, Word.final] using finalEq

/-- The no-new-support/no-new-edge half of marked-graph equality says exactly
that the appended suffix is a directed walk in the complete prefix's graph. -/
theorem suffixWalk_directedPathIn
    {complete expanded : Word Nat} {suffix : List Nat}
    (shape : expanded.toList = complete.toList ++ suffix)
    (sameGraph : complete.SameMarkedDigraph expanded) :
    DirectedPathIn complete (suffixWalk complete suffix) := by
  constructor
  · intro letter member
    simp only [suffixWalk_toList, List.mem_cons] at member
    rcases member with equal | suffixMember
    · subst letter
      exact suffix_final_mem_toList complete
    · apply (sameGraph.support letter).mpr
      rw [shape]
      exact List.mem_append.mpr (Or.inr suffixMember)
  · intro source target member
    have expandedEq := suffix_expanded_eq_appendLetters shape
    apply (sameGraph.edge source target).mpr
    cases suffix with
    | nil =>
        simp [suffixWalk, Word.adjacentPairs,
          Word.adjacentPairsFrom] at member
    | cons head tail =>
        rw [expandedEq]
        simp only [prefixAppendLetters]
        rw [Word.adjacentPairs_append]
        apply List.mem_append.mpr
        right
        change
          (source, target) ∈
            (complete.final, head) ::
              Word.adjacentPairsFrom head tail
        simpa [suffixWalk, Word.adjacentPairs,
          Word.adjacentPairsFrom] using member

/-! ## Extracting a simple cycle from a nonempty closed suffix walk -/

private theorem suffix_exists_simple_cycle_split :
    ∀ letters : List Nat,
      ¬letters.Nodup →
        ∃ before anchor interior after,
          letters =
              before ++ anchor :: interior ++ anchor :: after ∧
            (anchor :: interior).Nodup
  | [], notNodup => False.elim (notNodup (by simp))
  | head :: tail, notNodup => by
      by_cases tailNodup : tail.Nodup
      · have headMember : head ∈ tail := by
          apply Decidable.byContradiction
          intro headAbsent
          exact notNodup (List.nodup_cons.mpr ⟨headAbsent, tailNodup⟩)
        rcases List.mem_iff_append.mp headMember with
          ⟨interior, after, tailShape⟩
        have splitNodup : (interior ++ head :: after).Nodup := by
          rw [← tailShape]
          exact tailNodup
        have appendData := List.nodup_append.mp splitNodup
        have headAbsent : head ∉ interior := by
          intro member
          exact appendData.2.2
            head member head (by simp) rfl
        have cycleNodup : (head :: interior).Nodup :=
          List.nodup_cons.mpr ⟨headAbsent, appendData.1⟩
        exact
          ⟨[], head, interior, after,
            by simp [tailShape], cycleNodup⟩
      · rcases suffix_exists_simple_cycle_split tail tailNodup with
          ⟨before, anchor, interior, after, cycleShape, cycleNodup⟩
        exact
          ⟨head :: before, anchor, interior, after,
            by simp [cycleShape], cycleNodup⟩

/-- The simple path obtained by deleting the repeated closing anchor from a
simple cycle. -/
def suffixCyclePath (anchor : Nat) (interior : List Nat) : Word Nat :=
  ⟨anchor, interior⟩

@[simp]
theorem suffixCyclePath_toList (anchor : Nat) (interior : List Nat) :
    (suffixCyclePath anchor interior).toList = anchor :: interior :=
  rfl

/-- Exact data supplied by the graph and completeness hypotheses for one
strictly shortening suffix step. -/
structure SuffixSimpleCycleCertificate
    (complete : Word Nat) (suffix : List Nat) : Type where
  before : List Nat
  anchor : Nat
  interior : List Nat
  after : List Nat
  walkShape :
    (suffixWalk complete suffix).toList =
      before ++ anchor :: interior ++ anchor :: after
  pathNodup : (anchor :: interior).Nodup
  pathIn : DirectedPathIn complete (suffixCyclePath anchor interior)
  pathOccurs : OccursAsFactor (suffixCyclePath anchor interior) complete
  closingEdge :
    ((suffixCyclePath anchor interior).final, anchor) ∈
      complete.adjacentPairs

/-- Every nonempty suffix satisfying the marked-graph condition contains a
simple cycle. Its open simple path occurs in the complete prefix, and its
closing edge is already an edge of that prefix. -/
theorem existsSuffixSimpleCycleCertificate
    {complete expanded : Word Nat} {suffix : List Nat}
    (completeWord : TrahtmanComplete complete)
    (shape : expanded.toList = complete.toList ++ suffix)
    (sameGraph : complete.SameMarkedDigraph expanded)
    (suffixNonempty : suffix ≠ []) :
    ∃ certificate : SuffixSimpleCycleCertificate complete suffix,
      True := by
  let walk := suffixWalk complete suffix
  have walkIn : DirectedPathIn complete walk :=
    suffixWalk_directedPathIn shape sameGraph
  have walkClosed : walk.final = complete.final :=
    suffixWalk_final_eq shape sameGraph
  have walkFinalInSuffix : walk.final ∈ suffix := by
    cases suffix with
    | nil => exact False.elim (suffixNonempty rfl)
    | cons head tail =>
        simpa only [walk, suffixWalk, Word.final,
          List.getLastD_cons, List.mem_cons] using
          (List.getLastD_mem_cons (l := tail) (a := head))
  have boundaryInSuffix : complete.final ∈ suffix := by
    rw [← walkClosed]
    exact walkFinalInSuffix
  have walkNotNodup : ¬walk.toList.Nodup := by
    intro walkNodup
    have nodupData : (complete.final :: suffix).Nodup := by
      simpa only [walk, suffixWalk, Word.toList] using walkNodup
    exact (List.nodup_cons.mp nodupData).1 boundaryInSuffix
  rcases suffix_exists_simple_cycle_split walk.toList walkNotNodup with
    ⟨before, anchor, interior, after, cycleShape, cycleNodup⟩
  let path := suffixCyclePath anchor interior
  have pathOccursInWalk : OccursAsFactor path walk := by
    refine ⟨before, anchor :: after, ?_⟩
    simpa [path, suffixCyclePath, List.append_assoc] using cycleShape
  have pathIn : DirectedPathIn complete path := by
    constructor
    · intro letter member
      exact walkIn.1 letter
        (occursAsFactor_support pathOccursInWalk letter member)
    · intro source target member
      exact walkIn.2 source target
        (occursAsFactor_edge pathOccursInWalk source target member)
  have pathOccurs : OccursAsFactor path complete :=
    completeWord path
      (by
        simpa only [path, suffixCyclePath, Word.toList] using cycleNodup)
      pathIn
  rcases suffix_word_toList_eq_prefix_final path with
    ⟨pathFront, pathFinalShape⟩
  have closingShape :
      walk.toList =
        (before ++ pathFront) ++ path.final :: anchor :: after := by
    rw [cycleShape]
    change
      before ++ path.toList ++ anchor :: after =
        (before ++ pathFront) ++ path.final :: anchor :: after
    rw [pathFinalShape]
    simp [List.append_assoc]
  have closingInWalk :
      (path.final, anchor) ∈ walk.adjacentPairs :=
    adjacentPair_mem_of_toList_split
      (word := walk) (before ++ pathFront) after
      path.final anchor closingShape
  have closingEdge :
      (path.final, anchor) ∈ complete.adjacentPairs :=
    walkIn.2 path.final anchor closingInWalk
  let certificate : SuffixSimpleCycleCertificate complete suffix :=
    { before := before
      anchor := anchor
      interior := interior
      after := after
      walkShape := by simpa [walk] using cycleShape
      pathNodup := cycleNodup
      pathIn := by simpa [path] using pathIn
      pathOccurs := by simpa [path] using pathOccurs
      closingEdge := by simpa [path] using closingEdge }
  exact ⟨certificate, True.intro⟩

/-! ## Exposing the certified closing edge in the complete prefix -/

/-- A derivable representative in which the complete prefix's occurrence of
the simple path has been extended by its recorded closing edge. -/
structure ClosedCycleExposure
    (complete : Word Nat) (anchor : Nat) (interior : List Nat) : Type where
  exposed : Word Nat
  before : List Nat
  after : List Nat
  derivation : Derives basis complete exposed
  shape :
    exposed.toList =
      before ++ (suffixCyclePath anchor interior).toList ++
        anchor :: after

/-- Prefix edge extension closes the occurrence supplied by completeness.
This is the exact use of indecomposability needed before the local suffix
contraction. -/
noncomputable def closedCycleExposure
    {complete : Word Nat} {suffix : List Nat}
    (indecomposable : TrahtmanIndecomposable complete)
    (certificate : SuffixSimpleCycleCertificate complete suffix) :
    ClosedCycleExposure complete certificate.anchor
      certificate.interior :=
  Classical.choice <| by
    let path := suffixCyclePath certificate.anchor certificate.interior
    rcases certificate.pathOccurs with
      ⟨occurrenceBefore, occurrenceAfter, occurrenceShape⟩
    rcases suffix_word_toList_eq_prefix_final path with
      ⟨pathFront, pathFinalShape⟩
    have completeShape :
        complete.toList =
          (occurrenceBefore ++ pathFront) ++
            path.final :: occurrenceAfter := by
      rw [occurrenceShape, pathFinalShape]
      simp [List.append_assoc]
    let extension : PrefixEdgeExtensionStep :=
      prefixEdgeExtensionStep_of_laterEdgeRepetition
        (laterEdgeRepetition_of_enclosingAnchorDuplication
          enclosingAnchorDuplication)
    rcases extension complete (occurrenceBefore ++ pathFront)
        path.final certificate.anchor occurrenceAfter indecomposable
        completeShape certificate.closingEdge with
      ⟨exposed, exposedAfter, derivation, exposedShape⟩
    refine
      ⟨{ exposed := exposed
         before := occurrenceBefore
         after := exposedAfter
         derivation := derivation
         shape := ?_ }⟩
    change
      exposed.toList =
        occurrenceBefore ++ path.toList ++
          certificate.anchor :: exposedAfter
    rw [pathFinalShape]
    simpa [List.append_assoc] using exposedShape

/-! ## The exact algebraic contractions used by a deletion step -/

/-- Two adjacent copies of a nontrivial anchored loop contract by the reverse
sandwich law. -/
theorem derivesAdjacentClosedWalkContraction
    (anchor interior : Word Nat) :
    Derives basis
      ((((anchor ++ interior) ++ anchor) ++ interior) ++ anchor)
      ((anchor ++ interior) ++ anchor) :=
  derivesSandwichContraction anchor interior

/-- Two separated copies of an anchored loop contract by Trahtman's derived
law `xyxzxyx → xyxzx`. -/
theorem derivesSeparatedClosedWalkContraction
    (anchor interior middle : Word Nat) :
    Derives basis
      ((((((anchor ++ interior) ++ anchor) ++ middle) ++ anchor) ++
          interior) ++ anchor)
      ((((anchor ++ interior) ++ anchor) ++ middle) ++ anchor) :=
  derivesAnchoredLoopContraction anchor interior middle

/-- An adjacent repeated self-edge is the power contraction `x³ → x²`. -/
theorem derivesAdjacentSelfLoopContraction (anchor : Word Nat) :
    Derives basis ((anchor ++ anchor) ++ anchor) (anchor ++ anchor) :=
  derivesPowerContraction anchor

/-- For separated self-edges, first expand both copies `x² → x³`, use
`xyxzxyx → xyxzx` with `y = x`, and contract the retained first cube. -/
theorem derivesSeparatedSelfLoopContraction
    (anchor middle : Word Nat) :
    Derives basis
      ((((anchor ++ anchor) ++ middle) ++ anchor) ++ anchor)
      (((anchor ++ anchor) ++ middle) ++ anchor) := by
  have expandFirst :
      Derives basis
        ((((anchor ++ anchor) ++ middle) ++ anchor) ++ anchor)
        (((((anchor ++ anchor) ++ anchor) ++ middle) ++ anchor) ++
          anchor) := by
    simpa [Word.append_assoc] using
      Derives.appendRight (derivesPowerExpansion anchor)
        ((middle ++ anchor) ++ anchor)
  have expandSecond :
      Derives basis
        (((((anchor ++ anchor) ++ anchor) ++ middle) ++ anchor) ++
          anchor)
        ((((((anchor ++ anchor) ++ anchor) ++ middle) ++ anchor) ++
          anchor) ++ anchor) := by
    simpa [Word.append_assoc] using
      Derives.prepend (((anchor ++ anchor) ++ anchor) ++ middle)
        (derivesPowerExpansion anchor)
  have removeRepeatedLoop :
      Derives basis
        ((((((anchor ++ anchor) ++ anchor) ++ middle) ++ anchor) ++
          anchor) ++ anchor)
        ((((anchor ++ anchor) ++ anchor) ++ middle) ++ anchor) := by
    simpa [Word.append_assoc] using
      derivesAnchoredLoopContraction anchor anchor middle
  have contractFirst :
      Derives basis
        ((((anchor ++ anchor) ++ anchor) ++ middle) ++ anchor)
        (((anchor ++ anchor) ++ middle) ++ anchor) := by
    simpa [Word.append_assoc] using
      Derives.appendRight (derivesPowerContraction anchor)
        (middle ++ anchor)
  exact expandFirst.trans <|
    expandSecond.trans <|
      removeRepeatedLoop.trans contractFirst

/-- If two ordinary loop copies have distinct adjacent anchor occurrences,
expand the middle square, use the derived loop contraction with `z = x`, and
contract the retained terminal cube. -/
theorem derivesAdjacentDistinctClosedWalkContraction
    (anchor interior : Word Nat) :
    Derives basis
      (((((anchor ++ interior) ++ anchor) ++ anchor) ++ interior) ++
        anchor)
      (((anchor ++ interior) ++ anchor) ++ anchor) := by
  have expandBoundary :
      Derives basis
        (((((anchor ++ interior) ++ anchor) ++ anchor) ++ interior) ++
          anchor)
        ((((((anchor ++ interior) ++ anchor) ++ anchor) ++ anchor) ++
          interior) ++ anchor) := by
    simpa [Word.append_assoc] using
      Derives.prepend (anchor ++ interior) <|
        Derives.appendRight (derivesPowerExpansion anchor)
          (interior ++ anchor)
  have removeRepeatedLoop :
      Derives basis
        ((((((anchor ++ interior) ++ anchor) ++ anchor) ++ anchor) ++
          interior) ++ anchor)
        ((((anchor ++ interior) ++ anchor) ++ anchor) ++ anchor) := by
    simpa [Word.append_assoc] using
      derivesAnchoredLoopContraction anchor interior anchor
  have contractBoundary :
      Derives basis
        ((((anchor ++ interior) ++ anchor) ++ anchor) ++ anchor)
        (((anchor ++ interior) ++ anchor) ++ anchor) := by
    simpa [Word.append_assoc] using
      Derives.prepend (anchor ++ interior)
        (derivesPowerContraction anchor)
  exact expandBoundary.trans <|
    removeRepeatedLoop.trans contractBoundary

/-- Four consecutive copies in the adjacent-distinct self-loop case reduce to
three by contracting the first cube under a right context. -/
theorem derivesAdjacentDistinctSelfLoopContraction (anchor : Word Nat) :
    Derives basis
      (((anchor ++ anchor) ++ anchor) ++ anchor)
      ((anchor ++ anchor) ++ anchor) := by
  simpa [Word.append_assoc] using
    Derives.appendRight (derivesPowerContraction anchor) anchor

/-- Delete a second loop which shares its opening anchor with the first loop,
under arbitrary raw-list contexts. Empty interiors are exactly the power-law
case. -/
theorem derivesSharedClosedWalkContractionInContext
    (current target : Word Nat)
    (left interior right : List Nat) (anchor : Nat)
    (currentShape :
      current.toList =
        left ++ anchor :: interior ++ anchor :: interior ++
          anchor :: right)
    (targetShape :
      target.toList = left ++ anchor :: interior ++ anchor :: right) :
    Derives basis current target := by
  let anchorWord := Word.singleton anchor
  cases interior with
  | nil =>
      let sourceCore := (anchorWord ++ anchorWord) ++ anchorWord
      let targetCore := anchorWord ++ anchorWord
      let sourceWord := prefixContext left sourceCore right
      let targetWord := prefixContext left targetCore right
      have currentEq : current = sourceWord := by
        apply Word.toList_injective
        rw [currentShape]
        simp only [sourceWord, prefixContext_toList, sourceCore,
          Word.toList_append, anchorWord, Word.toList_singleton,
          List.cons_append, List.nil_append, List.append_assoc]
      have targetEq : target = targetWord := by
        apply Word.toList_injective
        rw [targetShape]
        simp only [targetWord, prefixContext_toList, targetCore,
          Word.toList_append, anchorWord, Word.toList_singleton,
          List.cons_append, List.nil_append, List.append_assoc]
      rw [currentEq, targetEq]
      exact derivesPrefixContext left right
        (derivesAdjacentSelfLoopContraction anchorWord)
  | cons interiorHead interiorTail =>
      let interiorWord : Word Nat := ⟨interiorHead, interiorTail⟩
      have interiorWordList :
          interiorWord.toList = interiorHead :: interiorTail := rfl
      let sourceCore :=
        ((((anchorWord ++ interiorWord) ++ anchorWord) ++
          interiorWord) ++ anchorWord)
      let targetCore := (anchorWord ++ interiorWord) ++ anchorWord
      let sourceWord := prefixContext left sourceCore right
      let targetWord := prefixContext left targetCore right
      have currentEq : current = sourceWord := by
        apply Word.toList_injective
        rw [currentShape]
        simp only [sourceWord, prefixContext_toList, sourceCore,
          Word.toList_append, anchorWord, Word.toList_singleton,
          interiorWordList, List.cons_append, List.nil_append,
          List.append_assoc]
      have targetEq : target = targetWord := by
        apply Word.toList_injective
        rw [targetShape]
        simp only [targetWord, prefixContext_toList, targetCore,
          Word.toList_append, anchorWord, Word.toList_singleton,
          interiorWordList, List.cons_append, List.nil_append,
          List.append_assoc]
      rw [currentEq, targetEq]
      exact derivesPrefixContext left right
        (derivesAdjacentClosedWalkContraction
          anchorWord interiorWord)

/-- Delete a second loop with a distinct opening-anchor occurrence. A
nonempty middle uses `xyxzxyx → xyxzx`; an empty middle is first expanded
at the adjacent anchor pair. Empty loop interiors use the corresponding
self-loop contractions. -/
theorem derivesDistinctClosedWalkContractionInContext
    (current target : Word Nat)
    (left interior middle right : List Nat) (anchor : Nat)
    (currentShape :
      current.toList =
        left ++ anchor :: interior ++ anchor :: middle ++
          anchor :: interior ++ anchor :: right)
    (targetShape :
      target.toList =
        left ++ anchor :: interior ++ anchor :: middle ++
          anchor :: right) :
    Derives basis current target := by
  let anchorWord := Word.singleton anchor
  cases interior with
  | nil =>
      cases middle with
      | nil =>
          let sourceCore :=
            (((anchorWord ++ anchorWord) ++ anchorWord) ++ anchorWord)
          let targetCore := (anchorWord ++ anchorWord) ++ anchorWord
          let sourceWord := prefixContext left sourceCore right
          let targetWord := prefixContext left targetCore right
          have currentEq : current = sourceWord := by
            apply Word.toList_injective
            rw [currentShape]
            simp only [sourceWord, prefixContext_toList, sourceCore,
              Word.toList_append, anchorWord, Word.toList_singleton,
              List.cons_append, List.nil_append, List.append_assoc]
          have targetEq : target = targetWord := by
            apply Word.toList_injective
            rw [targetShape]
            simp only [targetWord, prefixContext_toList, targetCore,
              Word.toList_append, anchorWord, Word.toList_singleton,
              List.cons_append, List.nil_append, List.append_assoc]
          rw [currentEq, targetEq]
          exact derivesPrefixContext left right
            (derivesAdjacentDistinctSelfLoopContraction anchorWord)
      | cons middleHead middleTail =>
          let middleWord : Word Nat := ⟨middleHead, middleTail⟩
          have middleWordList :
              middleWord.toList = middleHead :: middleTail := rfl
          let sourceCore :=
            ((((anchorWord ++ anchorWord) ++ middleWord) ++
              anchorWord) ++ anchorWord)
          let targetCore :=
            (((anchorWord ++ anchorWord) ++ middleWord) ++ anchorWord)
          let sourceWord := prefixContext left sourceCore right
          let targetWord := prefixContext left targetCore right
          have currentEq : current = sourceWord := by
            apply Word.toList_injective
            rw [currentShape]
            simp only [sourceWord, prefixContext_toList, sourceCore,
              Word.toList_append, anchorWord, Word.toList_singleton,
              middleWordList, List.cons_append, List.nil_append,
              List.append_assoc]
          have targetEq : target = targetWord := by
            apply Word.toList_injective
            rw [targetShape]
            simp only [targetWord, prefixContext_toList, targetCore,
              Word.toList_append, anchorWord, Word.toList_singleton,
              middleWordList, List.cons_append, List.nil_append,
              List.append_assoc]
          rw [currentEq, targetEq]
          exact derivesPrefixContext left right
            (derivesSeparatedSelfLoopContraction
              anchorWord middleWord)
  | cons interiorHead interiorTail =>
      let interiorWord : Word Nat := ⟨interiorHead, interiorTail⟩
      have interiorWordList :
          interiorWord.toList = interiorHead :: interiorTail := rfl
      cases middle with
      | nil =>
          let sourceCore :=
            (((((anchorWord ++ interiorWord) ++ anchorWord) ++
              anchorWord) ++ interiorWord) ++ anchorWord)
          let targetCore :=
            (((anchorWord ++ interiorWord) ++ anchorWord) ++ anchorWord)
          let sourceWord := prefixContext left sourceCore right
          let targetWord := prefixContext left targetCore right
          have currentEq : current = sourceWord := by
            apply Word.toList_injective
            rw [currentShape]
            simp only [sourceWord, prefixContext_toList, sourceCore,
              Word.toList_append, anchorWord, Word.toList_singleton,
              interiorWordList, List.cons_append, List.nil_append,
              List.append_assoc]
          have targetEq : target = targetWord := by
            apply Word.toList_injective
            rw [targetShape]
            simp only [targetWord, prefixContext_toList, targetCore,
              Word.toList_append, anchorWord, Word.toList_singleton,
              interiorWordList, List.cons_append, List.nil_append,
              List.append_assoc]
          rw [currentEq, targetEq]
          exact derivesPrefixContext left right
            (derivesAdjacentDistinctClosedWalkContraction
              anchorWord interiorWord)
      | cons middleHead middleTail =>
          let middleWord : Word Nat := ⟨middleHead, middleTail⟩
          have middleWordList :
              middleWord.toList = middleHead :: middleTail := rfl
          let sourceCore :=
            ((((((anchorWord ++ interiorWord) ++ anchorWord) ++
              middleWord) ++ anchorWord) ++ interiorWord) ++ anchorWord)
          let targetCore :=
            ((((anchorWord ++ interiorWord) ++ anchorWord) ++
              middleWord) ++ anchorWord)
          let sourceWord := prefixContext left sourceCore right
          let targetWord := prefixContext left targetCore right
          have currentEq : current = sourceWord := by
            apply Word.toList_injective
            rw [currentShape]
            simp only [sourceWord, prefixContext_toList, sourceCore,
              Word.toList_append, anchorWord, Word.toList_singleton,
              interiorWordList, middleWordList, List.cons_append,
              List.nil_append, List.append_assoc]
          have targetEq : target = targetWord := by
            apply Word.toList_injective
            rw [targetShape]
            simp only [targetWord, prefixContext_toList, targetCore,
              Word.toList_append, anchorWord, Word.toList_singleton,
              interiorWordList, middleWordList, List.cons_append,
              List.nil_append, List.append_assoc]
          rw [currentEq, targetEq]
          exact derivesPrefixContext left right
            (derivesSeparatedClosedWalkContraction
              anchorWord interiorWord middleWord)

/-! ## Terminating reduction boundary -/

/-- The remaining local bridge: expose the complete prefix's occurrence of
the certified simple cycle, close it with the recorded edge, and apply the
appropriate adjacent/separated and ordinary/self-loop contraction above. -/
def CompleteSimpleCycleDeletion : Prop :=
  ∀ complete expanded : Word Nat, ∀ suffix : List Nat,
    TrahtmanIndecomposable complete →
      TrahtmanComplete complete →
        expanded.toList = complete.toList ++ suffix →
          complete.SameMarkedDigraph expanded →
            suffix ≠ [] →
              SuffixSimpleCycleCertificate complete suffix →
                ∃ reduced : Word Nat, ∃ reducedSuffix : List Nat,
                  Derives basis expanded reduced ∧
                    reduced.toList = complete.toList ++ reducedSuffix ∧
                      reducedSuffix.length < suffix.length

/-- The final occurrence-alignment boundary after the complete prefix already
contains a literal closed copy of the certified simple cycle. -/
def ExposedSuffixCycleDeletion : Prop :=
  ∀ complete expanded : Word Nat, ∀ suffix : List Nat,
    TrahtmanIndecomposable complete →
      TrahtmanComplete complete →
        expanded.toList = complete.toList ++ suffix →
          complete.SameMarkedDigraph expanded →
            suffix ≠ [] →
              ∀ certificate : SuffixSimpleCycleCertificate complete suffix,
                ClosedCycleExposure complete certificate.anchor
                    certificate.interior →
                  ∃ reduced : Word Nat, ∃ reducedSuffix : List Nat,
                    Derives basis expanded reduced ∧
                      reduced.toList = complete.toList ++ reducedSuffix ∧
                        reducedSuffix.length < suffix.length

theorem completeSimpleCycleDeletion_of_exposedSuffixCycleDeletion
    (deleteExposed : ExposedSuffixCycleDeletion) :
    CompleteSimpleCycleDeletion := by
  intro complete expanded suffix indecomposable completeWord shape
    sameGraph suffixNonempty certificate
  exact deleteExposed complete expanded suffix indecomposable completeWord
    shape sameGraph suffixNonempty certificate
      (closedCycleExposure indecomposable certificate)

/-- The exposed occurrence and the suffix occurrence can always be aligned in
raw-list contexts. If the suffix cycle starts at the marked final vertex, the
two copies may share that anchor; otherwise they have distinct occurrences.
The exact context lemmas above cover both possibilities and strictly shorten
the suffix. -/
theorem exposedSuffixCycleDeletion : ExposedSuffixCycleDeletion := by
  intro complete expanded suffix _ _ shape _ _ certificate exposure
  let exposedWithSuffix :=
    prefixAppendLetters exposure.exposed suffix
  have expandedEq : expanded = prefixAppendLetters complete suffix :=
    suffix_expanded_eq_appendLetters shape
  have expandedToExposed :
      Derives basis expanded exposedWithSuffix := by
    rw [expandedEq]
    exact derivesPrefixAppendLetters exposure.derivation suffix
  have exposedFinal : exposure.exposed.final = complete.final :=
    (derives_sameMarkedDigraph exposure.derivation).final.symm
  have exposureAfterFinal :
      exposure.after.getLastD certificate.anchor =
        exposure.exposed.final := by
    have lastEquality :=
      congrArg
        (fun letters : List Nat =>
          letters.getLastD certificate.anchor)
        exposure.shape
    simpa only [suffix_toList_getLastD, suffix_getLastD_append,
      List.getLastD_cons] using lastEquality.symm
  cases beforeShape : certificate.before with
  | nil =>
      have walkShape := certificate.walkShape
      rw [beforeShape] at walkShape
      simp only [suffixWalk_toList, List.nil_append] at walkShape
      injection walkShape with boundaryEq suffixShape
      cases afterShape : exposure.after with
      | nil =>
          let reducedSuffix := certificate.after
          let exposedReduced :=
            prefixAppendLetters exposure.exposed reducedSuffix
          let reduced := prefixAppendLetters complete reducedSuffix
          have localCurrentShape :
              exposedWithSuffix.toList =
                exposure.before ++
                  certificate.anchor :: certificate.interior ++
                    certificate.anchor :: certificate.interior ++
                      certificate.anchor :: certificate.after := by
            simp [exposedWithSuffix, exposure.shape, afterShape,
              suffixShape, List.append_assoc]
          have localTargetShape :
              exposedReduced.toList =
                exposure.before ++
                  certificate.anchor :: certificate.interior ++
                    certificate.anchor :: certificate.after := by
            simp [exposedReduced, reducedSuffix, exposure.shape,
              afterShape, List.append_assoc]
          have deleteCycle :
              Derives basis exposedWithSuffix exposedReduced :=
            derivesSharedClosedWalkContractionInContext
              exposedWithSuffix exposedReduced exposure.before
              certificate.interior certificate.after certificate.anchor
              localCurrentShape localTargetShape
          have restoreComplete : Derives basis exposedReduced reduced := by
            exact derivesPrefixAppendLetters exposure.derivation.symm
              reducedSuffix
          have reducedLength : reducedSuffix.length < suffix.length := by
            have lengthEq := congrArg List.length suffixShape
            simp [reducedSuffix] at lengthEq ⊢
            omega
          exact
            ⟨reduced, reducedSuffix,
              expandedToExposed.trans (deleteCycle.trans restoreComplete),
              by simp [reduced], reducedLength⟩
      | cons afterHead afterTail =>
          have afterLast :
              (afterHead :: afterTail).getLastD certificate.anchor =
                certificate.anchor := by
            calc
              (afterHead :: afterTail).getLastD certificate.anchor =
                  exposure.after.getLastD certificate.anchor := by
                rw [afterShape]
              _ = exposure.exposed.final := exposureAfterFinal
              _ = complete.final := exposedFinal
              _ = certificate.anchor := boundaryEq
          rcases suffix_exists_append_getLastD_cons afterHead
              certificate.anchor afterTail with
            ⟨middle, splitAfter⟩
          rw [afterLast] at splitAfter
          have exposureAfterShape :
              exposure.after = middle ++ [certificate.anchor] :=
            afterShape.trans splitAfter
          let reducedSuffix := certificate.after
          let exposedReduced :=
            prefixAppendLetters exposure.exposed reducedSuffix
          let reduced := prefixAppendLetters complete reducedSuffix
          have localCurrentShape :
              exposedWithSuffix.toList =
                exposure.before ++
                  certificate.anchor :: certificate.interior ++
                    certificate.anchor :: middle ++
                      certificate.anchor :: certificate.interior ++
                        certificate.anchor :: certificate.after := by
            simp [exposedWithSuffix, exposure.shape,
              exposureAfterShape, suffixShape, List.append_assoc]
          have localTargetShape :
              exposedReduced.toList =
                exposure.before ++
                  certificate.anchor :: certificate.interior ++
                    certificate.anchor :: middle ++
                      certificate.anchor :: certificate.after := by
            simp [exposedReduced, reducedSuffix, exposure.shape,
              exposureAfterShape, List.append_assoc]
          have deleteCycle :
              Derives basis exposedWithSuffix exposedReduced :=
            derivesDistinctClosedWalkContractionInContext
              exposedWithSuffix exposedReduced exposure.before
              certificate.interior middle certificate.after
              certificate.anchor localCurrentShape localTargetShape
          have restoreComplete : Derives basis exposedReduced reduced := by
            exact derivesPrefixAppendLetters exposure.derivation.symm
              reducedSuffix
          have reducedLength : reducedSuffix.length < suffix.length := by
            have lengthEq := congrArg List.length suffixShape
            simp [reducedSuffix] at lengthEq ⊢
            omega
          exact
            ⟨reduced, reducedSuffix,
              expandedToExposed.trans (deleteCycle.trans restoreComplete),
              by simp [reduced], reducedLength⟩
  | cons beforeHead beforeTail =>
      have walkShape := certificate.walkShape
      rw [beforeShape] at walkShape
      simp only [suffixWalk_toList, List.cons_append] at walkShape
      injection walkShape with _ suffixShape
      let middle := exposure.after ++ beforeTail
      let reducedSuffix :=
        beforeTail ++ certificate.anchor :: certificate.after
      let exposedReduced :=
        prefixAppendLetters exposure.exposed reducedSuffix
      let reduced := prefixAppendLetters complete reducedSuffix
      have localCurrentShape :
          exposedWithSuffix.toList =
            exposure.before ++
              certificate.anchor :: certificate.interior ++
                certificate.anchor :: middle ++
                  certificate.anchor :: certificate.interior ++
                    certificate.anchor :: certificate.after := by
        simp [exposedWithSuffix, exposure.shape, middle, suffixShape,
          List.append_assoc]
      have localTargetShape :
          exposedReduced.toList =
            exposure.before ++
              certificate.anchor :: certificate.interior ++
                certificate.anchor :: middle ++
                  certificate.anchor :: certificate.after := by
        simp [exposedReduced, reducedSuffix, exposure.shape, middle,
          List.append_assoc]
      have deleteCycle :
          Derives basis exposedWithSuffix exposedReduced :=
        derivesDistinctClosedWalkContractionInContext
          exposedWithSuffix exposedReduced exposure.before
          certificate.interior middle certificate.after
          certificate.anchor localCurrentShape localTargetShape
      have restoreComplete : Derives basis exposedReduced reduced := by
        exact derivesPrefixAppendLetters exposure.derivation.symm
          reducedSuffix
      have reducedLength : reducedSuffix.length < suffix.length := by
        have lengthEq := congrArg List.length suffixShape
        simp [reducedSuffix] at lengthEq ⊢
        omega
      exact
        ⟨reduced, reducedSuffix,
          expandedToExposed.trans (deleteCycle.trans restoreComplete),
          by simp [reduced], reducedLength⟩

/-- The certified simple-cycle deletion bridge is now unconditional. -/
theorem completeSimpleCycleDeletion : CompleteSimpleCycleDeletion :=
  completeSimpleCycleDeletion_of_exposedSuffixCycleDeletion
    exposedSuffixCycleDeletion

/-- One certified cycle deletion supplies a strict suffix-reduction step. -/
def CompleteSuffixReductionStep : Prop :=
  ∀ complete expanded : Word Nat, ∀ suffix : List Nat,
    TrahtmanIndecomposable complete →
      TrahtmanComplete complete →
        expanded.toList = complete.toList ++ suffix →
          complete.SameMarkedDigraph expanded →
            suffix ≠ [] →
              ∃ reduced : Word Nat, ∃ reducedSuffix : List Nat,
                Derives basis expanded reduced ∧
                  reduced.toList = complete.toList ++ reducedSuffix ∧
                    reducedSuffix.length < suffix.length

theorem completeSuffixReductionStep_of_simpleCycleDeletion
    (deleteCycle : CompleteSimpleCycleDeletion) :
    CompleteSuffixReductionStep := by
  intro complete expanded suffix indecomposable completeWord shape
    sameGraph suffixNonempty
  rcases existsSuffixSimpleCycleCertificate completeWord shape sameGraph
      suffixNonempty with
    ⟨certificate, _⟩
  exact deleteCycle complete expanded suffix indecomposable completeWord
    shape sameGraph suffixNonempty certificate

/-- Strict shortening of the explicit suffix is sufficient for Trahtman's
entire suffix-removal node. -/
theorem completeSuffixContraction_of_reductionStep
    (reduceSuffix : CompleteSuffixReductionStep) :
    CompleteSuffixContraction := by
  intro complete expanded suffix indecomposable completeWord shape sameGraph
  have inductionStatement :
      ∀ length,
        (∀ smaller < length,
          ∀ currentSuffix : List Nat, ∀ current : Word Nat,
            currentSuffix.length = smaller →
              current.toList = complete.toList ++ currentSuffix →
                complete.SameMarkedDigraph current →
                  Derives basis current complete) →
          ∀ currentSuffix : List Nat, ∀ current : Word Nat,
            currentSuffix.length = length →
              current.toList = complete.toList ++ currentSuffix →
                complete.SameMarkedDigraph current →
                  Derives basis current complete := by
    intro length smaller currentSuffix current lengthEq currentShape
      currentGraph
    by_cases suffixEmpty : currentSuffix = []
    · subst currentSuffix
      have currentEq : current = complete := by
        apply Word.toList_injective
        simpa using currentShape
      subst current
      exact Derives.refl complete
    · rcases reduceSuffix complete current currentSuffix
          indecomposable completeWord currentShape currentGraph suffixEmpty with
        ⟨reduced, reducedSuffix, currentReduced, reducedShape,
          reducedLength⟩
      have completeReducedGraph : complete.SameMarkedDigraph reduced :=
        sameMarkedDigraph_trans currentGraph
          (derives_sameMarkedDigraph currentReduced)
      have reducedComplete : Derives basis reduced complete :=
        smaller reducedSuffix.length (by omega) reducedSuffix reduced rfl
          reducedShape completeReducedGraph
      exact currentReduced.trans reducedComplete
  exact
    Nat.strongRecOn
      (motive := fun length =>
        ∀ currentSuffix : List Nat, ∀ current : Word Nat,
          currentSuffix.length = length →
            current.toList = complete.toList ++ currentSuffix →
              complete.SameMarkedDigraph current →
                Derives basis current complete)
      suffix.length inductionStatement suffix expanded rfl shape sameGraph

theorem completeSuffixContraction_of_simpleCycleDeletion
    (deleteCycle : CompleteSimpleCycleDeletion) :
    CompleteSuffixContraction :=
  completeSuffixContraction_of_reductionStep
    (completeSuffixReductionStep_of_simpleCycleDeletion deleteCycle)

theorem completeSuffixContraction_of_exposedSuffixCycleDeletion
    (deleteExposed : ExposedSuffixCycleDeletion) :
    CompleteSuffixContraction :=
  completeSuffixContraction_of_simpleCycleDeletion
    (completeSimpleCycleDeletion_of_exposedSuffixCycleDeletion
      deleteExposed)

/-- Trahtman's suffix-removal step: every appended closed walk with no new
support or edge contracts back to the complete prefix. -/
theorem completeSuffixContraction : CompleteSuffixContraction :=
  completeSuffixContraction_of_simpleCycleDeletion
    completeSimpleCycleDeletion

/-- The marked-graph theorem is now unconditional on each indecomposable
component. No maximal-factor assembly is used here. -/
theorem indecomposableMarkedDigraphDerivationalCompleteness :
    IndecomposableMarkedDigraphDerivationalCompleteness :=
  indecomposableMarkedDigraphDerivationalCompleteness_of_publishedSteps
    completeRepresentativeExistence completePrefixReachability
      completeSuffixContraction

/-- Exact remaining global boundary after suffix contraction. -/
theorem markedDigraphDerivationalCompleteness_of_maximalFactorReduction
    (reduceFactors : MaximalIndecomposableFactorReduction) :
    MarkedDigraphDerivationalCompleteness :=
  reduceFactors indecomposableMarkedDigraphDerivationalCompleteness

end SemigroupBasis.CoRoots.S5_868
