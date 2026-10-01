import SemigroupBasis.CoRoots.Order6SporadicSection16CanonicalObservations

/-! Lee-Zhang (2015), Proposition16.1, uniqueness half. Ini and simplicity
fix the skeleton. A terminal marker discrepancy contradicts the simple-final
invariant; an internal discrepancy contradicts FSS. Every marker bit is thus
forced. No completeness or uniqueness assumption is added to the data. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection16

open SemigroupBasis CanonicalShape CanonicalObservations

theorem lemma16_2Invariants_symm {left right : Word Nat}
    (same : Lemma16_2Invariants left right) : Lemma16_2Invariants right left where
  toFactorInvariants := {
    ini := same.ini.symm
    capped := fun letter => (same.capped letter).symm
    simpleFinal := fun letter => (same.simpleFinal letter).symm }
  fss := fun source target => (same.fss source target).symm

theorem marked_head_transfer (left right : CanonicalData)
    (leftWF : CanonicalWellFormed left) (rightWF : CanonicalWellFormed right)
    (same : Lemma16_2Invariants (canonicalWord left) (canonicalWord right))
    (before beforeOther : List CanonicalBlock) (first other : CanonicalBlock)
    (rest otherRest : List CanonicalBlock)
    (leftSplit : left.blocks = before ++ first :: rest)
    (rightSplit : right.blocks = beforeOther ++ other :: otherRest)
    (shapes : (first :: rest).map blockShape = (other :: otherRest).map blockShape)
    (marked : first.markerAfter = true) : other.markerAfter = true := by
  have shapeParts := List.cons.inj shapes
  have letterEq : first.letter = other.letter := congrArg Prod.fst shapeParts.1
  have doubledEq : first.doubled = other.doubled := congrArg Prod.snd shapeParts.1
  have allAdmissible : AdmissibleMarkers (before ++ first :: rest) := by
    rw [← leftSplit]
    exact leftWF.2
  have admissible := admissible_suffix before (first :: rest) allAdmissible
  have simplicity := admissible.1 marked
  have otherSimple : other.doubled = false := doubledEq ▸ simplicity.1
  have falseIff : first.markerAfter = false ↔ other.markerAfter = false := by
    cases rest with
    | nil =>
        cases otherRest with
        | nil =>
            have leftObservation := terminal_simple_iff left leftWF before first leftSplit simplicity.1
            have rightObservation := terminal_simple_iff right rightWF beforeOther other rightSplit otherSimple
            have finalSame : S5_107.SimpleFinal (canonicalWord left) first.letter ↔
                S5_107.SimpleFinal (canonicalWord right) other.letter := by
              simpa only [letterEq] using same.simpleFinal first.letter
            exact leftObservation.symm.trans (finalSame.trans rightObservation)
        | cons next tail =>
            have impossible := shapeParts.2
            simp at impossible
    | cons next tail =>
        cases otherRest with
        | nil =>
            have impossible := shapeParts.2
            simp at impossible
        | cons nextOther tailOther =>
            have nextShapes := List.cons.inj shapeParts.2
            have nextLetterEq : next.letter = nextOther.letter := congrArg Prod.fst nextShapes.1
            have nextDoubledEq : next.doubled = nextOther.doubled := congrArg Prod.snd nextShapes.1
            have nextSimple : next.doubled = false := simplicity.2
            have nextOtherSimple : nextOther.doubled = false := nextDoubledEq ▸ nextSimple
            have leftObservation := neighboring_simple_pair_iff left leftWF before first next tail
              leftSplit simplicity.1 nextSimple
            have rightObservation := neighboring_simple_pair_iff right rightWF beforeOther other nextOther tailOther
              rightSplit otherSimple nextOtherSimple
            have fssSame : S5_107.SimpleAdjacent (canonicalWord left) first.letter next.letter ↔
                S5_107.SimpleAdjacent (canonicalWord right) other.letter nextOther.letter := by
              simpa only [letterEq, nextLetterEq] using same.fss first.letter next.letter
            exact leftObservation.symm.trans (fssSame.trans rightObservation)
  cases otherMarker : other.markerAfter with
  | true => rfl
  | false =>
      have impossible := falseIff.mpr otherMarker
      rw [marked] at impossible
      cases impossible

theorem head_marker_eq (left right : CanonicalData)
    (leftWF : CanonicalWellFormed left) (rightWF : CanonicalWellFormed right)
    (same : Lemma16_2Invariants (canonicalWord left) (canonicalWord right))
    (before beforeOther : List CanonicalBlock) (first other : CanonicalBlock)
    (rest otherRest : List CanonicalBlock)
    (leftSplit : left.blocks = before ++ first :: rest)
    (rightSplit : right.blocks = beforeOther ++ other :: otherRest)
    (shapes : (first :: rest).map blockShape = (other :: otherRest).map blockShape) :
    first.markerAfter = other.markerAfter := by
  have forward := marked_head_transfer left right leftWF rightWF same before beforeOther first other
    rest otherRest leftSplit rightSplit shapes
  have backward := marked_head_transfer right left rightWF leftWF (lemma16_2Invariants_symm same)
    beforeOther before other first otherRest rest rightSplit leftSplit shapes.symm
  cases firstMarker : first.markerAfter <;> cases otherMarker : other.markerAfter
  · rfl
  · have impossible := backward otherMarker
    simp only [firstMarker, Bool.false_eq_true] at impossible
  · have impossible := forward firstMarker
    simp only [otherMarker, Bool.false_eq_true] at impossible
  · rfl

theorem suffix_blocks_eq (left right : CanonicalData)
    (leftWF : CanonicalWellFormed left) (rightWF : CanonicalWellFormed right)
    (same : Lemma16_2Invariants (canonicalWord left) (canonicalWord right)) :
    ∀ (blocks otherBlocks before beforeOther : List CanonicalBlock),
      left.blocks = before ++ blocks → right.blocks = beforeOther ++ otherBlocks →
      blocks.map blockShape = otherBlocks.map blockShape → blocks = otherBlocks
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, shapes => by simp at shapes
  | _ :: _, [], _, _, _, _, shapes => by simp at shapes
  | first :: rest, other :: otherRest, before, beforeOther, leftSplit, rightSplit, shapes => by
      have shapeParts := List.cons.inj shapes
      have markerEq := head_marker_eq left right leftWF rightWF same before beforeOther first other
        rest otherRest leftSplit rightSplit shapes
      have firstEq : first = other := by
        cases first with
        | mk firstLetter firstDoubled firstMarker =>
            cases other with
            | mk otherLetter otherDoubled otherMarker =>
                have letterEq : firstLetter = otherLetter := congrArg Prod.fst shapeParts.1
                have doubledEq : firstDoubled = otherDoubled := congrArg Prod.snd shapeParts.1
                cases letterEq
                cases doubledEq
                cases markerEq
                rfl
      have leftRest : left.blocks = (before ++ [first]) ++ rest := by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using leftSplit
      have rightRest : right.blocks = (beforeOther ++ [other]) ++ otherRest := by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using rightSplit
      have restEq := suffix_blocks_eq left right leftWF rightWF same rest otherRest
        (before ++ [first]) (beforeOther ++ [other]) leftRest rightRest shapeParts.2
      rw [firstEq, restEq]

theorem canonicalWord_unique (left right : CanonicalData)
    (leftWF : CanonicalWellFormed left) (rightWF : CanonicalWellFormed right)
    (same : Lemma16_2Invariants (canonicalWord left) (canonicalWord right)) :
    canonicalWord left = canonicalWord right := by
  have skeleton := same_skeleton left right leftWF rightWF same.toFactorInvariants
  have blocks := suffix_blocks_eq left right leftWF rightWF same left.blocks right.blocks [] []
    rfl rfl skeleton.2.2
  apply Word.toList_injective
  rw [canonicalWord_toList, canonicalWord_toList]
  simp only [renderCanonical, skeleton.1, skeleton.2.1, blocks]

#print axioms lemma16_2Invariants_symm
#print axioms marked_head_transfer
#print axioms head_marker_eq
#print axioms suffix_blocks_eq
#print axioms canonicalWord_unique

end SemigroupBasis.CoRoots.Order6SporadicSection16
