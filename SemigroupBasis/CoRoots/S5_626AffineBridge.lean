import SemigroupBasis.CoRoots.S5_626SegmentInduction

namespace SemigroupBasis.CoRoots.S5_626

open SemigroupBasis
open SemigroupBasis.Examples

/-- Reverse one left-to-right segment into the orientation used by the
`AffineParityFour` normalizer. -/
def dualFirstParitySegment
    (segment : FirstParitySegment) : AffineParitySegment :=
  ⟨segment.parity.reverse, segment.marker⟩

/-- Reverse the segment order as well as every parity block. -/
def dualFirstParitySegments
    (segments : List FirstParitySegment) :
    List AffineParitySegment :=
  (segments.map dualFirstParitySegment).reverse

@[simp]
theorem dualFirstParitySegments_append_singleton
    (segments : List FirstParitySegment)
    (segment : FirstParitySegment) :
    dualFirstParitySegments (segments ++ [segment]) =
      dualFirstParitySegment segment ::
        dualFirstParitySegments segments := by
  simp [dualFirstParitySegments]

private theorem affineParityMarkers_eq_map :
    ∀ segments : List AffineParitySegment,
      affineParityMarkers segments =
        segments.map fun segment => segment.marker
  | [] => rfl
  | segment :: rest => by
      simp [affineParityMarkers, affineParityMarkers_eq_map rest]

def firstParityMarkers
    (segments : List FirstParitySegment) : List Nat :=
  segments.map fun segment => segment.marker

theorem affineParityMarkers_dualFirstParitySegments
    (segments : List FirstParitySegment) :
    affineParityMarkers (dualFirstParitySegments segments) =
      (firstParityMarkers segments).reverse := by
  simp [affineParityMarkers_eq_map, dualFirstParitySegments,
    firstParityMarkers, dualFirstParitySegment,
    List.map_reverse, List.map_map]

private theorem affineParityRender_append :
    ∀ left right : List AffineParitySegment,
      affineParityRender (left ++ right) =
        affineParityRender left ++ affineParityRender right
  | [], _ => rfl
  | segment :: rest, right => by
      simp [affineParityRender,
        affineParityRender_append rest right,
        List.append_assoc]

theorem affineParityRender_dualFirstParitySegments :
    ∀ segments : List FirstParitySegment,
      affineParityRender (dualFirstParitySegments segments) =
        (renderFirstParitySegments segments).reverse
  | [] => rfl
  | segment :: rest => by
      rw [show
        dualFirstParitySegments (segment :: rest) =
          dualFirstParitySegments rest ++
            [dualFirstParitySegment segment] by
              simp [dualFirstParitySegments]]
      rw [affineParityRender_append,
        affineParityRender_dualFirstParitySegments rest]
      simp [dualFirstParitySegment, affineParityRender,
        renderFirstParitySegments, List.reverse_append,
        List.append_assoc]

theorem dualFirstParitySegments_ne_nil
    {segments : List FirstParitySegment}
    (nonempty : segments ≠ []) :
    dualFirstParitySegments segments ≠ [] := by
  intro empty
  have mappedEmpty :
      segments.map dualFirstParitySegment = [] := by
    simpa [dualFirstParitySegments] using
      congrArg List.reverse empty
  apply nonempty
  apply List.eq_nil_of_length_eq_zero
  simpa using congrArg List.length mappedEmpty

private theorem affineSegmentsPerm_markers :
    ∀ {left right : List AffineParitySegment},
      AffineParitySegmentsPerm left right →
        affineParityMarkers left = affineParityMarkers right
  | [], [], AffineParitySegmentsPerm.nil => rfl
  | _ :: _, _ :: _,
      AffineParitySegmentsPerm.cons _ restPerm => by
      simp [affineParityMarkers,
        affineSegmentsPerm_markers restPerm]

private theorem affineSegmentsPerm_normalRight :
    ∀ {left right : List AffineParitySegment},
      AffineParitySegmentsPerm left right →
      AffineParitySegmentsNormal left →
        AffineParitySegmentsNormal right
  | [], [], AffineParitySegmentsPerm.nil,
      AffineParitySegmentsNormal.nil =>
      AffineParitySegmentsNormal.nil
  | ⟨leftBlock, marker⟩ :: leftRest,
      ⟨rightBlock, .(marker)⟩ :: rightRest,
      AffineParitySegmentsPerm.cons blockPerm restPerm,
      AffineParitySegmentsNormal.cons
        leftNodup markerFresh leftGuard restNormal => by
      have rightNodup : rightBlock.Nodup :=
        blockPerm.nodup_iff.mp leftNodup
      have restMarkers := affineSegmentsPerm_markers restPerm
      apply AffineParitySegmentsNormal.cons rightNodup
      · rwa [← restMarkers]
      · intro letter member
        simpa only [restMarkers] using
          leftGuard letter ((blockPerm.mem_iff).mpr member)
      · exact affineSegmentsPerm_normalRight restPerm restNormal

private theorem nodupPerm
    {left right : List Nat}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (same : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left.Perm right := by
  rw [List.perm_iff_count]
  intro letter
  rw [leftNodup.count, rightNodup.count]
  simp only [same letter]

private theorem nodup_reverse
    {alpha : Type} {items : List alpha}
    (nodup : items.Nodup) : items.reverse.Nodup := by
  change items.reverse.Pairwise (fun left right : alpha => left ≠ right)
  rw [List.pairwise_reverse]
  exact nodup.imp fun different => Ne.symm different

private theorem affineToggle_perm_orderedToggle_reverse
    {seen parity block : List Nat} {letter : Nat}
    (seenNodup : seen.Nodup)
    (parityNodup : parity.Nodup)
    (paritySupport : ∀ tested, tested ∈ parity → tested ∈ seen)
    (letterSeen : letter ∈ seen)
    (blockPerm : block.Perm parity.reverse) :
    (affineParityToggle letter block).Perm
      (orderedParityToggle seen letter parity).reverse := by
  have blockNodup : block.Nodup :=
    blockPerm.nodup_iff.mpr (nodup_reverse parityNodup)
  have leftNodup : (affineParityToggle letter block).Nodup :=
    affineParityToggle_nodup letter blockNodup
  have rightNodup :
      (orderedParityToggle seen letter parity).reverse.Nodup :=
    nodup_reverse <|
      orderedParityToggle_nodup seenNodup letter parity
  apply nodupPerm leftNodup rightNodup
  intro tested
  have blockMembership : tested ∈ block ↔ tested ∈ parity := by
    rw [blockPerm.mem_iff]
    simp
  have letterMembership : letter ∈ block ↔ letter ∈ parity := by
    rw [blockPerm.mem_iff]
    simp
  by_cases same : tested = letter
  · subst tested
    by_cases present : letter ∈ parity
    · have inBlock := letterMembership.mpr present
      simp [affineParityToggle, orderedParityToggle,
        present, inBlock, letterSeen,
        blockNodup.mem_erase_iff]
    · have notInBlock : letter ∉ block :=
        fun member => present (letterMembership.mp member)
      simp [affineParityToggle, orderedParityToggle,
        present, notInBlock, letterSeen]
  · by_cases present : tested ∈ parity
    · have inBlock := blockMembership.mpr present
      have inSeen := paritySupport tested present
      by_cases letterInParity : letter ∈ parity
      · have letterInBlock := letterMembership.mpr letterInParity
        simp [affineParityToggle, orderedParityToggle, same,
          present, inBlock, inSeen, letterInParity, letterInBlock]
      · have letterNotInBlock : letter ∉ block :=
          fun member => letterInParity (letterMembership.mp member)
        simp [affineParityToggle, orderedParityToggle, same,
          present, inBlock, inSeen, letterInParity, letterNotInBlock]
    · have notInBlock : tested ∉ block :=
        fun member => present (blockMembership.mp member)
      by_cases letterInParity : letter ∈ parity
      · have letterInBlock := letterMembership.mpr letterInParity
        simp [affineParityToggle, orderedParityToggle, same,
          present, notInBlock, letterInParity, letterInBlock]
      · have letterNotInBlock : letter ∉ block :=
          fun member => letterInParity (letterMembership.mp member)
        simp [affineParityToggle, orderedParityToggle, same,
          present, notInBlock, letterInParity, letterNotInBlock]

/-- The exact induction state relating a processed left-to-right prefix to
the direct affine normal form of its reversal. -/
structure SegmentedAffineAlignment
    (seen : List Nat) (completed : List FirstParitySegment)
    (current : FirstParitySegment) (processed : List Nat) : Prop where
  seenMarkers :
    firstParityMarkers (completed ++ [current]) = seen
  seenNodup : seen.Nodup
  segments :
    AffineParitySegmentsPerm
      (affineParityNormalSegments processed.reverse)
      (dualFirstParitySegments (completed ++ [current]))

private theorem currentParity_support
    {seen : List Nat} {completed : List FirstParitySegment}
    {current : FirstParitySegment}
    (seenMarkers :
      firstParityMarkers (completed ++ [current]) = seen)
    (normal :
      AffineParitySegmentsNormal
        (dualFirstParitySegments (completed ++ [current]))) :
    ∀ tested, tested ∈ current.parity → tested ∈ seen := by
  rw [dualFirstParitySegments_append_singleton] at normal
  cases normal with
  | cons blockNodup markerFresh blockGuard restNormal =>
      intro tested member
      have reversedMember : tested ∈ current.parity.reverse := by
        simpa using member
      have guarded := blockGuard tested reversedMember
      have markerMember :
          tested ∈ affineParityMarkers
            (dualFirstParitySegments (completed ++ [current])) := by
        rw [dualFirstParitySegments_append_singleton,
          affineParityMarkers]
        simpa [dualFirstParitySegment] using guarded
      rw [affineParityMarkers_dualFirstParitySegments,
        seenMarkers] at markerMember
      simpa using markerMember

private theorem SegmentedAffineAlignment.appendFresh
    {seen : List Nat} {completed : List FirstParitySegment}
    {current : FirstParitySegment} {processed : List Nat}
    (alignment :
      SegmentedAffineAlignment seen completed current processed)
    (letter : Nat) (fresh : letter ∉ seen) :
    SegmentedAffineAlignment
      (seen ++ [letter]) (completed ++ [current])
      ⟨letter, []⟩ (processed ++ [letter]) := by
  have markerEq := affineSegmentsPerm_markers alignment.segments
  have rightAbsent :
      letter ∉ affineParityMarkers
        (dualFirstParitySegments (completed ++ [current])) := by
    rw [affineParityMarkers_dualFirstParitySegments,
      alignment.seenMarkers]
    simpa using fresh
  have leftAbsent :
      letter ∉ affineParityMarkers
        (affineParityNormalSegments processed.reverse) := by
    rw [markerEq]
    exact rightAbsent
  constructor
  · calc
      firstParityMarkers
          (completed ++ [current] ++ [⟨letter, []⟩]) =
          firstParityMarkers (completed ++ [current]) ++ [letter] := by
        simp [firstParityMarkers, List.map_append,
          List.append_assoc]
      _ = seen ++ [letter] :=
        congrArg (fun markers => markers ++ [letter])
          alignment.seenMarkers
  · apply List.nodup_append.mpr
    refine ⟨alignment.seenNodup, by simp, ?_⟩
    intro old oldMember new newMember equal
    simp only [List.mem_singleton] at newMember
    subst new
    subst old
    exact fresh oldMember
  · have nextShape :
        affineParityNormalSegments
            (processed ++ [letter]).reverse =
          ⟨[], letter⟩ ::
            affineParityNormalSegments processed.reverse := by
        cases sourceShape :
            affineParityNormalSegments processed.reverse with
        | nil =>
            simp [List.reverse_append, affineParityNormalSegments,
              sourceShape]
        | cons segment rest =>
            have absent :
                letter ∉ affineParityMarkers (segment :: rest) := by
              simpa [sourceShape] using leftAbsent
            simp [List.reverse_append, affineParityNormalSegments,
              sourceShape, absent]
    rw [nextShape, dualFirstParitySegments_append_singleton]
    simp only [dualFirstParitySegment, List.reverse_nil]
    exact AffineParitySegmentsPerm.cons
      (List.Perm.refl []) alignment.segments

private theorem SegmentedAffineAlignment.appendSeen
    {seen : List Nat} {completed : List FirstParitySegment}
    {current : FirstParitySegment} {processed : List Nat}
    (alignment :
      SegmentedAffineAlignment seen completed current processed)
    (letter : Nat) (letterSeen : letter ∈ seen) :
    SegmentedAffineAlignment seen completed
      ⟨current.marker,
        orderedParityToggle seen letter current.parity⟩
      (processed ++ [letter]) := by
  have leftNormal :=
    affineParityNormalSegments_normal processed.reverse
  have rightNormal :=
    affineSegmentsPerm_normalRight alignment.segments leftNormal
  have paritySupport :=
    currentParity_support alignment.seenMarkers rightNormal
  have markerEq := affineSegmentsPerm_markers alignment.segments
  have rightMember :
      letter ∈ affineParityMarkers
        (dualFirstParitySegments (completed ++ [current])) := by
    rw [affineParityMarkers_dualFirstParitySegments,
      alignment.seenMarkers]
    simpa using letterSeen
  have leftMember :
      letter ∈ affineParityMarkers
        (affineParityNormalSegments processed.reverse) := by
    rw [markerEq]
    exact rightMember
  have relation := alignment.segments
  rw [dualFirstParitySegments_append_singleton] at relation
  generalize sourceShape :
      affineParityNormalSegments processed.reverse = sourceSegments
    at relation
  cases relation with
  | @cons leftBlock rightBlock marker leftRest rightRest
      blockPerm restPerm =>
      have currentNodup : current.parity.Nodup := by
        rw [dualFirstParitySegments_append_singleton] at rightNormal
        cases rightNormal with
        | cons blockNodup markerFresh blockGuard restNormal =>
            simpa using nodup_reverse blockNodup
      have toggledPerm :=
        affineToggle_perm_orderedToggle_reverse
          alignment.seenNodup currentNodup paritySupport
          letterSeen blockPerm
      have sourceMember :
          letter ∈ affineParityMarkers
            (⟨leftBlock, current.marker⟩ :: leftRest) := by
        simpa [sourceShape] using leftMember
      constructor
      · simpa [firstParityMarkers] using alignment.seenMarkers
      · exact alignment.seenNodup
      · have nextShape :
            affineParityNormalSegments
                (processed ++ [letter]).reverse =
              ⟨affineParityToggle letter leftBlock, current.marker⟩ ::
                leftRest := by
            simp [List.reverse_append, affineParityNormalSegments,
              sourceMember, sourceShape]
        rw [nextShape,
          dualFirstParitySegments_append_singleton]
        exact AffineParitySegmentsPerm.cons toggledPerm restPerm

private theorem segmentedAffineAlignment_scanAux
    {seen : List Nat} {completed : List FirstParitySegment}
    {current : FirstParitySegment} {processed : List Nat}
    (alignment :
      SegmentedAffineAlignment seen completed current processed) :
    ∀ remaining,
      AffineParitySegmentsPerm
        (affineParityNormalSegments
          (processed ++ remaining).reverse)
        (dualFirstParitySegments
          (segmentedParityScanAux
            seen completed current remaining))
  | [] => by
      simpa [segmentedParityScanAux] using alignment.segments
  | letter :: rest => by
      by_cases old : letter ∈ seen
      · have next := alignment.appendSeen letter old
        simpa [segmentedParityScanAux, old,
          List.append_assoc] using
            segmentedAffineAlignment_scanAux next rest
      · have next := alignment.appendFresh letter old
        simpa [segmentedParityScanAux, old,
          List.append_assoc] using
            segmentedAffineAlignment_scanAux next rest

theorem segmentedAffineSegmentsPerm (word : Word Nat) :
    AffineParitySegmentsPerm
      (affineParityNormalSegments word.toList.reverse)
      (dualFirstParitySegments (segmentedParityScan word)) := by
  let current : FirstParitySegment := ⟨word.head, []⟩
  have start :
      SegmentedAffineAlignment
        [word.head] [] current [word.head] := by
    constructor
    · rfl
    · simp
    · simpa [current, dualFirstParitySegments,
        dualFirstParitySegment, affineParityNormalSegments] using
          (AffineParitySegmentsPerm.cons
            (List.Perm.refl []) AffineParitySegmentsPerm.nil)
  simpa [segmentedParityScan, Word.toList, current] using
    segmentedAffineAlignment_scanAux start word.tail

private def AffineSegmentsDerivable
    (left right : List AffineParitySegment) : Prop :=
  match left, right with
  | [], [] => True
  | leftHead :: leftRest, rightHead :: rightRest =>
      Derives affineParityFourBasis
        (affineParityRenderWord leftHead leftRest)
        (affineParityRenderWord rightHead rightRest)
  | _, _ => False

private theorem affineSegmentsPerm_derives :
    ∀ {left right : List AffineParitySegment},
      AffineParitySegmentsPerm left right →
      AffineParitySegmentsNormal left →
      AffineParitySegmentsNormal right →
        AffineSegmentsDerivable left right
  | [], [], AffineParitySegmentsPerm.nil,
      AffineParitySegmentsNormal.nil,
      AffineParitySegmentsNormal.nil => True.intro
  | ⟨leftBlock, marker⟩ :: leftRest,
      ⟨rightBlock, .(marker)⟩ :: rightRest,
      AffineParitySegmentsPerm.cons blockPerm restPerm,
      AffineParitySegmentsNormal.cons
        leftNodup leftFresh leftGuard leftRestNormal,
      AffineParitySegmentsNormal.cons
        rightNodup rightFresh rightGuard rightRestNormal => by
      let leftSuffix :=
        affineParityWordOfCons marker
          (affineParityRender leftRest)
      have blockGuard :
          ∀ tested, tested ∈ leftBlock →
            tested ∈ leftSuffix.toList := by
        intro tested member
        change tested ∈ marker :: affineParityRender leftRest
        rcases leftGuard tested member with rfl | restMember
        · exact List.Mem.head _
        · exact List.Mem.tail _ <|
            affineParityMarker_mem_render restMember
      have first :=
        affineParityDerivesGuardedPermutation
          leftSuffix blockPerm blockGuard
      cases restPerm with
      | nil =>
          simpa [AffineSegmentsDerivable,
            affineParityRenderWord, leftSuffix,
            affineParityRender] using first
      | @cons nextLeft nextRight nextMarker
          leftTail rightTail nextPerm tailPerm =>
          have tailDerivation :=
            affineSegmentsPerm_derives
              (AffineParitySegmentsPerm.cons nextPerm tailPerm)
              leftRestNormal rightRestNormal
          have underMarker :=
            Derives.prepend (Word.singleton marker) tailDerivation
          have underBlock :=
            affineParityPrependLetters_derivation
              rightBlock underMarker
          have leftWordEq :
              affineParityPrependLetters rightBlock
                  (Word.singleton marker ++
                    affineParityRenderWord
                      ⟨nextLeft, nextMarker⟩ leftTail) =
                affineParityRenderWord
                  ⟨rightBlock, marker⟩
                  (⟨nextLeft, nextMarker⟩ :: leftTail) := by
            apply Word.toList_injective
            rw [affineParityPrependLetters_toList,
              Word.toList_append, Word.toList_singleton,
              affineParityRenderWord_toList,
              affineParityRenderWord_toList]
            rfl
          have rightWordEq :
              affineParityPrependLetters rightBlock
                  (Word.singleton marker ++
                    affineParityRenderWord
                      ⟨nextRight, nextMarker⟩ rightTail) =
                affineParityRenderWord
                  ⟨rightBlock, marker⟩
                  (⟨nextRight, nextMarker⟩ :: rightTail) := by
            apply Word.toList_injective
            rw [affineParityPrependLetters_toList,
              Word.toList_append, Word.toList_singleton,
              affineParityRenderWord_toList,
              affineParityRenderWord_toList]
            rfl
          rw [leftWordEq, rightWordEq] at underBlock
          exact Derives.trans
            (by
              simpa [AffineSegmentsDerivable,
                affineParityRenderWord,
                leftSuffix] using first)
            underBlock

/-- Blockwise permutation-equivalent nonempty affine normal forms are
derivable in the direct affine basis.  This public wrapper is the owned bridge
needed by the combinatorial converse; the recursive implementation remains
private to this module. -/
theorem affineParitySegmentsPerm_derivesRendered
    {leftHead rightHead : AffineParitySegment}
    {leftRest rightRest : List AffineParitySegment}
    (segmentsPerm :
      AffineParitySegmentsPerm
        (leftHead :: leftRest) (rightHead :: rightRest))
    (leftNormal :
      AffineParitySegmentsNormal (leftHead :: leftRest))
    (rightNormal :
      AffineParitySegmentsNormal (rightHead :: rightRest)) :
    Derives affineParityFourBasis
      (affineParityRenderWord leftHead leftRest)
      (affineParityRenderWord rightHead rightRest) := by
  simpa [AffineSegmentsDerivable] using
    affineSegmentsPerm_derives segmentsPerm leftNormal rightNormal

theorem affineParityDerivesSegmentedBase (word : Word Nat) :
    Derives affineParityFourBasis word.reverse
      (segmentedParityBaseWord word).reverse := by
  have sourceDerivation := affineParityDerivesNormal word.reverse
  have sourceNormal :=
    affineParityNormalSegments_normal word.reverse.toList
  simp only [Word.toList_reverse] at sourceDerivation sourceNormal
  have segmentPerm := segmentedAffineSegmentsPerm word
  cases sourceShape :
      affineParityNormalSegments word.toList.reverse with
  | nil =>
      exact False.elim <|
        affineParityNormalSegments_cons_ne_nil
          word.reverse.head word.reverse.tail <| by
            change
              affineParityNormalSegments word.reverse.toList = []
            simpa using sourceShape
  | cons sourceHead sourceRest =>
      rw [sourceShape] at sourceDerivation sourceNormal segmentPerm
      cases targetShape :
          dualFirstParitySegments (segmentedParityScan word) with
      | nil =>
          exact False.elim <|
            dualFirstParitySegments_ne_nil
              (segmentedParityScan_ne_nil word) targetShape
      | cons targetHead targetRest =>
          rw [targetShape] at segmentPerm
          have targetNormal :=
            affineSegmentsPerm_normalRight segmentPerm sourceNormal
          have between :=
            affineSegmentsPerm_derives
              segmentPerm sourceNormal targetNormal
          have targetWordEq :
              affineParityRenderWord targetHead targetRest =
                (segmentedParityBaseWord word).reverse := by
            apply Word.toList_injective
            rw [affineParityRenderWord_toList,
              Word.toList_reverse,
              segmentedParityBaseWord_toList]
            have rendered :=
              affineParityRender_dualFirstParitySegments
                (segmentedParityScan word)
            rw [targetShape] at rendered
            exact rendered
          have between' :
              Derives affineParityFourBasis
                (affineParityRenderWord sourceHead sourceRest)
                (segmentedParityBaseWord word).reverse := by
            simpa [AffineSegmentsDerivable, targetWordEq] using between
          exact sourceDerivation.trans between'

theorem affineOppositeDerivesSegmentedBase (word : Word Nat) :
    Derives affineParityFourOppositeBasis word
      (segmentedParityBaseWord word) := by
  have reversed := (affineParityDerivesSegmentedBase word).reverse
  simpa [affineParityFourOppositeBasis] using reversed

theorem segmentedParityBaseWord_affineValid (word : Word Nat) :
    (Identity.mk word (segmentedParityBaseWord word)).SatisfiedBy
      affineParityFactorTable.semigroup.opposite := by
  intro valuation
  have evaluated :=
    (affineOppositeDerivesSegmentedBase word).sound
      affineParityFourOppositeBasis_complete.1 valuation
  simpa [affineParityFour] using evaluated

/-- The semantic bridge discharges the final parameter of the protected
segment induction for every repeated-initial word. -/
theorem derivesRepeatedInitialToSegmentedNormal_closed
    (word : Word Nat) (repeated : word.head ∈ word.tail) :
    Derives basis word (segmentedParityNormalWord word) :=
  derivesRepeatedInitialToSegmentedNormal word repeated
    (segmentedParityBaseWord_affineValid word)

end SemigroupBasis.CoRoots.S5_626
