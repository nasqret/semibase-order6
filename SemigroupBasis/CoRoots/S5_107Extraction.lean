import SemigroupBasis.CoRoots.S5_107
import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_107Syntax

namespace SemigroupBasis.CoRoots.S5_107

open SemigroupBasis

/-- The ten arrangements connected by the nine attachment identities.
The constructor names record the order of the two copies of `x`, the two
copies of `y`, and the nonempty block `z`. -/
inductive AttachmentShape where
  | xxyzy
  | xxzyy
  | xyxzy
  | xyyzx
  | xyzxy
  | xyzyx
  | xzxyy
  | xzyxy
  | xzyyx
  | yxxzy
  deriving DecidableEq

/-- Render an attachment shape with singleton repeated letters and an
arbitrary nonempty block. -/
def renderAttachmentShape
    (shape : AttachmentShape)
    (x y : Nat) (z : List Nat) : List Nat :=
  match shape with
  | .xxyzy => [x, x, y] ++ z ++ [y]
  | .xxzyy => [x, x] ++ z ++ [y, y]
  | .xyxzy => [x, y, x] ++ z ++ [y]
  | .xyyzx => [x, y, y] ++ z ++ [x]
  | .xyzxy => [x, y] ++ z ++ [x, y]
  | .xyzyx => [x, y] ++ z ++ [y, x]
  | .xzxyy => [x] ++ z ++ [x, y, y]
  | .xzyxy => [x] ++ z ++ [y, x, y]
  | .xzyyx => [x] ++ z ++ [y, y, x]
  | .yxxzy => [y, x, x] ++ z ++ [y]

/-- Every attachment arrangement is derivable from the common
`x²yzy` arrangement. -/
theorem listDerivesAttachmentFromBase
    (shape : AttachmentShape)
    (x y zHead : Nat) (zTail : List Nat) :
    ListDerives basis
      (renderAttachmentShape .xxyzy x y (zHead :: zTail))
      (renderAttachmentShape shape x y (zHead :: zTail)) := by
  cases shape with
  | xxyzy =>
      exact ListDerives.refl _
  | xxzyy =>
      simpa [renderAttachmentShape, listWordOfCons, Word.append,
        Word.singleton, List.append_assoc] using
          (ListDerives.ofWord <|
            derivesAttachmentXXZYY
              (Word.singleton x)
              (Word.singleton y)
              (listWordOfCons zHead zTail))
  | xyxzy =>
      simpa [renderAttachmentShape, listWordOfCons, Word.append,
        Word.singleton, List.append_assoc] using
          (ListDerives.ofWord <|
            derivesAttachmentXYXZY
              (Word.singleton x)
              (Word.singleton y)
              (listWordOfCons zHead zTail))
  | xyyzx =>
      simpa [renderAttachmentShape, listWordOfCons, Word.append,
        Word.singleton, List.append_assoc] using
          (ListDerives.ofWord <|
            derivesAttachmentXYYZX
              (Word.singleton x)
              (Word.singleton y)
              (listWordOfCons zHead zTail))
  | xyzxy =>
      simpa [renderAttachmentShape, listWordOfCons, Word.append,
        Word.singleton, List.append_assoc] using
          (ListDerives.ofWord <|
            derivesAttachmentXYZXY
              (Word.singleton x)
              (Word.singleton y)
              (listWordOfCons zHead zTail))
  | xyzyx =>
      simpa [renderAttachmentShape, listWordOfCons, Word.append,
        Word.singleton, List.append_assoc] using
          (ListDerives.ofWord <|
            derivesAttachmentXYZYX
              (Word.singleton x)
              (Word.singleton y)
              (listWordOfCons zHead zTail))
  | xzxyy =>
      simpa [renderAttachmentShape, listWordOfCons, Word.append,
        Word.singleton, List.append_assoc] using
          (ListDerives.ofWord <|
            derivesAttachmentXZXYY
              (Word.singleton x)
              (Word.singleton y)
              (listWordOfCons zHead zTail))
  | xzyxy =>
      simpa [renderAttachmentShape, listWordOfCons, Word.append,
        Word.singleton, List.append_assoc] using
          (ListDerives.ofWord <|
            derivesAttachmentXZYXY
              (Word.singleton x)
              (Word.singleton y)
              (listWordOfCons zHead zTail))
  | xzyyx =>
      simpa [renderAttachmentShape, listWordOfCons, Word.append,
        Word.singleton, List.append_assoc] using
          (ListDerives.ofWord <|
            derivesAttachmentXZYYX
              (Word.singleton x)
              (Word.singleton y)
              (listWordOfCons zHead zTail))
  | yxxzy =>
      simpa [renderAttachmentShape, listWordOfCons, Word.append,
        Word.singleton, List.append_assoc] using
          (ListDerives.ofWord <|
            derivesAttachmentYXXZY
              (Word.singleton x)
              (Word.singleton y)
              (listWordOfCons zHead zTail))

/-- Any two attachment arrangements with the same repeated letters and
nonempty block are mutually derivable. -/
theorem listDerivesAttachmentShapes
    (source target : AttachmentShape)
    (x y zHead : Nat) (zTail : List Nat) :
    ListDerives basis
      (renderAttachmentShape source x y (zHead :: zTail))
      (renderAttachmentShape target x y (zHead :: zTail)) :=
  (listDerivesAttachmentFromBase
      source x y zHead zTail).symm.trans
    (listDerivesAttachmentFromBase
      target x y zHead zTail)

/-- Retarget a block bracketed by `y` to the repeated anchor `x`, leaving a
square of `y` behind. This is the principal local extraction move. -/
theorem listDerivesRetargetAttachmentBlock
    (x y zHead : Nat) (zTail : List Nat) :
    ListDerives basis
      (renderAttachmentShape .xxyzy x y (zHead :: zTail))
      (renderAttachmentShape .xzxyy x y (zHead :: zTail)) :=
  listDerivesAttachmentShapes
    .xxyzy .xzxyy x y zHead zTail

/-- Change the leading repeated letter from `x` to `y` while retaining the
same nonempty attachment block. -/
theorem listDerivesChangeLeadingAttachment
    (x y zHead : Nat) (zTail : List Nat) :
    ListDerives basis
      (renderAttachmentShape .xxyzy x y (zHead :: zTail))
      (renderAttachmentShape .yxxzy x y (zHead :: zTail)) :=
  listDerivesAttachmentShapes
    .xxyzy .yxxzy x y zHead zTail

/-- Retarget a square-ended nonempty factor to the preceding square. -/
theorem listDerivesRetargetSquaredBlock
    (x y zHead : Nat) (zTail : List Nat) :
    ListDerives basis
      ([x, x] ++ (zHead :: zTail) ++ [y, y])
      ([x] ++ (zHead :: zTail) ++ [x, y, y]) := by
  simpa [renderAttachmentShape, List.append_assoc] using
    listDerivesAttachmentShapes
      .xxzyy .xzxyy x y zHead zTail

/-- Move a leading square past a block already bracketed by another marker.
The bracketing marker becomes the new leading marker and the old one remains
as a square in the tail. -/
theorem listDerivesChangeAnchoredLeadingSquare
    (x y zHead : Nat) (zTail : List Nat) :
    ListDerives basis
      ([x, x, y] ++ (zHead :: zTail) ++ [y])
      ([y] ++ (zHead :: zTail) ++ [y, x, x]) := by
  have first :=
    listDerivesAttachmentShapes
      .xxyzy .xyyzx x y zHead zTail
  have second :=
    listDerivesAttachmentShapes
      .yxxzy .xzxyy y x zHead zTail
  have firstStep :
      ListDerives basis
        ([x, x, y] ++ (zHead :: zTail) ++ [y])
        ([x, y, y] ++ (zHead :: zTail) ++ [x]) := by
    simpa [renderAttachmentShape,
      List.append_assoc] using first
  have secondStep :
      ListDerives basis
        ([x, y, y] ++ (zHead :: zTail) ++ [x])
        ([y] ++ (zHead :: zTail) ++ [y, x, x]) := by
    simpa [renderAttachmentShape,
      List.append_assoc] using second
  exact firstStep.trans secondStep

/-- Install the terminating marker of a square-ended nonempty factor as the
leading anchor, moving the old leading square into the square tail. -/
theorem listDerivesInstallFactorMarkerAsAnchor
    (x y zHead : Nat) (zTail : List Nat) :
    ListDerives basis
      ([x, x] ++ (zHead :: zTail) ++ [y, y])
      ([y] ++ (zHead :: zTail) ++ [y, x, x]) := by
  have expose :=
    listDerivesAttachmentShapes
      .xxzyy .xxyzy x y zHead zTail
  have exposeStep :
      ListDerives basis
        ([x, x] ++ (zHead :: zTail) ++ [y, y])
        ([x, x, y] ++ (zHead :: zTail) ++ [y]) := by
    simpa [renderAttachmentShape,
      List.append_assoc] using expose
  exact exposeStep.trans
    (listDerivesChangeAnchoredLeadingSquare
      x y zHead zTail)

/-- Duplicate the left occurrence of a letter with an explicitly displayed
later occurrence. -/
theorem listDerivesExpandLeftOccurrence
    (x : Nat) :
    ∀ middle : List Nat,
      ListDerives basis
        ([x] ++ middle ++ [x])
        ([x, x] ++ middle ++ [x])
  | [] => by
      simpa [Word.singleton, Word.append] using
        (ListDerives.ofWord <|
          derivesTwoToThree (Word.singleton x))
  | head :: tail => by
      simpa [listWordOfCons, Word.singleton, Word.append,
        List.append_assoc] using
          (ListDerives.ofWord <|
            derivesLeftEndpointExpansion
              (Word.singleton x)
              (listWordOfCons head tail))

/-- Duplicate the right occurrence of a letter with an explicitly displayed
earlier occurrence. -/
theorem listDerivesExpandRightOccurrence
    (x : Nat) :
    ∀ middle : List Nat,
      ListDerives basis
        ([x] ++ middle ++ [x])
        ([x] ++ middle ++ [x, x])
  | [] => by
      simpa [Word.singleton, Word.append] using
        (ListDerives.ofWord <|
          derivesTwoToThree (Word.singleton x))
  | head :: tail => by
      simpa [listWordOfCons, Word.singleton, Word.append,
        List.append_assoc] using
          (ListDerives.ofWord <|
            derivesRightEndpointExpansion
              (Word.singleton x)
              (listWordOfCons head tail))

/-- A letter occurring at least twice admits a split displaying two selected
occurrences. Additional occurrences may remain in any of the three pieces. -/
theorem exists_two_occurrence_split_of_count_ge_two
    (x : Nat) :
    ∀ {letters : List Nat},
      2 ≤ letters.count x →
        ∃ before middle after,
          letters =
            before ++ x :: middle ++ x :: after
  | [], count => by
      simp at count
  | first :: rest, count => by
      by_cases equality : first = x
      · subst first
        have restPositive : 0 < rest.count x := by
          simp only [List.count_cons_self] at count
          omega
        have restMember : x ∈ rest :=
          List.count_pos_iff.mp restPositive
        obtain ⟨middle, after, split⟩ :=
          List.mem_iff_append.mp restMember
        exact
          ⟨[], middle, after, by simp [split, List.append_assoc]⟩
      · have restCount : 2 ≤ rest.count x := by
          simpa [equality] using count
        obtain ⟨before, middle, after, split⟩ :=
          exists_two_occurrence_split_of_count_ge_two
            x restCount
        exact
          ⟨first :: before, middle, after,
            by simp [split, List.append_assoc]⟩

/-- Square two explicitly displayed occurrences inside arbitrary prefix and
suffix context. -/
theorem listDerivesExpandTwoOccurrences
    (x : Nat) (before middle after : List Nat) :
    ListDerives basis
      (before ++ [x] ++ middle ++ [x] ++ after)
      (before ++ [x, x] ++ middle ++ [x, x] ++ after) := by
  have first :=
    (listDerivesExpandLeftOccurrence x middle).context
      before after
  have second :=
    (listDerivesExpandRightOccurrence x middle).context
      (before ++ [x]) after
  have firstStep :
      ListDerives basis
        (before ++ [x] ++ middle ++ [x] ++ after)
        (before ++ [x, x] ++ middle ++ [x] ++ after) := by
    simpa [List.append_assoc] using first
  have secondStep :
      ListDerives basis
        (before ++ [x, x] ++ middle ++ [x] ++ after)
        (before ++ [x, x] ++ middle ++ [x, x] ++ after) := by
    simpa [List.append_assoc] using second
  exact firstStep.trans secondStep

/-- Every globally repeated letter can have two selected occurrences squared
by a derivation that leaves all surrounding context explicit. -/
theorem exists_listDerivesExpandTwoOccurrences
    (letters : List Nat) (x : Nat)
    (multiple : 2 ≤ letters.count x) :
    ∃ before middle after,
      letters =
          before ++ [x] ++ middle ++ [x] ++ after ∧
        ListDerives basis letters
          (before ++ [x, x] ++ middle ++ [x, x] ++ after) := by
  obtain ⟨before, middle, after, split⟩ :=
    exists_two_occurrence_split_of_count_ge_two x multiple
  refine ⟨before, middle, after, ?_, ?_⟩
  · simpa [List.append_assoc] using split
  · rw [split]
    simpa [List.append_assoc] using
      listDerivesExpandTwoOccurrences x before middle after

/-- Duplicate one selected occurrence of a globally repeated letter. The
second occurrence may lie on either side of the selected position. -/
theorem listDerivesDuplicateSelectedOccurrence
    (x : Nat) (before after : List Nat)
    (multiple :
      2 ≤ (before ++ [x] ++ after).count x) :
    ListDerives basis
      (before ++ [x] ++ after)
      (before ++ [x, x] ++ after) := by
  by_cases afterMember : x ∈ after
  · obtain ⟨middle, suffix, split⟩ :=
      List.mem_iff_append.mp afterMember
    have expanded :=
      (listDerivesExpandLeftOccurrence x middle).context
        before suffix
    simpa [split, List.append_assoc] using expanded
  · have beforeMember : x ∈ before := by
      apply Classical.byContradiction
      intro beforeAbsent
      have beforeZero : before.count x = 0 :=
        List.count_eq_zero.mpr beforeAbsent
      have afterZero : after.count x = 0 :=
        List.count_eq_zero.mpr afterMember
      have countOne :
          (before ++ [x] ++ after).count x = 1 := by
        simp [List.count_append, beforeZero, afterZero]
      rw [countOne] at multiple
      omega
    obtain ⟨beforePrefix, middle, split⟩ :=
      List.mem_iff_append.mp beforeMember
    have expanded :=
      (listDerivesExpandRightOccurrence x middle).context
        beforePrefix after
    simpa [split, List.append_assoc] using expanded

/-- Expand one selected occurrence of a globally repeated letter to four
consecutive copies. -/
theorem listDerivesQuadrupleSelectedOccurrence
    (x : Nat) (before after : List Nat)
    (multiple :
      2 ≤ (before ++ [x] ++ after).count x) :
    ListDerives basis
      (before ++ [x] ++ after)
      (before ++ [x, x, x, x] ++ after) := by
  have duplicate :=
    listDerivesDuplicateSelectedOccurrence
      x before after multiple
  have squareToFourth :=
    (ListDerives.ofWord <|
      derivesTwoToFour (Word.singleton x)).context
        before after
  exact duplicate.trans <| by
    simpa [Word.singleton, Word.append,
      List.append_assoc] using squareToFourth

/-- Prepend another square-controlled block to a middle that is already
anchored at `anchor`. One existing anchor inside the middle permits the final
anchor occurrence to be duplicated; the attachment calculation then moves
the leading square into the square tail. -/
theorem listDerivesPrependToAnchoredMiddle
    (x anchor zHead : Nat) (zTail suffix : List Nat)
    (anchorInMiddle : anchor ∈ zHead :: zTail) :
    ListDerives basis
      ([x, x] ++ (zHead :: zTail) ++ [anchor] ++ suffix)
      ([anchor] ++ (zHead :: zTail) ++
        [anchor, x, x] ++ suffix) := by
  have middlePositive :
      0 < (zHead :: zTail).count anchor :=
    List.count_pos_iff.mpr anchorInMiddle
  have anchorMultiple :
      2 ≤
        (([x, x] ++ (zHead :: zTail)) ++
          [anchor] ++ suffix).count anchor := by
    have singletonCount :
        [anchor].count anchor = 1 := by
      simp
    rw [List.count_append, List.count_append,
      List.count_append, singletonCount]
    omega
  have duplicate :=
    listDerivesDuplicateSelectedOccurrence
      anchor
      ([x, x] ++ (zHead :: zTail))
      suffix
      anchorMultiple
  have duplicateStep :
      ListDerives basis
        ([x, x] ++ (zHead :: zTail) ++ [anchor] ++ suffix)
        ([x, x] ++ (zHead :: zTail) ++
          [anchor, anchor] ++ suffix) := by
    simpa [List.append_assoc] using duplicate
  have install :=
    (listDerivesInstallFactorMarkerAsAnchor
      x anchor zHead zTail).append suffix
  have installStep :
      ListDerives basis
        ([x, x] ++ (zHead :: zTail) ++
          [anchor, anchor] ++ suffix)
        ([anchor] ++ (zHead :: zTail) ++
          [anchor, x, x] ++ suffix) := by
    simpa [List.append_assoc] using install
  exact duplicateStep.trans installStep

/-- List-level anchored block swap for arbitrary nonempty blocks. -/
private theorem listDerivesAnchoredBlockSwapLists
    (anchor : Nat) {left right : List Nat}
    (leftNonempty : left ≠ [])
    (rightNonempty : right ≠ []) :
    ListDerives basis
      ([anchor] ++ left ++ [anchor] ++ right ++ [anchor])
      ([anchor] ++ right ++ [anchor] ++ left ++ [anchor]) := by
  obtain ⟨leftHead, leftTail, rfl⟩ :=
    List.exists_cons_of_ne_nil leftNonempty
  obtain ⟨rightHead, rightTail, rfl⟩ :=
    List.exists_cons_of_ne_nil rightNonempty
  simpa [listWordOfCons, Word.toList, Word.singleton,
    Word.append, List.append_assoc] using
      (ListDerives.ofWord <|
        derivesAnchoredBlockSwap
          (Word.singleton anchor)
          (listWordOfCons leftHead leftTail)
          (listWordOfCons rightHead rightTail))

/-- Lee's factor-swap calculation after the controller and the two factor
markers have been expanded. The proof follows Lemma 5.2(i): two square
moves expose an anchored `xyxzx` pattern, the block-swap law exchanges the
factors, and the square moves are reversed. -/
theorem listDerivesExpandedFactorSwap
    (controller leftMarker rightMarker : Nat)
    (leftBlock rightBlock : List Nat) :
    ListDerives basis
      ([controller, controller, controller, controller] ++
        leftBlock ++ [leftMarker, leftMarker] ++
        rightBlock ++ [rightMarker, rightMarker])
      ([controller, controller, controller, controller] ++
        rightBlock ++ [rightMarker, rightMarker] ++
        leftBlock ++ [leftMarker, leftMarker]) := by
  let firstMiddle : Word Nat :=
    listWordOfCons controller (controller :: leftBlock)
  have firstMoveCore :=
    ListDerives.ofWord <|
      derivesSquareMove
        (Word.singleton controller)
        firstMiddle
        (Word.singleton leftMarker)
  have firstMove :
      ListDerives basis
        ([controller, controller, controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker] ++
          rightBlock ++ [rightMarker, rightMarker])
        ([controller, controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker, controller] ++
          rightBlock ++ [rightMarker, rightMarker]) := by
    simpa [firstMiddle, listWordOfCons, Word.toList,
      Word.singleton, Word.append, List.append_assoc] using
        firstMoveCore.append
          (rightBlock ++ [rightMarker, rightMarker])

  let secondMiddle : Word Nat :=
    listWordOfCons controller
      (leftBlock ++
        [leftMarker, leftMarker, controller] ++ rightBlock)
  have secondMove :
      ListDerives basis
        ([controller, controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker, controller] ++
          rightBlock ++ [rightMarker, rightMarker])
        ([controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker, controller] ++
          rightBlock ++
            [rightMarker, rightMarker, controller]) := by
    simpa [secondMiddle, listWordOfCons, Word.toList,
      Word.singleton, Word.append, List.append_assoc] using
        (ListDerives.ofWord <|
          derivesSquareMove
            (Word.singleton controller)
            secondMiddle
            (Word.singleton rightMarker))

  have swapCore :=
    listDerivesAnchoredBlockSwapLists
      controller
      (left := leftBlock ++ [leftMarker, leftMarker])
      (right := rightBlock ++ [rightMarker, rightMarker])
      (by simp) (by simp)
  have swapped :
      ListDerives basis
        ([controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker, controller] ++
          rightBlock ++
            [rightMarker, rightMarker, controller])
        ([controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker, controller] ++
          leftBlock ++
            [leftMarker, leftMarker, controller]) := by
    simpa [Word.toList, Word.singleton, Word.append,
      List.append_assoc] using
      swapCore.prepend [controller]

  let thirdMiddle : Word Nat :=
    listWordOfCons controller
      (rightBlock ++
        [rightMarker, rightMarker, controller] ++ leftBlock)
  have thirdMoveForward :=
    ListDerives.ofWord <|
      derivesSquareMove
        (Word.singleton controller)
        thirdMiddle
        (Word.singleton leftMarker)
  have thirdMove :
      ListDerives basis
        ([controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker, controller] ++
          leftBlock ++
            [leftMarker, leftMarker, controller])
        ([controller, controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker, controller] ++
          leftBlock ++ [leftMarker, leftMarker]) := by
    simpa [thirdMiddle, listWordOfCons, Word.toList,
      Word.singleton, Word.append, List.append_assoc] using
        thirdMoveForward.symm

  let fourthMiddle : Word Nat :=
    listWordOfCons controller (controller :: rightBlock)
  have fourthMoveCore :=
    ListDerives.ofWord <|
      derivesSquareMove
        (Word.singleton controller)
        fourthMiddle
        (Word.singleton rightMarker)
  have fourthMove :
      ListDerives basis
        ([controller, controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker, controller] ++
          leftBlock ++ [leftMarker, leftMarker])
        ([controller, controller, controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker] ++
          leftBlock ++ [leftMarker, leftMarker]) := by
    simpa [fourthMiddle, listWordOfCons, Word.toList,
      Word.singleton, Word.append, List.append_assoc] using
        fourthMoveCore.symm.append
          (leftBlock ++ [leftMarker, leftMarker])

  exact
    firstMove.trans <|
      secondMove.trans <|
        swapped.trans <|
          thirdMove.trans fourthMove

/-- Swap two adjacent square-ended factors using the square at the end of the
preceding factor as controller. -/
theorem listDerivesSquaredFactorSwapAfterController
    (before controllerBlock leftBlock rightBlock after : List Nat)
    (controller leftMarker rightMarker : Nat) :
    ListDerives basis
      (before ++ controllerBlock ++ [controller, controller] ++
        leftBlock ++ [leftMarker, leftMarker] ++
        rightBlock ++ [rightMarker, rightMarker] ++ after)
      (before ++ controllerBlock ++ [controller, controller] ++
        rightBlock ++ [rightMarker, rightMarker] ++
        leftBlock ++ [leftMarker, leftMarker] ++ after) := by
  have expandController :=
    (ListDerives.ofWord <|
      derivesTwoToFour (Word.singleton controller)).context
        (before ++ controllerBlock)
        (leftBlock ++ [leftMarker, leftMarker] ++
          rightBlock ++ [rightMarker, rightMarker] ++ after)
  have expandStep :
      ListDerives basis
        (before ++ controllerBlock ++ [controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker] ++
          rightBlock ++ [rightMarker, rightMarker] ++ after)
        (before ++ controllerBlock ++
          [controller, controller, controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker] ++
          rightBlock ++ [rightMarker, rightMarker] ++ after) := by
    simpa [Word.toList, Word.singleton, Word.append,
      List.append_assoc] using expandController
  have swapStep :=
    (listDerivesExpandedFactorSwap
      controller leftMarker rightMarker
      leftBlock rightBlock).context
        (before ++ controllerBlock) after
  have swapStep' :
      ListDerives basis
        (before ++ controllerBlock ++
          [controller, controller, controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker] ++
          rightBlock ++ [rightMarker, rightMarker] ++ after)
        (before ++ controllerBlock ++
          [controller, controller, controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker] ++
          leftBlock ++ [leftMarker, leftMarker] ++ after) := by
    simpa [List.append_assoc] using swapStep
  have contractController :=
    (ListDerives.ofWord <|
      derivesFourToTwo (Word.singleton controller)).context
        (before ++ controllerBlock)
        (rightBlock ++ [rightMarker, rightMarker] ++
          leftBlock ++ [leftMarker, leftMarker] ++ after)
  have contractStep :
      ListDerives basis
        (before ++ controllerBlock ++
          [controller, controller, controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker] ++
          leftBlock ++ [leftMarker, leftMarker] ++ after)
        (before ++ controllerBlock ++ [controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker] ++
          leftBlock ++ [leftMarker, leftMarker] ++ after) := by
    simpa [Word.toList, Word.singleton, Word.append,
      List.append_assoc] using contractController
  exact expandStep.trans (swapStep'.trans contractStep)

/-- Scan a word into blocks of globally simple letters, each terminated by
one globally non-simple letter, together with the trailing simple block.
The current block is stored in reverse order during the scan. -/
def terminatedBlockScan
    (whole current : List Nat) :
    List Nat → List (List Nat × Nat) × List Nat
  | [] => ([], current.reverse)
  | letter :: rest =>
      if whole.count letter = 1 then
        terminatedBlockScan whole (letter :: current) rest
      else
        let scanned := terminatedBlockScan whole [] rest
        ((current.reverse, letter) :: scanned.1, scanned.2)

/-- Render blocks that carry their terminating non-simple letter. -/
def renderTerminatedBlocks :
    List (List Nat × Nat) → List Nat
  | [] => []
  | (block, marker) :: rest =>
      block ++ marker :: renderTerminatedBlocks rest

/-- Render every terminating marker as an adjacent square. -/
def renderSquaredTerminatedBlocks :
    List (List Nat × Nat) → List Nat
  | [] => []
  | (block, marker) :: rest =>
      block ++ marker :: marker ::
        renderSquaredTerminatedBlocks rest

@[simp]
theorem renderSquaredTerminatedBlocks_append
    (left right : List (List Nat × Nat)) :
    renderSquaredTerminatedBlocks (left ++ right) =
      renderSquaredTerminatedBlocks left ++
        renderSquaredTerminatedBlocks right := by
  induction left with
  | nil =>
      rfl
  | cons factor rest ih =>
      rcases factor with ⟨block, marker⟩
      simp [renderSquaredTerminatedBlocks, ih,
        List.append_assoc]

/-- The simple blocks carried by a list of terminated factors. -/
def terminatedFactorBlocks
    (factors : List (List Nat × Nat)) : List (List Nat) :=
  factors.map fun factor => factor.1

/-- The terminating markers carried by a list of terminated factors. -/
def terminatedFactorMarkers
    (factors : List (List Nat × Nat)) : List Nat :=
  factors.map fun factor => factor.2

/-- Factor permutations induce block permutations. -/
theorem terminatedFactorBlocks_perm
    {left right : List (List Nat × Nat)}
    (permutation : left.Perm right) :
    (terminatedFactorBlocks left).Perm
      (terminatedFactorBlocks right) := by
  simpa [terminatedFactorBlocks] using
    permutation.map (fun factor => factor.1)

/-- Factor permutations induce marker permutations. -/
theorem terminatedFactorMarkers_perm
    {left right : List (List Nat × Nat)}
    (permutation : left.Perm right) :
    (terminatedFactorMarkers left).Perm
      (terminatedFactorMarkers right) := by
  simpa [terminatedFactorMarkers] using
    permutation.map (fun factor => factor.2)

/-- Factors carrying a nonempty simple block, in their original order. -/
def blockBearingFactors
    (factors : List (List Nat × Nat)) :
    List (List Nat × Nat) :=
  factors.filter fun factor => decide (factor.1 ≠ [])

/-- Factors carrying no simple block, in their original order. -/
def markerOnlyFactors
    (factors : List (List Nat × Nat)) :
    List (List Nat × Nat) :=
  factors.filter fun factor => decide (factor.1 = [])

/-- Stable partitioning by block emptiness only permutes the factor list. -/
theorem blockBearingFactors_append_markerOnlyFactors_perm
    (factors : List (List Nat × Nat)) :
    (blockBearingFactors factors ++ markerOnlyFactors factors).Perm
      factors := by
  simpa [blockBearingFactors, markerOnlyFactors] using
    (List.filter_append_perm
      (fun factor : List Nat × Nat =>
        decide (factor.1 ≠ []))
      factors)

/-- Every block-bearing factor has a genuinely nonempty block. -/
theorem blockBearingFactors_blocks_nonempty
    (factors : List (List Nat × Nat)) :
    ∀ factor ∈ blockBearingFactors factors,
      factor.1 ≠ [] := by
  intro factor member
  have tested := (List.mem_filter.mp member).2
  exact of_decide_eq_true tested

/-- Every marker-only factor has an empty block. -/
theorem markerOnlyFactors_blocks_empty
    (factors : List (List Nat × Nat)) :
    ∀ factor ∈ markerOnlyFactors factors,
      factor.1 = [] := by
  intro factor member
  have tested := (List.mem_filter.mp member).2
  exact of_decide_eq_true tested

/-- Turn a leading marker square followed by four copies of the chosen
anchor into one leading anchor, an anchor square, and the displaced marker
square. -/
theorem listDerivesLeadingSquareAnchorFourth
    (leading anchor : Nat) :
    ListDerives basis
      ([leading, leading] ++
        [anchor, anchor, anchor, anchor])
      ([anchor, anchor, anchor] ++
        [leading, leading]) := by
  have contractAnchor :=
    (ListDerives.ofWord <|
      derivesFourToTwo (Word.singleton anchor)).prepend
        [leading, leading]
  have contractStep :
      ListDerives basis
        ([leading, leading] ++
          [anchor, anchor, anchor, anchor])
        ([leading, leading] ++ [anchor, anchor]) := by
    simpa [Word.toList, Word.singleton, Word.append,
      List.append_assoc] using contractAnchor
  have commuteStep :
      ListDerives basis
        ([leading, leading] ++ [anchor, anchor])
        ([anchor, anchor] ++ [leading, leading]) := by
    simpa [Word.toList, Word.singleton, Word.append,
      List.append_assoc] using
        (ListDerives.ofWord <|
          derivesSquareBlockCommutation
            (Word.singleton leading)
            (Word.singleton anchor))
  have expandAnchor :=
    (ListDerives.ofWord <|
      derivesTwoToThree (Word.singleton anchor)).append
        [leading, leading]
  have expandStep :
      ListDerives basis
        ([anchor, anchor] ++ [leading, leading])
        ([anchor, anchor, anchor] ++ [leading, leading]) := by
    simpa [Word.toList, Word.singleton, Word.append,
      List.append_assoc] using expandAnchor
  exact contractStep.trans (commuteStep.trans expandStep)

/-- Expand one adjacent singleton square to four copies. -/
theorem listDerivesExpandSquareToFourth
    (letter : Nat) :
    ListDerives basis
      [letter, letter]
      [letter, letter, letter, letter] := by
  simpa [Word.toList, Word.singleton, Word.append,
    List.append_assoc] using
      (ListDerives.ofWord <|
        derivesFourToTwo
          (Word.singleton letter)).symm

/-- Normalize a nonempty chain of square-ended factors from right to left.
The marker of the final factor becomes the common anchor of every block, and
the leading marker plus all earlier factor markers become a square tail. -/
theorem listDerivesAnchorNonemptyFactorChain
    (leadingBlock : List Nat) (leadingMarker anchor : Nat)
    (front : List (List Nat × Nat))
    (lastHead : Nat) (lastTail suffix : List Nat)
    (frontBlocksNonempty :
      ∀ factor ∈ front, factor.1 ≠ []) :
    ListDerives basis
      (leadingBlock ++ [leadingMarker, leadingMarker] ++
        renderSquaredTerminatedBlocks
          (front ++ [((lastHead :: lastTail), anchor)]) ++
        suffix)
      (leadingBlock ++ [anchor] ++
        renderAnchoredBlocks anchor
          (terminatedFactorBlocks front ++
            [lastHead :: lastTail]) ++
        renderMultipleSquares
          (leadingMarker :: terminatedFactorMarkers front) ++
        suffix) := by
  induction front generalizing leadingBlock leadingMarker with
  | nil =>
      have installed :=
        (listDerivesInstallFactorMarkerAsAnchor
          leadingMarker anchor lastHead lastTail).context
            leadingBlock suffix
      simpa [terminatedFactorBlocks, terminatedFactorMarkers,
        renderSquaredTerminatedBlocks, renderAnchoredBlocks,
        renderMultipleSquares, List.append_assoc] using installed
  | cons factor rest ih =>
      rcases factor with ⟨block, marker⟩
      have blockNonempty : block ≠ [] :=
        frontBlocksNonempty (block, marker) (by simp)
      obtain ⟨blockHead, blockTail, rfl⟩ :=
        List.exists_cons_of_ne_nil blockNonempty
      have restBlocksNonempty :
          ∀ candidate ∈ rest, candidate.1 ≠ [] := by
        intro candidate member
        exact
          frontBlocksNonempty candidate
            (List.mem_cons_of_mem (blockHead :: blockTail, marker)
              member)
      have tailStep :=
        ih (blockHead :: blockTail) marker restBlocksNonempty
      have tailStep' :=
        tailStep.prepend
          (leadingBlock ++ [leadingMarker, leadingMarker])
      let middleTail : List Nat :=
        blockTail ++ [anchor] ++
          renderAnchoredBlocks anchor
            (terminatedFactorBlocks rest) ++
          (lastHead :: lastTail)
      let squareSuffix : List Nat :=
        renderMultipleSquares
            (marker :: terminatedFactorMarkers rest) ++
          suffix
      have tailNormalized :
          ListDerives basis
            (leadingBlock ++ [leadingMarker, leadingMarker] ++
              (blockHead :: blockTail) ++ [marker, marker] ++
              renderSquaredTerminatedBlocks
                (rest ++
                  [((lastHead :: lastTail), anchor)]) ++
              suffix)
            (leadingBlock ++ [leadingMarker, leadingMarker] ++
              (blockHead :: middleTail) ++
              [anchor] ++ squareSuffix) := by
        simpa [middleTail, squareSuffix,
          terminatedFactorBlocks, terminatedFactorMarkers,
          renderAnchoredBlocks, renderMultipleSquares,
          List.append_assoc] using tailStep'
      have anchorInMiddle :
          anchor ∈ blockHead :: middleTail := by
        simp [middleTail]
      have prependStep :=
        (listDerivesPrependToAnchoredMiddle
          leadingMarker anchor blockHead middleTail
          squareSuffix anchorInMiddle).prepend leadingBlock
      have prepended :
          ListDerives basis
            (leadingBlock ++ [leadingMarker, leadingMarker] ++
              (blockHead :: middleTail) ++
              [anchor] ++ squareSuffix)
            (leadingBlock ++ [anchor] ++
              (blockHead :: middleTail) ++
              [anchor, leadingMarker, leadingMarker] ++
              squareSuffix) := by
        simpa [List.append_assoc] using prependStep
      have combined := tailNormalized.trans prepended
      simpa [middleTail, squareSuffix,
        terminatedFactorBlocks, terminatedFactorMarkers,
        renderSquaredTerminatedBlocks, renderAnchoredBlocks,
        renderMultipleSquares, List.append_assoc] using combined

/-- Select a nonempty anchor factor while retaining one anchor square in the
final square tail. -/
theorem listDerivesAnchorNonemptyFactorChainRetainingSquare
    (leadingBlock : List Nat) (leadingMarker anchor : Nat)
    (front : List (List Nat × Nat))
    (lastHead : Nat) (lastTail suffix : List Nat)
    (frontBlocksNonempty :
      ∀ factor ∈ front, factor.1 ≠ []) :
    ListDerives basis
      (leadingBlock ++ [leadingMarker, leadingMarker] ++
        renderSquaredTerminatedBlocks
          (front ++ [((lastHead :: lastTail), anchor)]) ++
        suffix)
      (leadingBlock ++ [anchor] ++
        renderAnchoredBlocks anchor
          (terminatedFactorBlocks front ++
            [lastHead :: lastTail]) ++
        renderMultipleSquares
          (leadingMarker ::
            terminatedFactorMarkers front ++ [anchor]) ++
        suffix) := by
  let beforeAnchor : List Nat :=
    leadingBlock ++ [leadingMarker, leadingMarker] ++
      renderSquaredTerminatedBlocks front ++
      (lastHead :: lastTail)
  have expanded :=
    (listDerivesExpandSquareToFourth anchor).context
      beforeAnchor suffix
  have expandedStep :
      ListDerives basis
        (leadingBlock ++ [leadingMarker, leadingMarker] ++
          renderSquaredTerminatedBlocks
            (front ++ [((lastHead :: lastTail), anchor)]) ++
          suffix)
        (leadingBlock ++ [leadingMarker, leadingMarker] ++
          renderSquaredTerminatedBlocks front ++
          (lastHead :: lastTail) ++
          [anchor, anchor, anchor, anchor] ++ suffix) := by
    simpa [beforeAnchor, renderSquaredTerminatedBlocks,
      List.append_assoc] using expanded
  have extracted :=
    listDerivesAnchorNonemptyFactorChain
      leadingBlock leadingMarker anchor front
      lastHead lastTail
      ([anchor, anchor] ++ suffix)
      frontBlocksNonempty
  have extractedStep :
      ListDerives basis
        (leadingBlock ++ [leadingMarker, leadingMarker] ++
          renderSquaredTerminatedBlocks front ++
          (lastHead :: lastTail) ++
          [anchor, anchor, anchor, anchor] ++ suffix)
        (leadingBlock ++ [anchor] ++
          renderAnchoredBlocks anchor
            (terminatedFactorBlocks front ++
              [lastHead :: lastTail]) ++
          renderMultipleSquares
            (leadingMarker ::
              terminatedFactorMarkers front ++ [anchor]) ++
          suffix) := by
    simpa [renderSquaredTerminatedBlocks,
      renderMultipleSquares, List.append_assoc] using extracted
  exact expandedStep.trans extractedStep

/-- Normalize a chain of square-ended nonempty factors when the selected
anchor is supplied by a following empty factor. Expanding that selected
anchor square to four copies provides one leading anchor and a retained
anchor square for the final square tail. -/
theorem listDerivesAnchorFactorChainFromEmptySeed
    (leadingBlock : List Nat) (leadingMarker anchor : Nat)
    (factors : List (List Nat × Nat))
    (suffix : List Nat)
    (blocksNonempty :
      ∀ factor ∈ factors, factor.1 ≠ []) :
    ListDerives basis
      (leadingBlock ++ [leadingMarker, leadingMarker] ++
        renderSquaredTerminatedBlocks factors ++
        [anchor, anchor, anchor, anchor] ++ suffix)
      (leadingBlock ++ [anchor] ++
        renderAnchoredBlocks anchor
          (terminatedFactorBlocks factors) ++
        renderMultipleSquares
          (anchor :: leadingMarker ::
            terminatedFactorMarkers factors) ++
        suffix) := by
  induction factors generalizing leadingBlock leadingMarker with
  | nil =>
      have seeded :=
        (listDerivesLeadingSquareAnchorFourth
          leadingMarker anchor).context leadingBlock suffix
      simpa [terminatedFactorBlocks, terminatedFactorMarkers,
        renderSquaredTerminatedBlocks, renderAnchoredBlocks,
        renderMultipleSquares, List.append_assoc] using seeded
  | cons factor rest ih =>
      rcases factor with ⟨block, marker⟩
      have blockNonempty : block ≠ [] :=
        blocksNonempty (block, marker) (by simp)
      obtain ⟨blockHead, blockTail, rfl⟩ :=
        List.exists_cons_of_ne_nil blockNonempty
      have restBlocksNonempty :
          ∀ candidate ∈ rest, candidate.1 ≠ [] := by
        intro candidate member
        exact
          blocksNonempty candidate
            (List.mem_cons_of_mem
              (blockHead :: blockTail, marker) member)
      have tailStep :=
        ih (blockHead :: blockTail) marker
          restBlocksNonempty
      have tailStep' :=
        tailStep.prepend
          (leadingBlock ++ [leadingMarker, leadingMarker])
      let anchoredCore : List Nat :=
        (blockHead :: blockTail) ++ [anchor] ++
          renderAnchoredBlocks anchor
            (terminatedFactorBlocks rest)
      let remainingSquares : List Nat :=
        renderMultipleSquares
            (marker :: terminatedFactorMarkers rest) ++
          suffix
      have tailNormalized :
          ListDerives basis
            (leadingBlock ++ [leadingMarker, leadingMarker] ++
              (blockHead :: blockTail) ++ [marker, marker] ++
              renderSquaredTerminatedBlocks rest ++
              [anchor, anchor, anchor, anchor] ++ suffix)
            (leadingBlock ++ [leadingMarker, leadingMarker] ++
              anchoredCore ++ [anchor, anchor] ++
              remainingSquares) := by
        simpa [anchoredCore, remainingSquares,
          terminatedFactorBlocks, terminatedFactorMarkers,
          renderAnchoredBlocks, renderMultipleSquares,
          List.append_assoc] using tailStep'
      have middleNonempty :
          anchoredCore ++ [anchor] ≠ [] := by
        simp
      obtain ⟨middleHead, middleTail, middleShape⟩ :=
        List.exists_cons_of_ne_nil middleNonempty
      have anchorInMiddle :
          anchor ∈ middleHead :: middleTail := by
        rw [← middleShape]
        simp
      have prependStep :=
        (listDerivesPrependToAnchoredMiddle
          leadingMarker anchor middleHead middleTail
          remainingSquares anchorInMiddle).prepend leadingBlock
      have prepended :
          ListDerives basis
            (leadingBlock ++ [leadingMarker, leadingMarker] ++
              anchoredCore ++ [anchor, anchor] ++
              remainingSquares)
            (leadingBlock ++ [anchor] ++
              anchoredCore ++ [anchor, anchor,
                leadingMarker, leadingMarker] ++
              remainingSquares) := by
        simpa only [← middleShape,
          List.append_assoc] using prependStep
      have combined := tailNormalized.trans prepended
      simpa [anchoredCore, remainingSquares,
        terminatedFactorBlocks, terminatedFactorMarkers,
        renderSquaredTerminatedBlocks, renderAnchoredBlocks,
        renderMultipleSquares, List.append_assoc] using combined

/-- Select an empty anchor factor, expanding its square just enough to seed
the anchored block chain while retaining one anchor square in the tail. -/
theorem listDerivesAnchorFactorChainFromEmptyFactor
    (leadingBlock : List Nat) (leadingMarker anchor : Nat)
    (factors : List (List Nat × Nat))
    (suffix : List Nat)
    (blocksNonempty :
      ∀ factor ∈ factors, factor.1 ≠ []) :
    ListDerives basis
      (leadingBlock ++ [leadingMarker, leadingMarker] ++
        renderSquaredTerminatedBlocks factors ++
        [anchor, anchor] ++ suffix)
      (leadingBlock ++ [anchor] ++
        renderAnchoredBlocks anchor
          (terminatedFactorBlocks factors) ++
        renderMultipleSquares
          (anchor :: leadingMarker ::
            terminatedFactorMarkers factors) ++
        suffix) := by
  let beforeAnchor : List Nat :=
    leadingBlock ++ [leadingMarker, leadingMarker] ++
      renderSquaredTerminatedBlocks factors
  have expanded :=
    (listDerivesExpandSquareToFourth anchor).context
      beforeAnchor suffix
  have expandedStep :
      ListDerives basis
        (leadingBlock ++ [leadingMarker, leadingMarker] ++
          renderSquaredTerminatedBlocks factors ++
          [anchor, anchor] ++ suffix)
        (leadingBlock ++ [leadingMarker, leadingMarker] ++
          renderSquaredTerminatedBlocks factors ++
          [anchor, anchor, anchor, anchor] ++ suffix) := by
    simpa [beforeAnchor, List.append_assoc] using expanded
  exact expandedStep.trans <|
    listDerivesAnchorFactorChainFromEmptySeed
      leadingBlock leadingMarker anchor factors suffix
        blocksNonempty

/-- Every permutation of the square-ended factors after a fixed first factor
is derivable. -/
theorem listDerivesSquaredTailPermutation
    {source target : List (List Nat × Nat)}
    (permutation : source.Perm target) :
    ∀ (first : List Nat × Nat) (final : List Nat),
      ListDerives basis
        (renderSquaredTerminatedBlocks
            (first :: source) ++ final)
        (renderSquaredTerminatedBlocks
            (first :: target) ++ final) := by
  induction permutation with
  | nil =>
      intro first final
      exact ListDerives.refl _
  | @cons factor source target permutation ih =>
      intro first final
      rcases first with ⟨firstBlock, firstMarker⟩
      have tailStep := ih factor final
      simpa [renderSquaredTerminatedBlocks,
        List.append_assoc] using
          tailStep.prepend
            (firstBlock ++ [firstMarker, firstMarker])
  | swap left right rest =>
      intro first final
      rcases first with ⟨controllerBlock, controller⟩
      rcases left with ⟨leftBlock, leftMarker⟩
      rcases right with ⟨rightBlock, rightMarker⟩
      have swapped :=
        listDerivesSquaredFactorSwapAfterController
          [] controllerBlock leftBlock rightBlock
          (renderSquaredTerminatedBlocks rest ++ final)
          controller leftMarker rightMarker
      simpa [renderSquaredTerminatedBlocks,
        List.append_assoc] using swapped.symm
  | @trans source middle target first second ihFirst ihSecond =>
      intro leading final
      exact
        (ihFirst leading final).trans
          (ihSecond leading final)

/-- The complete terminated-factor list of a word. -/
def terminatedBlocks (letters : List Nat) :
    List (List Nat × Nat) :=
  (terminatedBlockScan letters [] letters).1

/-- The trailing globally simple block after the final non-simple letter. -/
def terminatedFinalBlock (letters : List Nat) : List Nat :=
  (terminatedBlockScan letters [] letters).2

/-- The marker projection of the scanner is exactly the rejected part of
the unprocessed suffix. Occurrences, not only distinct labels, are retained. -/
theorem terminatedBlockScan_markers
    (whole current remaining : List Nat) :
    terminatedFactorMarkers
        (terminatedBlockScan whole current remaining).1 =
      remaining.filter
        (fun letter => decide (whole.count letter ≠ 1)) := by
  induction remaining generalizing current with
  | nil =>
      simp [terminatedBlockScan, terminatedFactorMarkers]
  | cons letter rest ih =>
      by_cases simple : whole.count letter = 1
      · simpa [terminatedBlockScan, terminatedFactorMarkers,
          simple] using ih (letter :: current)
      · have tail := ih ([] : List Nat)
        simp only [terminatedBlockScan, if_neg simple,
          terminatedFactorMarkers, List.map_cons, Prod.snd]
        rw [List.filter_cons_of_pos]
        · exact congrArg (List.cons letter) tail
        · simp [simple]

/-- Public marker projection for the complete terminated decomposition. -/
theorem terminatedFactorMarkers_terminatedBlocks
    (letters : List Nat) :
    terminatedFactorMarkers (terminatedBlocks letters) =
      letters.filter
        (fun letter => decide (letters.count letter ≠ 1)) := by
  simpa [terminatedBlocks] using
    terminatedBlockScan_markers letters [] letters

/-- A label occurs among the terminated markers exactly when it is multiple
in the original word. -/
theorem mem_terminatedFactorMarkers_iff
    (letter : Nat) (letters : List Nat) :
    letter ∈ terminatedFactorMarkers (terminatedBlocks letters) ↔
      2 ≤ letters.count letter := by
  rw [terminatedFactorMarkers_terminatedBlocks]
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨member, notSimple⟩
    have positive : 0 < letters.count letter :=
      List.count_pos_iff.mpr member
    omega
  · intro multiple
    exact
      ⟨List.count_pos_iff.mp (by omega),
        by omega⟩

/-- Filtering the complete marker projection preserves the exact number of
occurrences of every multiple label. -/
theorem count_terminatedFactorMarkers_of_multiple
    (letter : Nat) (letters : List Nat)
    (multiple : 2 ≤ letters.count letter) :
    (terminatedFactorMarkers
        (terminatedBlocks letters)).count letter =
      letters.count letter := by
  rw [terminatedFactorMarkers_terminatedBlocks]
  have notSimple : letters.count letter ≠ 1 := by
    omega
  simp [notSimple]

/-- Once the fixed first factor is removed, every multiple marker still has
at least one factor occurrence in the tail. -/
theorem exists_tail_factor_with_marker_of_multiple
    (letters : List Nat)
    (first : List Nat × Nat)
    (tail : List (List Nat × Nat))
    (marker : Nat)
    (shape :
      terminatedBlocks letters = first :: tail)
    (multiple : 2 ≤ letters.count marker) :
    ∃ factor ∈ tail, factor.2 = marker := by
  have countEq :=
    count_terminatedFactorMarkers_of_multiple
      marker letters multiple
  rw [shape] at countEq
  have tailPositive :
      0 <
        (terminatedFactorMarkers tail).count marker := by
    by_cases firstIsMarker : first.2 = marker
    · have countShape :
          (terminatedFactorMarkers tail).count marker + 1 =
            letters.count marker := by
        simpa [terminatedFactorMarkers, firstIsMarker,
          Nat.add_comm] using countEq
      omega
    · have countShape :
          (terminatedFactorMarkers tail).count marker =
            letters.count marker := by
        simpa [terminatedFactorMarkers, firstIsMarker] using countEq
      omega
  have markerMember :
      marker ∈ terminatedFactorMarkers tail :=
    List.count_pos_iff.mp tailPositive
  rcases List.mem_map.mp markerMember with
    ⟨factor, factorMember, factorMarker⟩
  exact ⟨factor, factorMember, factorMarker⟩

/-- Move a distinguished head past an arbitrary front segment. -/
theorem perm_cons_append
    {α : Type} (item : α) :
    ∀ front back : List α,
      (item :: front ++ back).Perm
        (front ++ item :: back)
  | [], back => List.Perm.refl _
  | head :: tail, back => by
      have swapped :
          (item :: head :: tail ++ back).Perm
            (head :: item :: tail ++ back) :=
        (List.Perm.swap item head (tail ++ back)).symm
      have moved :
          (head :: item :: tail ++ back).Perm
            (head :: tail ++ item :: back) :=
        List.Perm.cons head
          (perm_cons_append item tail back)
      exact swapped.trans moved

/-- Expose a selected factor, stably partition the remainder by block
emptiness, and place the selected factor between the two partitions. -/
theorem perm_selected_factor_after_blockBearing
    {factors : List (List Nat × Nat)}
    {selected : List Nat × Nat}
    (member : selected ∈ factors) :
    factors.Perm
      (blockBearingFactors (factors.erase selected) ++
        selected ::
          markerOnlyFactors (factors.erase selected)) := by
  have expose :
      factors.Perm (selected :: factors.erase selected) :=
    List.perm_cons_erase member
  have partition :
      (factors.erase selected).Perm
        (blockBearingFactors (factors.erase selected) ++
          markerOnlyFactors (factors.erase selected)) :=
    (blockBearingFactors_append_markerOnlyFactors_perm
      (factors.erase selected)).symm
  have partitionWithSelected :
      (selected :: factors.erase selected).Perm
        (selected ::
          (blockBearingFactors (factors.erase selected) ++
            markerOnlyFactors (factors.erase selected))) :=
    List.Perm.cons selected partition
  have moveSelected :=
    perm_cons_append selected
      (blockBearingFactors (factors.erase selected))
      (markerOnlyFactors (factors.erase selected))
  exact expose.trans
    (partitionWithSelected.trans moveSelected)

/-- Forget terminating markers and discard empty simple blocks. -/
def nonemptyTerminatedBlocks :
    List (List Nat × Nat) → List (List Nat)
  | [] => []
  | (block, _) :: rest =>
      if block = [] then
        nonemptyTerminatedBlocks rest
      else
        block :: nonemptyTerminatedBlocks rest

@[simp]
theorem nonemptyTerminatedBlocks_append
    (left right : List (List Nat × Nat)) :
    nonemptyTerminatedBlocks (left ++ right) =
      nonemptyTerminatedBlocks left ++
        nonemptyTerminatedBlocks right := by
  induction left with
  | nil =>
      rfl
  | cons factor rest ih =>
      rcases factor with ⟨block, marker⟩
      by_cases empty : block = []
      · simp [nonemptyTerminatedBlocks, empty, ih]
      · simp [nonemptyTerminatedBlocks, empty, ih]

/-- Every retained block is nonempty by construction. -/
theorem nonemptyTerminatedBlocks_blocks_nonempty
    (factors : List (List Nat × Nat)) :
    ∀ block ∈ nonemptyTerminatedBlocks factors,
      block ≠ [] := by
  induction factors with
  | nil =>
      simp [nonemptyTerminatedBlocks]
  | cons factor rest ih =>
      rcases factor with ⟨block, marker⟩
      by_cases empty : block = []
      · simpa [nonemptyTerminatedBlocks, empty] using ih
      · intro candidate member
        simp only [nonemptyTerminatedBlocks, if_neg empty,
          List.mem_cons] at member
        rcases member with rfl | member
        · exact empty
        · exact ih candidate member

/-- Filtering for block-bearing factors and then forgetting markers is the
same as directly discarding empty blocks. -/
theorem terminatedFactorBlocks_blockBearingFactors
    (factors : List (List Nat × Nat)) :
    terminatedFactorBlocks (blockBearingFactors factors) =
      nonemptyTerminatedBlocks factors := by
  induction factors with
  | nil =>
      simp [terminatedFactorBlocks, blockBearingFactors,
        nonemptyTerminatedBlocks]
  | cons factor rest ih =>
      rcases factor with ⟨block, marker⟩
      change
        terminatedFactorBlocks
            (List.filter
              (fun candidate : List Nat × Nat =>
                decide (candidate.1 ≠ []))
              ((block, marker) :: rest)) =
          (if block = [] then
            nonemptyTerminatedBlocks rest
           else
            block :: nonemptyTerminatedBlocks rest)
      change
        terminatedFactorBlocks
            (List.filter
              (fun candidate : List Nat × Nat =>
                decide (candidate.1 ≠ []))
              rest) =
          nonemptyTerminatedBlocks rest at ih
      by_cases empty : block = []
      · simpa [empty, terminatedFactorBlocks] using ih
      · simpa [empty, terminatedFactorBlocks] using ih

/-- Discarding empty blocks commutes with factor permutations. -/
theorem nonemptyTerminatedBlocks_perm
    {left right : List (List Nat × Nat)}
    (permutation : left.Perm right) :
    (nonemptyTerminatedBlocks left).Perm
      (nonemptyTerminatedBlocks right) := by
  rw [← terminatedFactorBlocks_blockBearingFactors,
    ← terminatedFactorBlocks_blockBearingFactors]
  exact
    (permutation.filter
      (fun factor : List Nat × Nat =>
        decide (factor.1 ≠ []))).map
      (fun factor => factor.1)

/-- If every factor carries a nonempty block, discarding empty blocks changes
nothing except forgetting the markers. -/
theorem nonemptyTerminatedBlocks_eq_terminatedFactorBlocks_of_blocks_nonempty
    (factors : List (List Nat × Nat))
    (blocksNonempty :
      ∀ factor ∈ factors, factor.1 ≠ []) :
    nonemptyTerminatedBlocks factors =
      terminatedFactorBlocks factors := by
  induction factors with
  | nil =>
      rfl
  | cons factor rest ih =>
      rcases factor with ⟨block, marker⟩
      have blockNonempty : block ≠ [] :=
        blocksNonempty (block, marker) (by simp)
      have restNonempty :
          ∀ candidate ∈ rest, candidate.1 ≠ [] := by
        intro candidate member
        exact blocksNonempty candidate (by simp [member])
      simp [nonemptyTerminatedBlocks,
        terminatedFactorBlocks, blockNonempty,
        ih restNonempty]

/-- Marker-only factors contribute no nonempty block. -/
theorem nonemptyTerminatedBlocks_eq_nil_of_blocks_empty
    (factors : List (List Nat × Nat))
    (blocksEmpty :
      ∀ factor ∈ factors, factor.1 = []) :
    nonemptyTerminatedBlocks factors = [] := by
  induction factors with
  | nil =>
      rfl
  | cons factor rest ih =>
      rcases factor with ⟨block, marker⟩
      have blockEmpty : block = [] :=
        blocksEmpty (block, marker) (by simp)
      have restEmpty :
          ∀ candidate ∈ rest, candidate.1 = [] := by
        intro candidate member
        exact blocksEmpty candidate (by simp [member])
      simp [nonemptyTerminatedBlocks, blockEmpty,
        ih restEmpty]

/-- A list of marker-only factors renders as an ordinary square tail. -/
theorem renderSquaredTerminatedBlocks_eq_renderMultipleSquares_of_blocks_empty
    (factors : List (List Nat × Nat))
    (blocksEmpty :
      ∀ factor ∈ factors, factor.1 = []) :
    renderSquaredTerminatedBlocks factors =
      renderMultipleSquares
        (terminatedFactorMarkers factors) := by
  induction factors with
  | nil =>
      simp [renderSquaredTerminatedBlocks,
        renderMultipleSquares, terminatedFactorMarkers]
  | cons factor rest ih =>
      rcases factor with ⟨block, marker⟩
      have blockEmpty : block = [] :=
        blocksEmpty (block, marker) (by simp)
      have restEmpty :
          ∀ candidate ∈ rest, candidate.1 = [] := by
        intro candidate member
        exact blocksEmpty candidate (by simp [member])
      have tail := ih restEmpty
      simp [renderSquaredTerminatedBlocks,
        renderMultipleSquares, terminatedFactorMarkers,
        blockEmpty, tail, List.append_assoc]

/-- Recover the ordinary simple-block list from terminated factors and the
trailing simple block. -/
def simpleBlocksFromTerminated
    (factors : List (List Nat × Nat))
    (final : List Nat) : List (List Nat) :=
  nonemptyTerminatedBlocks factors ++
    if final = [] then [] else [final]

/-- The terminated scan is a literal factorization of the scanned suffix. -/
theorem terminatedBlockScan_render
    (whole current remaining : List Nat) :
    renderTerminatedBlocks
        (terminatedBlockScan whole current remaining).1 ++
      (terminatedBlockScan whole current remaining).2 =
        current.reverse ++ remaining := by
  induction remaining generalizing current with
  | nil =>
      simp [terminatedBlockScan, renderTerminatedBlocks]
  | cons letter rest ih =>
      by_cases simple : whole.count letter = 1
      · simpa [terminatedBlockScan, simple, List.reverse_cons,
          List.append_assoc] using ih (letter :: current)
      · have tail := ih ([] : List Nat)
        simpa [terminatedBlockScan, simple, renderTerminatedBlocks,
          List.append_assoc] using tail

/-- Every word is exactly its rendered terminated factors followed by the
trailing simple block. -/
theorem terminatedBlocks_render (letters : List Nat) :
    renderTerminatedBlocks (terminatedBlocks letters) ++
      terminatedFinalBlock letters = letters := by
  simpa [terminatedBlocks, terminatedFinalBlock] using
    terminatedBlockScan_render letters [] letters

/-- Every emitted marker is globally non-simple in the frozen whole word. -/
theorem terminatedBlockScan_marker_not_simple
    (whole current remaining : List Nat) :
    ∀ factor ∈ (terminatedBlockScan whole current remaining).1,
      whole.count factor.2 ≠ 1 := by
  induction remaining generalizing current with
  | nil =>
      simp [terminatedBlockScan]
  | cons letter rest ih =>
      by_cases simple : whole.count letter = 1
      · simpa [terminatedBlockScan, simple] using
          ih (letter :: current)
      · intro factor member
        simp only [terminatedBlockScan, if_neg simple,
          List.mem_cons] at member
        rcases member with rfl | member
        · exact simple
        · exact ih ([] : List Nat) factor member

/-- Assuming the current accumulator contains only globally simple letters,
all blocks and the final suffix emitted by the scan do too. -/
theorem terminatedBlockScan_blocks_simple
    (whole current remaining : List Nat)
    (currentSimple :
      ∀ letter ∈ current, whole.count letter = 1) :
    (∀ factor ∈ (terminatedBlockScan whole current remaining).1,
        ∀ letter ∈ factor.1, whole.count letter = 1) ∧
      (∀ letter ∈ (terminatedBlockScan whole current remaining).2,
        whole.count letter = 1) := by
  induction remaining generalizing current with
  | nil =>
      constructor
      · simp [terminatedBlockScan]
      · intro letter member
        change letter ∈ current.reverse at member
        exact currentSimple letter <| by
          simpa using member
  | cons next rest ih =>
      by_cases simple : whole.count next = 1
      · have extendedSimple :
            ∀ letter ∈ next :: current,
              whole.count letter = 1 := by
          intro letter member
          simp only [List.mem_cons] at member
          rcases member with equal | member
          · simpa [equal] using simple
          · exact currentSimple letter member
        simpa [terminatedBlockScan, simple] using
          ih (next :: current) extendedSimple
      · have tail :=
          ih ([] : List Nat) (by simp)
        constructor
        · intro factor member letter letterMember
          simp only [terminatedBlockScan, if_neg simple,
            List.mem_cons] at member
          rcases member with rfl | member
          · exact currentSimple letter <| by
              simpa using letterMember
          · exact tail.1 factor member letter letterMember
        · simpa [terminatedBlockScan, simple] using tail.2

/-- A terminating marker occurs in the rendering of every factor list that
contains its factor. -/
theorem marker_mem_renderTerminatedBlocks
    {factors : List (List Nat × Nat)}
    {factor : List Nat × Nat}
    (member : factor ∈ factors) :
    factor.2 ∈ renderTerminatedBlocks factors := by
  induction factors with
  | nil =>
      simp at member
  | cons first rest ih =>
      rcases first with ⟨block, marker⟩
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp [renderTerminatedBlocks]
      · simp only [renderTerminatedBlocks, List.mem_append,
          List.mem_cons]
        exact Or.inr (Or.inr (ih member))

/-- Every public terminated marker is globally non-simple. -/
theorem terminatedBlocks_marker_not_simple
    (letters : List Nat)
    (factor : List Nat × Nat)
    (member : factor ∈ terminatedBlocks letters) :
    letters.count factor.2 ≠ 1 :=
  terminatedBlockScan_marker_not_simple
    letters [] letters factor member

/-- Every public terminated marker occurs at least twice. -/
theorem terminatedBlocks_marker_multiple
    (letters : List Nat)
    (factor : List Nat × Nat)
    (member : factor ∈ terminatedBlocks letters) :
    2 ≤ letters.count factor.2 := by
  have markerInRendering :
      factor.2 ∈ renderTerminatedBlocks (terminatedBlocks letters) :=
    marker_mem_renderTerminatedBlocks member
  have markerInLetters : factor.2 ∈ letters := by
    rw [← terminatedBlocks_render letters]
    exact List.mem_append_left _ markerInRendering
  have positive : 0 < letters.count factor.2 :=
    List.count_pos_iff.mpr markerInLetters
  have notSimple :=
    terminatedBlocks_marker_not_simple letters factor member
  omega

/-- Every letter in a public terminated block is globally simple. -/
theorem terminatedBlocks_block_simple
    (letters : List Nat)
    (factor : List Nat × Nat)
    (factorMember : factor ∈ terminatedBlocks letters)
    (letter : Nat)
    (letterMember : letter ∈ factor.1) :
    letters.count letter = 1 := by
  exact
    (terminatedBlockScan_blocks_simple
      letters [] letters (by simp)).1
        factor factorMember letter letterMember

/-- Every letter in the trailing public block is globally simple. -/
theorem terminatedFinalBlock_letter_simple
    (letters : List Nat)
    (letter : Nat)
    (member : letter ∈ terminatedFinalBlock letters) :
    letters.count letter = 1 := by
  exact
    (terminatedBlockScan_blocks_simple
      letters [] letters (by simp)).2 letter member

/-- Duplicating one selected occurrence never decreases the count of any
tested letter. -/
theorem count_le_count_duplicateSelected
    (tested inserted : Nat)
    (before after : List Nat) :
    (before ++ [inserted] ++ after).count tested ≤
      (before ++ [inserted, inserted] ++ after).count tested := by
  by_cases equality : tested = inserted
  · subst inserted
    simp [List.count_append]
  · have reverseEquality : inserted ≠ tested :=
      Ne.symm equality
    simp [List.count_append, equality, reverseEquality]

/-- Square every terminating marker while preserving an arbitrary processed
prefix. The multiplicity premise is measured in the whole current list, so
a witness may occur either before or after the selected marker. -/
theorem listDerivesSquareTerminatedMarkersAux
    (final : List Nat) :
    ∀ (factors : List (List Nat × Nat))
      (before : List Nat),
      (∀ factor ∈ factors,
        2 ≤
          (before ++
            renderTerminatedBlocks factors ++ final).count factor.2) →
      ListDerives basis
        (before ++ renderTerminatedBlocks factors ++ final)
        (before ++ renderSquaredTerminatedBlocks factors ++ final)
  | [], before, _ => by
      simpa [renderTerminatedBlocks,
        renderSquaredTerminatedBlocks] using
          (ListDerives.refl (basis := basis) (before ++ final))
  | (block, marker) :: rest, before, multiples => by
      have markerMultiple :
          2 ≤
            ((before ++ block) ++ [marker] ++
              (renderTerminatedBlocks rest ++ final)).count marker := by
        simpa [renderTerminatedBlocks, List.append_assoc] using
          multiples (block, marker) (by simp)
      have firstRaw :=
        listDerivesDuplicateSelectedOccurrence
          marker (before ++ block)
          (renderTerminatedBlocks rest ++ final)
          markerMultiple
      have firstStep :
          ListDerives basis
            (before ++
              renderTerminatedBlocks
                ((block, marker) :: rest) ++ final)
            ((before ++ block ++ [marker, marker]) ++
              renderTerminatedBlocks rest ++ final) := by
        simpa [renderTerminatedBlocks,
          List.append_assoc] using firstRaw
      have restMultiples :
          ∀ factor ∈ rest,
            2 ≤
              ((before ++ block ++ [marker, marker]) ++
                renderTerminatedBlocks rest ++ final).count
                  factor.2 := by
        intro factor member
        have oldMultiple :
            2 ≤
              ((before ++ block) ++ [marker] ++
                (renderTerminatedBlocks rest ++ final)).count
                  factor.2 := by
          simpa [renderTerminatedBlocks,
            List.append_assoc] using
              multiples factor (by simp [member])
        have monotone :=
          count_le_count_duplicateSelected
            factor.2 marker (before ++ block)
              (renderTerminatedBlocks rest ++ final)
        have newMultiple :=
          Nat.le_trans oldMultiple monotone
        simpa [List.append_assoc] using newMultiple
      have restStep :=
        listDerivesSquareTerminatedMarkersAux
          final rest
          (before ++ block ++ [marker, marker])
          restMultiples
      have restStep' :
          ListDerives basis
            ((before ++ block ++ [marker, marker]) ++
              renderTerminatedBlocks rest ++ final)
            ((before ++ block ++ [marker, marker]) ++
              renderSquaredTerminatedBlocks rest ++ final) := by
        simpa [List.append_assoc] using restStep
      have combined := firstStep.trans restStep'
      simpa [renderSquaredTerminatedBlocks,
        List.append_assoc] using combined

/-- Every word derives to the literal terminated decomposition in which each
non-simple occurrence has been doubled. -/
theorem listDerivesSquareAllTerminatedMarkers
    (letters : List Nat) :
    ListDerives basis letters
      (renderSquaredTerminatedBlocks
          (terminatedBlocks letters) ++
        terminatedFinalBlock letters) := by
  have multiples :
      ∀ factor ∈ terminatedBlocks letters,
        2 ≤
          (renderTerminatedBlocks
              (terminatedBlocks letters) ++
            terminatedFinalBlock letters).count factor.2 := by
    intro factor member
    rw [terminatedBlocks_render letters]
    exact
      terminatedBlocks_marker_multiple
        letters factor member
  have squared :=
    listDerivesSquareTerminatedMarkersAux
      (terminatedFinalBlock letters)
      (terminatedBlocks letters) [] <| by
        simpa using multiples
  simpa [terminatedBlocks_render letters] using squared

/-- The terminated scan and the original simple-block scan expose exactly
the same nonempty simple blocks. -/
theorem simpleBlockScan_eq_terminatedBlockScan
    (whole current remaining : List Nat) :
    simpleBlockScan whole current remaining =
      simpleBlocksFromTerminated
        (terminatedBlockScan whole current remaining).1
        (terminatedBlockScan whole current remaining).2 := by
  induction remaining generalizing current with
  | nil =>
      cases current with
      | nil =>
          simp [simpleBlockScan, terminatedBlockScan,
            simpleBlocksFromTerminated, nonemptyTerminatedBlocks]
      | cons head tail =>
          have reverseNe : (head :: tail).reverse ≠ [] := by
            simp
          simp [simpleBlockScan, terminatedBlockScan,
            simpleBlocksFromTerminated, nonemptyTerminatedBlocks,
            reverseNe]
  | cons letter rest ih =>
      by_cases simple : whole.count letter = 1
      · simpa [simpleBlockScan, terminatedBlockScan, simple] using
          ih (letter :: current)
      · cases current with
        | nil =>
            simpa [simpleBlockScan, terminatedBlockScan, simple,
              simpleBlocksFromTerminated,
              nonemptyTerminatedBlocks] using
                ih ([] : List Nat)
        | cons head tail =>
            have reverseNe : (head :: tail).reverse ≠ [] := by
              simp
            have tailBlocks := ih ([] : List Nat)
            simpa [simpleBlockScan, terminatedBlockScan, simple,
              simpleBlocksFromTerminated, nonemptyTerminatedBlocks,
              reverseNe] using
                congrArg
                  (fun blocks => (head :: tail).reverse :: blocks)
                  tailBlocks

/-- The public terminated decomposition recovers `simpleBlocks`. -/
theorem simpleBlocks_eq_simpleBlocksFromTerminated
    (letters : List Nat) :
    simpleBlocks letters =
      simpleBlocksFromTerminated
        (terminatedBlocks letters)
        (terminatedFinalBlock letters) := by
  simpa [simpleBlocks, terminatedBlocks, terminatedFinalBlock] using
    simpleBlockScan_eq_terminatedBlockScan letters [] letters

end SemigroupBasis.CoRoots.S5_107
